// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Problem classification for adaptive portfolio strategy selection.
//!
//! This module extracts features from CHC problems to classify them
//! and select the best solving strategy. The goal is to predict which
//! engine will work best, budget time accordingly, and return gracefully
//! before external timeouts.
//!
//! # Problem Classes
//!
//! - **Trivial**: <5 clauses, 1 predicate, no cycles -> direct PDR, <0.5s expected
//! - **SimpleLoop**: Single predicate, linear, single transition -> TPA primary
//! - **ComplexLoop**: Single predicate, complex structure -> PDR primary
//! - **MultiPredLinear**: Multiple predicates, linear -> PDR with decomposition
//! - **MultiPredComplex**: Hyperedge structure -> PDR with splits
//!
//! # Reference
//!
//! Part of #1868 - Adaptive portfolio for 30s bounded execution.
//! See `designs/2026-02-01-adaptive-portfolio-30s.md` for full design.

use crate::{pdr::scc::tarjan_scc, ChcExpr, ChcOp, ChcProblem, ChcSort};

/// Extracted features from a CHC problem.
#[derive(Debug, Clone)]
pub(crate) struct ProblemFeatures {
    /// Number of predicates declared
    pub(crate) num_predicates: usize,
    /// Number of clauses
    pub(crate) num_clauses: usize,
    /// Each clause has at most one body predicate
    pub(crate) is_linear: bool,
    /// Only one predicate exists (classic transition system)
    pub(crate) is_single_predicate: bool,
    /// Predicate dependency graph has cycles (SCC analysis)
    pub(crate) has_cycles: bool,
    /// Number of SCCs in the predicate dependency graph
    pub(crate) scc_count: usize,
    /// Size of the largest SCC in the predicate dependency graph
    pub(crate) max_scc_size: usize,
    /// Longest path length in the SCC condensation DAG
    pub(crate) dag_depth: usize,
    /// Any Array sort in predicate signatures
    pub(crate) uses_arrays: bool,
    /// Any Real sort in predicate signatures
    pub(crate) uses_real: bool,
    /// Number of transition clauses (neither facts nor queries)
    pub(crate) num_transitions: usize,
    /// Number of fact clauses (no body predicates, predicate head)
    pub(crate) num_facts: usize,
    /// Number of query clauses (False head)
    pub(crate) num_queries: usize,
    /// Maximum number of distinct variables in a single clause
    pub(crate) max_clause_variables: usize,
    /// Mean number of distinct variables per clause
    pub(crate) mean_clause_variables: f64,
    /// Any arithmetic multiplication term in clause constraints
    pub(crate) has_multiplication: bool,
    /// Any arithmetic mod/div term in clause constraints
    pub(crate) has_mod_div: bool,
    /// Any if-then-else term in clause constraints
    pub(crate) has_ite: bool,
    /// Fraction of transition clauses that are self-loops
    pub(crate) self_loop_ratio: f64,
    /// Maximum predicate arity across all declared predicates
    pub(crate) max_predicate_arity: usize,
    /// All clauses are entry->exit only (queries with no body predicates).
    /// Reference: Golem's `isTrivial()` in TransformationUtils.cc:284-290
    pub(crate) is_entry_exit_only: bool,
    /// Phase-bounded depth: if `Some(depth)`, the problem has a phase counter
    /// argument that monotonically increases across all transitions, making it
    /// safe to solve with BMC at depth `depth` with `acyclic_safe=true`.
    /// Common in zani-generated CHC for phased Rust program execution (#7897).
    pub(crate) phase_bounded_depth: Option<usize>,
    /// Any Datatype sort in predicate signatures.
    ///
    /// When true, the problem uses algebraic datatypes (e.g., `Option<u8>`,
    /// newtype structs). DT problems need SMT-level constructor/selector
    /// reasoning; LIA generalization escalation and k-induction via SingleLoop
    /// are unproductive. Used to skip Kind and cap PDR escalation (#7930).
    pub(crate) uses_datatypes: bool,
    /// Classified problem class
    pub(crate) class: ProblemClass,
}

/// Classification of CHC problem structure for strategy selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProblemClass {
    /// No predicates needed - all clauses are entry->exit only.
    /// This means all queries are facts (no predicate in body).
    /// Solved with single SMT satisfiability check.
    /// Reference: Golem's `isTrivial()` in TransformationUtils.cc:284-290
    EntryExitOnly,
    /// <5 clauses, 1 predicate, no cycles
    /// Expected: <0.5s with any engine
    Trivial,
    /// Single predicate, linear, single transition
    /// Best: TPA (transition power abstraction)
    SimpleLoop,
    /// Single predicate, multiple transitions or non-linear constraints
    /// Best: PDR with generalization
    ComplexLoop,
    /// Multiple predicates, linear (graph structure)
    /// Best: PDR with potential decomposition
    MultiPredLinear,
    /// Multiple predicates, hyperedges (multi-body clauses)
    /// Best: PDR with negated equality splits
    MultiPredComplex,
}

impl std::fmt::Display for ProblemClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EntryExitOnly => write!(f, "EntryExitOnly"),
            Self::Trivial => write!(f, "Trivial"),
            Self::SimpleLoop => write!(f, "SimpleLoop"),
            Self::ComplexLoop => write!(f, "ComplexLoop"),
            Self::MultiPredLinear => write!(f, "MultiPredLinear"),
            Self::MultiPredComplex => write!(f, "MultiPredComplex"),
        }
    }
}

/// Problem classifier for CHC solving strategy selection.
pub(crate) struct ProblemClassifier;

#[derive(Debug, Clone, Copy, Default)]
struct ConstraintFeatures {
    has_multiplication: bool,
    has_mod_div: bool,
    has_ite: bool,
}

impl ConstraintFeatures {
    fn all_set(self) -> bool {
        self.has_multiplication && self.has_mod_div && self.has_ite
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct ClauseFeatures {
    num_transitions: usize,
    num_facts: usize,
    num_queries: usize,
    max_clause_variables: usize,
    mean_clause_variables: f64,
    has_multiplication: bool,
    has_mod_div: bool,
    has_ite: bool,
    self_loop_ratio: f64,
}

#[derive(Debug, Clone, Copy, Default)]
struct DependencyGraphFeatures {
    has_cycles: bool,
    scc_count: usize,
    max_scc_size: usize,
    dag_depth: usize,
}

impl ProblemClassifier {
    /// Classify a CHC problem and extract features.
    ///
    /// This runs in O(|clauses| + |predicates|) time and should complete
    /// in <100ms even for large problems.
    pub(crate) fn classify(problem: &ChcProblem) -> ProblemFeatures {
        let num_predicates = problem.predicates().len();
        let num_clauses = problem.clauses().len();

        // Check linearity: each clause has at most one body predicate
        let is_linear = problem
            .clauses()
            .iter()
            .all(|c| c.body.predicates.len() <= 1);

        let is_single_predicate = num_predicates == 1;

        // Summarize the predicate dependency graph.
        let dependency_graph = Self::analyze_dependency_graph(problem);

        // Check for array/real sorts
        let (uses_arrays, uses_real) = Self::check_sorts(problem);

        // Count clause types and scan clause/constraint-level features.
        let clause_features = Self::analyze_clauses(problem);

        let max_predicate_arity = problem
            .predicates()
            .iter()
            .map(|pred| pred.arity())
            .max()
            .unwrap_or(0);

        // Check for entry-exit-only pattern (Golem's isTrivial)
        let is_entry_exit_only = Self::is_entry_exit_only(problem);

        // Detect phase-bounded problems (#7897)
        let phase_bounded_depth = problem.detect_phase_bounded_depth();

        // Determine class
        let class = Self::determine_class(
            num_predicates,
            num_clauses,
            clause_features.num_transitions,
            is_linear,
            is_single_predicate,
            dependency_graph.has_cycles,
            is_entry_exit_only,
        );

        // Check for datatype sorts in predicate signatures (#7930).
        let uses_datatypes = problem.has_datatype_sorts();

        ProblemFeatures {
            num_predicates,
            num_clauses,
            is_linear,
            is_single_predicate,
            has_cycles: dependency_graph.has_cycles,
            scc_count: dependency_graph.scc_count,
            max_scc_size: dependency_graph.max_scc_size,
            dag_depth: dependency_graph.dag_depth,
            uses_arrays,
            uses_real,
            num_transitions: clause_features.num_transitions,
            num_facts: clause_features.num_facts,
            num_queries: clause_features.num_queries,
            max_clause_variables: clause_features.max_clause_variables,
            mean_clause_variables: clause_features.mean_clause_variables,
            has_multiplication: clause_features.has_multiplication,
            has_mod_div: clause_features.has_mod_div,
            has_ite: clause_features.has_ite,
            self_loop_ratio: clause_features.self_loop_ratio,
            max_predicate_arity,
            is_entry_exit_only,
            phase_bounded_depth,
            uses_datatypes,
            class,
        }
    }

    /// Compute SCC-based dependency graph features.
    fn analyze_dependency_graph(problem: &ChcProblem) -> DependencyGraphFeatures {
        let scc_info = tarjan_scc(problem);
        let scc_count = scc_info.sccs.len();

        if scc_count == 0 {
            return DependencyGraphFeatures::default();
        }

        let has_cycles = scc_info.sccs.iter().any(|scc| scc.is_cyclic);
        let max_scc_size = scc_info
            .sccs
            .iter()
            .map(|scc| scc.predicates.len())
            .max()
            .unwrap_or(0);

        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); scc_count];
        let mut in_degree = vec![0usize; scc_count];

        for (from_pred, to_pred) in problem.dependency_edges() {
            let Some(&from_scc) = scc_info.predicate_to_scc.get(&from_pred) else {
                continue;
            };
            let Some(&to_scc) = scc_info.predicate_to_scc.get(&to_pred) else {
                continue;
            };

            if from_scc != to_scc && !adj[from_scc].contains(&to_scc) {
                adj[from_scc].push(to_scc);
                in_degree[to_scc] += 1;
            }
        }

        let mut queue: Vec<_> = (0..scc_count).filter(|i| in_degree[*i] == 0).collect();
        let mut depth = vec![1usize; scc_count];
        let mut dag_depth = 1usize;

        while let Some(scc_idx) = queue.pop() {
            dag_depth = dag_depth.max(depth[scc_idx]);
            for &next in &adj[scc_idx] {
                depth[next] = depth[next].max(depth[scc_idx] + 1);
                in_degree[next] -= 1;
                if in_degree[next] == 0 {
                    queue.push(next);
                }
            }
        }

        DependencyGraphFeatures {
            has_cycles,
            scc_count,
            max_scc_size,
            dag_depth,
        }
    }

    /// Compute clause-level counts and constraint-derived features.
    fn analyze_clauses(problem: &ChcProblem) -> ClauseFeatures {
        let mut num_transitions = 0usize;
        let mut num_facts = 0usize;
        let mut num_queries = 0usize;
        let mut max_clause_variables = 0usize;
        let mut total_clause_variables = 0usize;
        let mut has_multiplication = false;
        let mut has_mod_div = false;
        let mut has_ite = false;
        let mut self_loops = 0usize;

        for clause in problem.clauses() {
            let clause_variables = clause.vars().len();
            max_clause_variables = max_clause_variables.max(clause_variables);
            total_clause_variables += clause_variables;

            if let Some(constraint) = &clause.body.constraint {
                let constraint_features = Self::scan_constraint_features(constraint);
                has_multiplication |= constraint_features.has_multiplication;
                has_mod_div |= constraint_features.has_mod_div;
                has_ite |= constraint_features.has_ite;
            }

            if clause.is_query() {
                num_queries += 1;
            } else if clause.body.predicates.is_empty() {
                num_facts += 1;
            } else {
                num_transitions += 1;
                if let Some(head_pred) = clause.head.predicate_id() {
                    if clause
                        .body
                        .predicates
                        .iter()
                        .any(|(body_pred, _)| *body_pred == head_pred)
                    {
                        self_loops += 1;
                    }
                }
            }
        }

        let num_clauses = problem.clauses().len();
        let mean_clause_variables = if num_clauses == 0 {
            0.0
        } else {
            total_clause_variables as f64 / num_clauses as f64
        };
        let self_loop_ratio = if num_transitions == 0 {
            0.0
        } else {
            self_loops as f64 / num_transitions as f64
        };

        ClauseFeatures {
            num_transitions,
            num_facts,
            num_queries,
            max_clause_variables,
            mean_clause_variables,
            has_multiplication,
            has_mod_div,
            has_ite,
            self_loop_ratio,
        }
    }

    /// Scan a clause constraint for arithmetic and control-flow operators.
    fn scan_constraint_features(expr: &ChcExpr) -> ConstraintFeatures {
        let mut features = ConstraintFeatures::default();
        let mut stack = vec![expr];

        while let Some(current) = stack.pop() {
            match current {
                ChcExpr::Op(op, args) => {
                    match op {
                        ChcOp::Mul => features.has_multiplication = true,
                        ChcOp::Div | ChcOp::Mod => features.has_mod_div = true,
                        ChcOp::Ite => features.has_ite = true,
                        _ => {}
                    }
                    if features.all_set() {
                        break;
                    }
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::ConstArray(_, value) => stack.push(value.as_ref()),
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
        }

        features
    }

    /// Check for array and real sorts in predicate signatures.
    fn check_sorts(problem: &ChcProblem) -> (bool, bool) {
        let mut uses_arrays = false;
        let mut uses_real = false;

        for pred in problem.predicates() {
            for sort in &pred.arg_sorts {
                Self::check_sort_recursive(sort, &mut uses_arrays, &mut uses_real);
            }
        }

        (uses_arrays, uses_real)
    }

    fn check_sort_recursive(sort: &ChcSort, uses_arrays: &mut bool, uses_real: &mut bool) {
        match sort {
            ChcSort::Array(k, v) => {
                *uses_arrays = true;
                Self::check_sort_recursive(k, uses_arrays, uses_real);
                Self::check_sort_recursive(v, uses_arrays, uses_real);
            }
            ChcSort::Real => {
                *uses_real = true;
            }
            ChcSort::Int
            | ChcSort::Bool
            | ChcSort::BitVec(_)
            | ChcSort::Uninterpreted(_)
            | ChcSort::Datatype { .. } => {}
        }
    }

    /// Check if problem has only entry->exit edges (Golem's isTrivial pattern).
    ///
    /// A problem is entry-exit-only if ALL clauses are queries (false head)
    /// with no body predicates. This means there are no intermediate predicates
    /// and the problem reduces to satisfiability checking.
    ///
    /// Reference: Golem's `isTrivial()` in TransformationUtils.cc:284-290
    fn is_entry_exit_only(problem: &ChcProblem) -> bool {
        // Must have at least one clause
        if problem.clauses().is_empty() {
            return false;
        }

        // All clauses must be queries (false head) with no body predicates
        problem.clauses().iter().all(|c| {
            // Must be a query (false head)
            c.is_query() &&
            // Must have no body predicates (only constraints)
            c.body.predicates.is_empty()
        })
    }

    /// Determine problem class based on extracted features.
    fn determine_class(
        _num_predicates: usize,
        num_clauses: usize,
        num_transitions: usize,
        is_linear: bool,
        is_single_predicate: bool,
        has_cycles: bool,
        is_entry_exit_only: bool,
    ) -> ProblemClass {
        // EntryExitOnly: simplest case - just SAT checking
        // Reference: Golem's isTrivial()
        if is_entry_exit_only {
            return ProblemClass::EntryExitOnly;
        }

        // Trivial: very small problems with predicates
        if num_clauses < 5 && is_single_predicate && !has_cycles {
            return ProblemClass::Trivial;
        }

        // Single predicate cases
        if is_single_predicate {
            // SimpleLoop: single transition, no branching
            if num_transitions == 1 && is_linear {
                return ProblemClass::SimpleLoop;
            }
            // ComplexLoop: multiple transitions or complex structure
            return ProblemClass::ComplexLoop;
        }

        // Multi-predicate cases
        if is_linear {
            ProblemClass::MultiPredLinear
        } else {
            ProblemClass::MultiPredComplex
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
