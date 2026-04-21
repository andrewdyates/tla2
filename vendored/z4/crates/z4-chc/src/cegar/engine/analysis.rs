// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample analysis: trace extraction, tree building, and feasibility checking.

use super::*;

impl CegarEngine {
    pub(super) fn analyze_counterexample(&mut self, cex_edge_idx: usize) -> CexAnalysis {
        let trace = self.extract_trace(cex_edge_idx);
        self.last_cex_trace = Some(trace.clone());
        if trace.is_empty() {
            return CexAnalysis::AnalysisFailed;
        }
        let trace_tree = self.extract_trace_tree(cex_edge_idx);
        if trace_tree.is_empty() {
            return CexAnalysis::AnalysisFailed;
        }
        if self.config.base.verbose {
            safe_eprintln!(
                "CEGAR: analyzing counterexample trace (linear={}, tree_nodes={})",
                trace.len(),
                trace_tree.len()
            );
        }
        let (_, tree_constraints, tree_links) =
            match self.build_tree_symbolic_constraints(&trace_tree, "_cex") {
                Some(data) => data,
                None => return CexAnalysis::AnalysisFailed,
            };
        let mut all_constraints = tree_constraints;
        for link in &tree_links {
            all_constraints.extend(link.equalities.iter().cloned());
        }
        let cex_formula = ChcExpr::and_all(all_constraints);
        // #7165: Use executor fallback for feasibility checks. The internal
        // DPLL(T) is incomplete on disequality-heavy QF_LIA and mod/div
        // queries, causing CEGAR to loop on Unknown feasibility results.
        let cex_result = self
            .smt
            .check_sat_with_executor_fallback_timeout(&cex_formula, self.config.query_timeout);

        if self.config.base.verbose {
            safe_eprintln!(
                "CEGAR: cex feasibility check: {:?}",
                if cex_result.is_unsat() {
                    "Unsat (spurious)"
                } else if cex_result.is_sat() {
                    "Sat (genuine)"
                } else {
                    "Unknown"
                }
            );
        }

        match cex_result {
            SmtResult::Sat(_) => {
                let trace_info: Vec<_> = trace
                    .iter()
                    .map(|&ei| {
                        let edge = &self.edges[ei];
                        (edge.clause_index, Some(edge.to.clone()))
                    })
                    .collect();

                CexAnalysis::Genuine(trace_info)
            }
            SmtResult::Unknown => CexAnalysis::AnalysisFailed,
            _ => self.refine_from_trace(&trace, &trace_tree),
        }
    }

    /// Validate a counterexample against the original problem constraints.
    ///
    /// Creates a fresh PdrSolver and uses its BMC-style reachability encoding
    /// to check whether the counterexample trace is concretely feasible.
    /// Returns true if valid (genuinely unsafe), false if spurious.
    ///
    /// This catches false genuines where the abstract feasibility check passes
    /// but the concrete trace is infeasible (#3156).
    ///
    /// For multi-predicate problems, the BMC encoding is unavailable
    /// (transition_system_encoding requires exactly one predicate), so we
    /// trust the abstract feasibility check and skip validation.
    pub(super) fn validate_counterexample(&self, trace: &[(usize, Option<AbstractState>)]) -> bool {
        let num_preds = self.problem.predicates().len();
        // Zero-predicate problems (fact => false): no abstraction involved,
        // counterexample is trivially concrete — trust the feasibility check.
        if num_preds == 0 {
            return true;
        }
        // Multi-predicate problems (>1): reject to be sound. The abstract
        // feasibility check can produce false genuines when the CEGAR
        // abstraction loses precision (#6047). Returning false causes the
        // engine to refine or postpone, eventually yielding Unknown — other
        // engines (PDR) can then solve the problem correctly.
        if num_preds > 1 {
            if self.config.base.verbose {
                safe_eprintln!(
                    "CEGAR: multi-predicate validation: rejecting counterexample \
                     (no BMC encoding for {} predicates)",
                    num_preds
                );
            }
            return false;
        }
        // Single-predicate: use BMC validation.

        let steps: Vec<CounterexampleStep> = trace
            .iter()
            .map(|(_, state)| {
                let predicate = state.as_ref().map_or(PredicateId(0), |s| s.relation);
                CounterexampleStep {
                    predicate,
                    assignments: FxHashMap::default(),
                }
            })
            .collect();
        let cex = Counterexample {
            steps,
            witness: None,
        };

        let config = PdrConfig {
            verbose: self.config.base.verbose,
            ..PdrConfig::default()
        };
        let mut verifier = PdrSolver::new(self.problem.clone(), config);
        match verifier.verify_counterexample(&cex) {
            CexVerificationResult::Valid => true,
            CexVerificationResult::Spurious => {
                if self.config.base.verbose {
                    safe_eprintln!("CEGAR: internal validation: counterexample is SPURIOUS");
                }
                false
            }
            CexVerificationResult::Unknown => {
                // Inconclusive — reject to be safe (#1288 soundness policy)
                if self.config.base.verbose {
                    safe_eprintln!(
                        "CEGAR: internal validation: counterexample verification UNKNOWN, rejecting"
                    );
                }
                false
            }
        }
    }

    fn extract_trace(&self, cex_edge_idx: usize) -> Vec<usize> {
        let mut trace = vec![cex_edge_idx];
        let mut visited = FxHashSet::default();
        visited.insert(cex_edge_idx);

        while let Some(&current_idx) = trace.last() {
            let current_edge = &self.edges[current_idx];
            if current_edge.from.is_empty() {
                break;
            }

            let mut found_parent = false;
            for from_state in &current_edge.from {
                for (idx, edge) in self.edges.iter().enumerate() {
                    if !visited.contains(&idx) && edge.to == *from_state {
                        trace.push(idx);
                        visited.insert(idx);
                        found_parent = true;
                        break;
                    }
                }
                if found_parent {
                    break;
                }
            }

            if !found_parent {
                break;
            }
        }

        trace.reverse();
        trace
    }

    fn find_predecessor_edge(
        &self,
        target_state: &AbstractState,
        before_edge_idx: usize,
    ) -> Option<usize> {
        (0..before_edge_idx)
            .rev()
            .find(|&idx| self.edges[idx].to == *target_state)
    }

    fn extract_trace_tree_rec(
        &self,
        edge_idx: usize,
        parent: Option<usize>,
        parent_body_pos: Option<usize>,
        nodes: &mut Vec<TraceTreeNode>,
    ) -> usize {
        let node_idx = nodes.len();
        nodes.push(TraceTreeNode {
            edge_idx,
            parent,
            parent_body_pos,
            children: Vec::new(),
        });

        let edge = &self.edges[edge_idx];
        for (body_pos, from_state) in edge.from.iter().enumerate() {
            if let Some(pred_edge_idx) = self.find_predecessor_edge(from_state, edge_idx) {
                let child_idx = self.extract_trace_tree_rec(
                    pred_edge_idx,
                    Some(node_idx),
                    Some(body_pos),
                    nodes,
                );
                nodes[node_idx].children.push(child_idx);
            }
        }

        node_idx
    }

    pub(super) fn extract_trace_tree(&self, cex_edge_idx: usize) -> Vec<TraceTreeNode> {
        let mut nodes = Vec::new();
        self.extract_trace_tree_rec(cex_edge_idx, None, None, &mut nodes);
        nodes
    }

    pub(super) fn build_tree_symbolic_constraints(
        &self,
        tree: &[TraceTreeNode],
        prefix: &str,
    ) -> Option<TreeSymbolicResult> {
        if tree.is_empty() {
            return None;
        }

        let mut node_substs: Vec<Vec<(ChcVar, ChcExpr)>> = Vec::with_capacity(tree.len());
        let mut node_constraints: Vec<ChcExpr> = Vec::with_capacity(tree.len());

        for (node_idx, node) in tree.iter().enumerate() {
            let edge = &self.edges[node.edge_idx];
            let clause = &self.problem.clauses()[edge.clause_index];
            let subst = rename_clause_vars(clause, prefix, node_idx);
            node_constraints.push(
                clause
                    .body
                    .constraint
                    .as_ref()
                    .map_or(ChcExpr::Bool(true), |c| c.substitute(&subst)),
            );
            node_substs.push(subst);
        }

        let mut links = Vec::new();
        for (child_idx, node) in tree.iter().enumerate() {
            let (Some(parent_idx), Some(parent_body_pos)) = (node.parent, node.parent_body_pos)
            else {
                continue;
            };

            let child_clause =
                &self.problem.clauses()[self.edges[tree[child_idx].edge_idx].clause_index];
            let parent_clause =
                &self.problem.clauses()[self.edges[tree[parent_idx].edge_idx].clause_index];
            let Some((_, parent_body_args)) = parent_clause.body.predicates.get(parent_body_pos)
            else {
                continue;
            };
            let ClauseHead::Predicate(_, ref child_head_args) = child_clause.head else {
                continue;
            };
            if child_head_args.len() != parent_body_args.len() {
                continue;
            }

            let mut eqs = Vec::new();
            for (h_arg, p_arg) in child_head_args.iter().zip(parent_body_args.iter()) {
                let child_renamed = h_arg.substitute(&node_substs[child_idx]);
                let parent_renamed = p_arg.substitute(&node_substs[parent_idx]);
                eqs.push(ChcExpr::eq(child_renamed, parent_renamed));
            }

            links.push(TraceTreeLink {
                child: child_idx,
                parent: parent_idx,
                equalities: eqs,
            });
        }

        Some((node_substs, node_constraints, links))
    }

    pub(super) fn collect_subtree_nodes(
        tree: &[TraceTreeNode],
        root: usize,
        out: &mut FxHashSet<usize>,
    ) {
        if !out.insert(root) {
            return;
        }
        for &child in &tree[root].children {
            Self::collect_subtree_nodes(tree, child, out);
        }
    }
}
