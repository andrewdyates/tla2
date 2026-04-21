// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl ChcProblem {
    /// Detect a phase-bounded execution depth for acyclic-safe BMC (#7897).
    ///
    /// Zani-generated CHC problems encode phased Rust program execution as
    /// single-predicate problems where one integer argument monotonically
    /// increases across transitions (e.g., phase 0 -> 1 -> 2 -> 3 -> 4).
    /// PDR struggles with the disjunctive invariants needed for such problems,
    /// but BMC with `acyclic_safe=true` can prove safety by exhausting all
    /// reachable states up to the maximum phase depth.
    ///
    /// Returns `Some(depth)` if a phase-bounded argument is found, where
    /// `depth` is the maximum phase value (+1 for BMC depth). Returns `None`
    /// if the problem is not phase-bounded.
    pub fn detect_phase_bounded_depth(&self) -> Option<usize> {
        // Only applicable to single-predicate problems
        if self.predicates.len() != 1 {
            return None;
        }

        let pred_id = PredicateId::new(0);
        let pred = self.get_predicate(pred_id)?;
        let arity = pred.arity();
        if arity == 0 {
            return None;
        }

        let transitions: Vec<_> = self.transitions().collect();
        // Need at least 2 transitions for a phased pattern
        if transitions.len() < 2 {
            return None;
        }

        let facts: Vec<_> = self.facts().collect();
        if facts.is_empty() {
            return None;
        }

        // Try each integer argument position as a candidate phase variable
        for arg_idx in 0..arity {
            if !matches!(pred.arg_sorts.get(arg_idx), Some(ChcSort::Int)) {
                continue;
            }
            if let Some(depth) =
                self.check_phase_bounded_arg(pred_id, arg_idx, &facts, &transitions)
            {
                return Some(depth);
            }
        }
        None
    }

    /// Check if argument at position `arg_idx` is a phase-bounded counter.
    ///
    /// Returns `Some(max_phase + 1)` if all transitions guard on a constant
    /// value for this argument and set it to a strictly larger constant in
    /// the head, forming a connected acyclic chain from the initial value.
    fn check_phase_bounded_arg(
        &self,
        pred_id: PredicateId,
        arg_idx: usize,
        facts: &[&HornClause],
        transitions: &[&HornClause],
    ) -> Option<usize> {
        // Step 1: Extract initial phase value(s) from fact clauses.
        // A fact clause has no body predicates and a predicate head.
        let mut init_values: Vec<i64> = Vec::new();
        for fact in facts {
            if let ClauseHead::Predicate(hid, head_args) = &fact.head {
                if *hid != pred_id {
                    continue;
                }
                // The head argument at `arg_idx` might be a constant or a variable.
                // If it's a variable, look in the constraint for (= var constant).
                if let Some(val) =
                    Self::extract_arg_constant(&head_args[arg_idx], fact.body.constraint.as_ref())
                {
                    init_values.push(val);
                } else {
                    // Can't determine the initial value - not phase-bounded
                    return None;
                }
            }
        }

        if init_values.is_empty() {
            return None;
        }

        // Step 2: For each transition, extract (from_phase, to_phase) pair.
        // A transition has one body predicate and a predicate head (same pred).
        let mut edges: Vec<(i64, i64)> = Vec::new();
        for trans in transitions {
            if trans.body.predicates.len() != 1 {
                return None; // Non-linear transition
            }
            let (body_pred_id, body_args) = &trans.body.predicates[0];
            if *body_pred_id != pred_id {
                return None;
            }

            let (head_pred_id, head_args) = match &trans.head {
                ClauseHead::Predicate(hid, args) => (*hid, args),
                ClauseHead::False => return None, // Query, not transition
            };
            if head_pred_id != pred_id {
                return None;
            }

            // Extract from_phase: the body predicate's arg at arg_idx
            // should be constrained to a constant in the clause constraint.
            let from_val =
                Self::extract_arg_constant(&body_args[arg_idx], trans.body.constraint.as_ref())?;

            // Extract to_phase: the head predicate's arg at arg_idx
            // should be constrained to a constant in the clause constraint.
            let to_val =
                Self::extract_arg_constant(&head_args[arg_idx], trans.body.constraint.as_ref())?;

            // Phase must strictly increase
            if to_val <= from_val {
                return None;
            }

            edges.push((from_val, to_val));
        }

        if edges.is_empty() {
            return None;
        }

        // Step 3: Verify chain connectivity and compute max depth.
        // All init_values must appear as `from` in some edge, and the chain
        // must be acyclic (guaranteed by strict increase).
        let max_phase = edges.iter().map(|(_, to)| *to).max()?;

        // Sanity: all initial values should be <= max_phase
        // and the chain should cover init -> ... -> max_phase.
        // We verify by building a reachability set from init values.
        let mut reachable: FxHashSet<i64> = FxHashSet::default();
        for v in &init_values {
            reachable.insert(*v);
        }

        // BFS / forward propagation through edges
        let mut changed = true;
        while changed {
            changed = false;
            for (from, to) in &edges {
                if reachable.contains(from) && reachable.insert(*to) {
                    changed = true;
                }
            }
        }

        // All edge sources must be reachable from initial values
        for (from, _) in &edges {
            if !reachable.contains(from) {
                return None;
            }
        }

        // Return depth = max_phase + 1 (BMC needs to explore up to and including max_phase)
        Some(max_phase as usize + 1)
    }

    /// Extract an integer constant value for a predicate argument expression.
    ///
    /// The argument might be:
    /// 1. A direct integer constant: `Int(k)` -> returns `Some(k)`
    /// 2. A variable that is constrained in the clause: `Var(v)` where
    ///    the constraint contains `(= v k)` -> returns `Some(k)`
    fn extract_arg_constant(arg: &ChcExpr, constraint: Option<&ChcExpr>) -> Option<i64> {
        // Case 1: Direct constant
        if let ChcExpr::Int(k) = arg {
            return Some(*k);
        }

        // Case 2: Variable with equality constraint
        if let ChcExpr::Var(var) = arg {
            if let Some(constraint) = constraint {
                return Self::find_var_constant_in_constraint(&var.name, constraint);
            }
        }

        None
    }

    /// Search a constraint expression for `(= var_name constant)`.
    ///
    /// Handles top-level conjunctions: `(and (= v 0) (= w 1) ...)`.
    fn find_var_constant_in_constraint(var_name: &str, constraint: &ChcExpr) -> Option<i64> {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(val) = Self::find_var_constant_in_constraint(var_name, arg) {
                        return Some(val);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // (= var constant) or (= constant var)
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(k)) if v.name == var_name => Some(*k),
                    (ChcExpr::Int(k), ChcExpr::Var(v)) if v.name == var_name => Some(*k),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Get query clauses (clauses with false head)
    pub fn queries(&self) -> impl Iterator<Item = &HornClause> {
        self.clauses.iter().filter(|c| c.is_query())
    }

    /// Get fact clauses (clauses with no predicates in body)
    pub fn facts(&self) -> impl Iterator<Item = &HornClause> {
        self.clauses.iter().filter(|c| c.is_fact() && !c.is_query())
    }

    /// Get transition clauses (clauses with predicates in both body and head)
    pub fn transitions(&self) -> impl Iterator<Item = &HornClause> {
        self.clauses
            .iter()
            .filter(|c| !c.is_fact() && !c.is_query())
    }

    /// Get clauses that define a predicate (have it in head)
    pub fn clauses_defining(&self, pred: PredicateId) -> impl Iterator<Item = &HornClause> {
        self.clauses
            .iter()
            .filter(move |c| c.head.predicate_id() == Some(pred))
    }

    /// Get clauses that define a predicate with their indices
    pub fn clauses_defining_with_index(
        &self,
        pred: PredicateId,
    ) -> impl Iterator<Item = (usize, &HornClause)> {
        self.clauses
            .iter()
            .enumerate()
            .filter(move |(_, c)| c.head.predicate_id() == Some(pred))
    }

    /// Get clauses that use a predicate (have it in body)
    pub fn clauses_using(&self, pred: PredicateId) -> impl Iterator<Item = &HornClause> {
        self.clauses
            .iter()
            .filter(move |c| c.body.predicates.iter().any(|(id, _)| *id == pred))
    }

    /// Validate the problem
    pub fn validate(&self) -> ChcResult<()> {
        use crate::ChcError;

        // Check that all predicates used in clauses are declared
        for clause in &self.clauses {
            for (pred_id, args) in &clause.body.predicates {
                let pred = self
                    .get_predicate(*pred_id)
                    .ok_or_else(|| ChcError::UndefinedPredicate(format!("P{}", pred_id.0)))?;
                if args.len() != pred.arity() {
                    return Err(ChcError::ArityMismatch {
                        name: pred.name.clone(),
                        expected: pred.arity(),
                        actual: args.len(),
                    });
                }
            }
            if let ClauseHead::Predicate(pred_id, args) = &clause.head {
                let pred = self
                    .get_predicate(*pred_id)
                    .ok_or_else(|| ChcError::UndefinedPredicate(format!("P{}", pred_id.0)))?;
                if args.len() != pred.arity() {
                    return Err(ChcError::ArityMismatch {
                        name: pred.name.clone(),
                        expected: pred.arity(),
                        actual: args.len(),
                    });
                }
            }
        }

        // Check that there's at least one query
        if self.queries().count() == 0 {
            return Err(ChcError::NoQuery);
        }

        Ok(())
    }

    /// Build a dependency graph of predicates
    ///
    /// Returns edges: (from, to) where `from` appears in body and `to` in head
    pub fn dependency_edges(&self) -> Vec<(PredicateId, PredicateId)> {
        let mut edges = Vec::new();
        for clause in &self.clauses {
            if let Some(head_id) = clause.head.predicate_id() {
                for (body_id, _) in &clause.body.predicates {
                    edges.push((*body_id, head_id));
                }
            }
        }
        edges
    }

    /// Topologically sort predicates (returns None if cyclic)
    pub fn topological_order(&self) -> Option<Vec<PredicateId>> {
        let n = self.predicates.len();
        let mut in_degree = vec![0usize; n];
        let mut adj: Vec<Vec<PredicateId>> = vec![Vec::new(); n];

        for (from, to) in self.dependency_edges() {
            adj[from.index()].push(to);
            in_degree[to.index()] += 1;
        }

        let mut queue: Vec<_> = (0..n)
            .filter(|i| in_degree[*i] == 0)
            .map(|i| PredicateId::new(i as u32))
            .collect();
        let mut result = Vec::new();

        while let Some(node) = queue.pop() {
            result.push(node);
            for &next in &adj[node.index()] {
                in_degree[next.index()] -= 1;
                if in_degree[next.index()] == 0 {
                    queue.push(next);
                }
            }
        }

        if result.len() == n {
            Some(result)
        } else {
            None // Cycle detected
        }
    }
}
