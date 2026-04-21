// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict detection for the DT theory solver.
//!
//! Implements constructor clash, injectivity, tester, disequality, and acyclicity checks.

use super::*;

impl DtSolver<'_> {
    /// Build a conflict clause from all asserted equality literals.
    fn eq_lits_as_conflict(&self) -> Vec<TheoryLit> {
        self.asserted_eq_lits
            .iter()
            .copied()
            .map(|t| TheoryLit::new(t, true))
            .collect()
    }

    /// Check for constructor clash in an equivalence class.
    ///
    /// Returns Some(conflict) if two different constructors are in the same class.
    pub(super) fn check_clash(&self) -> Option<Vec<TheoryLit>> {
        // Group constructor terms by their equivalence class representative
        // Sort by TermId for deterministic clash detection (#3060)
        let mut class_ctors: HashMap<TermId, Vec<(TermId, &ConstructorInfo)>> = HashMap::new();

        let mut sorted_ctors: Vec<_> = self.term_constructors.iter().collect();
        sorted_ctors.sort_by_key(|(term_id, _)| term_id.0);
        for (term_id, info) in sorted_ctors {
            let rep = self.find(*term_id);
            class_ctors.entry(rep).or_default().push((*term_id, info));
        }

        // Check each class for constructor clashes (sorted by rep for determinism)
        let mut sorted_classes: Vec<_> = class_ctors.into_iter().collect();
        sorted_classes.sort_by_key(|(rep, _)| rep.0);
        for (_rep, ctors) in sorted_classes {
            if ctors.len() < 2 {
                continue;
            }

            // Check if all constructors have the same name (same datatype)
            let first_ctor = &ctors[0].1.ctor_name;
            let first_dt = &ctors[0].1.dt_name;

            for (term_id, info) in &ctors[1..] {
                if &info.dt_name == first_dt && &info.ctor_name != first_ctor {
                    // Constructor clash! Different constructors in same class.
                    // Return a conflict clause.
                    // The conflict reason is that these two terms are equal
                    // but have different constructors.
                    //
                    // For MVP, we return a simple conflict. A full implementation
                    // would track the equality chain that led to this.
                    //
                    // For DPLL(T) integration, conflicts must be expressed in terms of
                    // Boolean theory atoms that are present in the SAT layer. We record
                    // all equality literals asserted true and use those as the conflict
                    // explanation. This is conservative but sound.
                    if self.asserted_eq_lits.is_empty() {
                        // Fall back to the old behavior (used by some unit tests that
                        // bypass assert_literal() and thus don't record equality terms).
                        return Some(vec![
                            TheoryLit::new(ctors[0].0, true),
                            TheoryLit::new(*term_id, true),
                        ]);
                    }

                    let mut c = self.eq_lits_as_conflict();
                    c.sort_by_key(|l| (l.term.0, l.value));
                    c.dedup_by_key(|l| (l.term.0, l.value));
                    return Some(c);
                }
            }
        }

        None
    }

    /// Check for injectivity conflicts and generate propagations.
    ///
    /// When C(a1, ..., an) = C(b1, ..., bn), we have a1 = b1, ..., an = bn by injectivity.
    /// If any of these equalities conflicts with an asserted disequality, return a conflict.
    /// Otherwise, queue them for Nelson-Oppen propagation.
    pub(super) fn check_injectivity_conflicts(&mut self) -> Option<Vec<TheoryLit>> {
        // Group same-constructor terms by equivalence class
        // Sort by TermId for deterministic conflict detection (#3060)
        let mut class_ctors: HashMap<TermId, Vec<(TermId, ConstructorInfo)>> = HashMap::new();

        let mut sorted_ctors: Vec<_> = self.term_constructors.iter().collect();
        sorted_ctors.sort_by_key(|(term_id, _)| term_id.0);
        for (term_id, info) in sorted_ctors {
            let rep = self.find(*term_id);
            class_ctors
                .entry(rep)
                .or_default()
                .push((*term_id, info.clone()));
        }

        // For each class with multiple same-constructor terms, check injectivity
        let mut sorted_classes: Vec<_> = class_ctors.into_iter().collect();
        sorted_classes.sort_by_key(|(rep, _)| rep.0);
        for (_rep, ctors) in sorted_classes {
            if ctors.len() < 2 {
                continue;
            }

            // Group by constructor name
            let mut by_ctor: HashMap<String, Vec<(TermId, ConstructorInfo)>> = HashMap::new();
            for (term_id, info) in ctors {
                by_ctor
                    .entry(info.ctor_name.clone())
                    .or_default()
                    .push((term_id, info));
            }

            // For each constructor with multiple terms, check field equalities (sorted by name)
            let mut sorted_by_ctor: Vec<_> = by_ctor.into_iter().collect();
            sorted_by_ctor.sort_by(|(a, _), (b, _)| a.cmp(b));
            for (_ctor_name, same_ctor) in sorted_by_ctor {
                if same_ctor.len() < 2 {
                    continue;
                }

                let arity = same_ctor[0].1.args.len();
                if same_ctor.iter().any(|(_, info)| info.args.len() != arity) {
                    continue;
                }

                // For each field position, all arguments must be equal across the class.
                for field_idx in 0..arity {
                    let mut args: Vec<TermId> = Vec::with_capacity(same_ctor.len());
                    let mut arg_set: HashSet<TermId> = Default::default();

                    for (_term_id, info) in &same_ctor {
                        let arg = info.args[field_idx];
                        if arg_set.insert(arg) {
                            args.push(arg);
                        }
                    }

                    if args.len() <= 1 {
                        continue;
                    }

                    // Disequality between required-equal args → conflict.
                    for &(diseq_lhs, diseq_rhs, diseq_lit) in &self.asserted_diseqs {
                        if arg_set.contains(&diseq_lhs) && arg_set.contains(&diseq_rhs) {
                            let mut c = self.eq_lits_as_conflict();
                            c.push(TheoryLit::new(diseq_lit, false));
                            c.sort_by_key(|l| (l.term.0, l.value));
                            c.dedup_by_key(|l| (l.term.0, l.value));
                            return Some(c);
                        }
                    }

                    // Merge in union-find (#5082) and queue for N-O propagation.
                    let rep = args[0];
                    for &other in &args[1..] {
                        self.union(rep, other);
                        let pair = if rep.0 < other.0 {
                            (rep, other)
                        } else {
                            (other, rep)
                        };
                        if !self.propagated_eq_pairs.contains(&pair) {
                            self.propagated_eq_pairs.insert(pair);
                            let reason = self.eq_lits_as_conflict();
                            self.pending_injectivity_eqs
                                .push(DiscoveredEquality::new(pair.0, pair.1, reason));
                        }
                    }
                }
            }
        }

        None
    }

    /// Check for conflicts between tester results and constructors (#5082).
    ///
    /// Two cases:
    /// 1. `is-C(t) = false` but a term `C(...)` is in the same equivalence class as `t`.
    /// 2. `is-C(t) = true` but a term `C'(...)` (different constructor) is in t's class.
    pub(super) fn check_tester_conflicts(&self) -> Option<Vec<TheoryLit>> {
        for (&tester_arg, (tester_ctor, tester_val, tester_lit)) in &self.tester_results {
            let tester_rep = self.find(tester_arg);

            // Check all constructors for a match in the same equivalence class
            for (ctor_term, ctor_info) in &self.term_constructors {
                let ctor_rep = self.find(*ctor_term);
                if ctor_rep != tester_rep {
                    continue;
                }

                // Same equivalence class. Check for contradiction.
                let same_ctor = &ctor_info.ctor_name == tester_ctor;
                if (*tester_val && !same_ctor) || (!*tester_val && same_ctor) {
                    let mut c = self.eq_lits_as_conflict();
                    c.push(TheoryLit::new(*tester_lit, *tester_val));
                    c.sort_by_key(|l| (l.term.0, l.value));
                    c.dedup_by_key(|l| (l.term.0, l.value));
                    return Some(c);
                }
            }
        }

        None
    }

    /// Check for conflicts between implied equalities and asserted disequalities.
    ///
    /// If `a` and `b` are in the same union-find class (via asserted equalities),
    /// then an asserted disequality `(not (= a b))` is inconsistent.
    pub(super) fn check_disequality_conflicts(&self) -> Option<Vec<TheoryLit>> {
        for idx in 0..self.asserted_diseqs.len() {
            let (lhs, rhs, diseq_lit) = self.asserted_diseqs[idx];
            if self.find(lhs) == self.find(rhs) {
                let mut c = self.eq_lits_as_conflict();
                c.push(TheoryLit::new(diseq_lit, false));
                c.sort_by_key(|l| (l.term.0, l.value));
                c.dedup_by_key(|l| (l.term.0, l.value));
                return Some(c);
            }
        }

        None
    }

    fn occurs_check_conflict(&self) -> Vec<TheoryLit> {
        let mut conflict = self.eq_lits_as_conflict();
        conflict.sort_by_key(|l| (l.term.0, l.value));
        conflict.dedup_by_key(|l| (l.term.0, l.value));
        conflict
    }

    pub(super) fn occurs_check(&self) -> Option<Vec<TheoryLit>> {
        // Build a map from equivalence-class representative to constructor arguments.
        //
        // Cycles can only occur through constructor terms; nodes that don't contain
        // any constructor application cannot participate in a cycle.
        // Sort for deterministic cycle detection (#3060)
        let mut ctor_terms: Vec<TermId> = self.term_constructors.keys().copied().collect();
        ctor_terms.sort_unstable_by_key(|t| t.0);
        let mut rep_to_args: HashMap<TermId, Vec<TermId>> = HashMap::new();
        for term_id in ctor_terms {
            let rep = self.find(term_id);
            let Some(info) = self.term_constructors.get(&term_id) else {
                continue;
            };
            // A single equivalence class can contain multiple constructor terms (e.g., from
            // selector/tester axioms). Accumulate edges from *all* constructor terms to avoid
            // missing cycles due to hash iteration order.
            rep_to_args
                .entry(rep)
                .or_default()
                .extend(info.args.iter().copied());
        }

        // 0/unset = unvisited, 1 = on stack, 2 = fully explored (cycle-free).
        let mut color: HashMap<TermId, u8> = HashMap::new();

        #[derive(Clone, Copy)]
        enum Op {
            Enter,
            Exit,
        }

        let mut reps: Vec<TermId> = rep_to_args.keys().copied().collect();
        reps.sort_unstable_by_key(|t| t.0); // Deterministic DFS start order (#3060)
        for start in reps {
            let start = self.find(start);
            if matches!(color.get(&start), Some(2)) {
                continue;
            }

            let mut stack: Vec<(Op, TermId)> = vec![(Op::Enter, start)];
            while let Some((op, node)) = stack.pop() {
                let node = self.find(node);
                match op {
                    Op::Exit => {
                        color.insert(node, 2);
                    }
                    Op::Enter => {
                        match color.get(&node).copied() {
                            Some(2) => continue,
                            Some(1) => return Some(self.occurs_check_conflict()),
                            _ => {}
                        }

                        color.insert(node, 1);
                        stack.push((Op::Exit, node));

                        let Some(args) = rep_to_args.get(&node) else {
                            continue;
                        };
                        for &arg in args {
                            let arg_rep = self.find(arg);
                            if !rep_to_args.contains_key(&arg_rep) {
                                continue;
                            }
                            match color.get(&arg_rep).copied() {
                                Some(2) => continue,
                                Some(1) => return Some(self.occurs_check_conflict()),
                                _ => stack.push((Op::Enter, arg_rep)),
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Check DT invariants (debug builds only).
    ///
    /// Extracted from check() to stay within the function-size limit.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_invariants(&self) {
        // Union-find representatives are fixpoints (sampled).
        debug_assert!(
            self.parent.keys().take(64).all(|&t| {
                let r = self.find(t);
                self.find(r) == r
            }),
            "BUG: DT union-find representative is not a fixpoint"
        );
        // asserted_eq_lits hasn't shrunk below the most recent scope snapshot.
        debug_assert!(
            self.scopes
                .last()
                .is_none_or(|s| self.asserted_eq_lits.len() >= s.asserted_eq_lits_len),
            "BUG: DT asserted_eq_lits ({}) < scope snapshot ({})",
            self.asserted_eq_lits.len(),
            self.scopes.last().map_or(0, |s| s.asserted_eq_lits_len),
        );
        // asserted_diseqs hasn't shrunk below the most recent scope snapshot.
        debug_assert!(
            self.scopes
                .last()
                .is_none_or(|s| self.asserted_diseqs.len() >= s.asserted_diseqs_len),
            "BUG: DT asserted_diseqs ({}) < scope snapshot ({})",
            self.asserted_diseqs.len(),
            self.scopes.last().map_or(0, |s| s.asserted_diseqs_len),
        );
    }
}
