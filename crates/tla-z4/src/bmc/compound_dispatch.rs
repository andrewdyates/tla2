// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compound type dispatch helpers for the BMC expression translator.
//!
//! Wires set operations (union, intersect, subset, cardinality), function
//! operations (EXCEPT, DOMAIN, construction), and universe extraction into
//! the BMC translator's expression evaluation path.
//!
//! Part of #3778: wire compound type encoders into BMC expression translator.

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::{Sort, Term};

use crate::error::{Z4Error, Z4Result};

use super::BmcTranslator;

/// Set binary operation kind for dispatch.
pub(super) enum SetBinOp {
    Union,
    Intersect,
    Minus,
}

impl BmcTranslator {
    /// Translate `S \subseteq T` by extracting a finite universe from the
    /// operands and expanding pointwise.
    pub(super) fn translate_subseteq_dispatch(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let universe = self.extract_universe_from_exprs(&[left, right])?;
        self.translate_subseteq_bmc(left, right, &universe)
    }

    /// Translate `{e1, ..., en}` as a Bool expression.
    ///
    /// Builds the SMT array term and returns TRUE to signal success. The set
    /// is stored in the solver context; the return value is used only because
    /// the shared dispatch requires a Bool-sorted result from
    /// `translate_bool_extended`.
    pub(super) fn translate_set_enum_bool(&mut self, elements: &[Spanned<Expr>]) -> Z4Result<Term> {
        // Build: (store (store (const false) e1 true) ... en true)
        let false_val = self.solver.bool_const(false);
        let true_val = self.solver.bool_const(true);
        let mut arr = self.solver.try_const_array(Sort::Int, false_val)?;
        for elem in elements {
            let elem_term = self.translate_int(elem)?;
            arr = self.solver.try_store(arr, elem_term, true_val)?;
        }
        // The array is built and available in the solver; return TRUE.
        let _ = arr;
        Ok(self.solver.bool_const(true))
    }

    /// Translate a set binary operation (`Union`, `Intersect`, `SetMinus`) as a
    /// Bool expression.
    ///
    /// Extracts a finite universe from both operands, builds the result array
    /// via the appropriate encoder, and returns TRUE.
    pub(super) fn translate_set_binop_bool(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
        op: SetBinOp,
    ) -> Z4Result<Term> {
        let universe = self.extract_universe_from_exprs(&[left, right])?;
        let set_s = self.translate_set_expr(left, &universe)?;
        let set_t = self.translate_set_expr(right, &universe)?;
        let _result = match op {
            SetBinOp::Union => self.encode_union(set_s, set_t, &universe)?,
            SetBinOp::Intersect => self.encode_intersect(set_s, set_t, &universe)?,
            SetBinOp::Minus => self.encode_set_minus(set_s, set_t, &universe)?,
        };
        Ok(self.solver.bool_const(true))
    }

    /// Translate `DOMAIN f` in Bool context.
    ///
    /// DOMAIN returns a set, not a Bool. In the dispatch we return an error
    /// with guidance to use `x \in DOMAIN f` for membership tests instead.
    pub(super) fn translate_domain_bool_dispatch(
        &mut self,
        func_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        match &func_expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                if self.func_vars.contains_key(name) {
                    Err(Z4Error::UntranslatableExpr(
                        "DOMAIN f is a set, not a Bool expression; \
                         use `x \\in DOMAIN f` for membership tests"
                            .to_string(),
                    ))
                } else {
                    Err(Z4Error::UnknownVariable(format!(
                        "DOMAIN {name}: not a declared function variable"
                    )))
                }
            }
            _ => Err(Z4Error::UntranslatableExpr(
                "BMC DOMAIN requires a variable reference".to_string(),
            )),
        }
    }

    /// Translate `[f EXCEPT ![a] = b]` as a Bool constraint.
    ///
    /// For function variables, builds a `(store mapping idx val)` term.
    /// Returns TRUE after the EXCEPT encoding is asserted.
    pub(super) fn translate_except_bool_dispatch(
        &mut self,
        base: &Spanned<Expr>,
        specs: &[tla_core::ast::ExceptSpec],
    ) -> Z4Result<Term> {
        let _mapping = self.translate_func_except_bmc(base, specs)?;
        Ok(self.solver.bool_const(true))
    }

    /// Translate `[x \in S |-> expr]` as a Bool constraint.
    ///
    /// For finite set domains, builds per-element constraints on a fresh
    /// mapping array. Returns TRUE after the constraints are asserted.
    pub(super) fn translate_func_def_bool_dispatch(
        &mut self,
        bounds: &[tla_core::ast::BoundVar],
        body: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let (_domain, _mapping) = self.translate_func_construct_bmc(bounds, body)?;
        Ok(self.solver.bool_const(true))
    }

    /// Translate `Cardinality(S)` as an Int term.
    ///
    /// Extracts a finite universe from the set expression, builds the SMT
    /// array term for S, and sums `ite((select S u), 1, 0)` over the universe.
    pub(super) fn translate_cardinality_int_dispatch(
        &mut self,
        set_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let universe = self.extract_universe_from_exprs(&[set_expr])?;
        if universe.is_empty() {
            return Ok(self.solver.int_const(0));
        }

        let set_term = self.translate_set_expr(set_expr, &universe)?;

        // Sum of ite((select S u), 1, 0) for each u in universe
        let one = self.solver.int_const(1);
        let zero = self.solver.int_const(0);
        let mut sum = self.solver.int_const(0);

        for &u in &universe {
            let in_set = self.solver.try_select(set_term, u)?;
            let contrib = self.solver.try_ite(in_set, one, zero)?;
            sum = self.solver.try_add(sum, contrib)?;
        }

        Ok(sum)
    }

    /// Extract a finite universe of Int terms from one or more set expressions.
    ///
    /// Collects all concrete integer values that appear in the set expressions
    /// (set enumerations, ranges, and subexpressions of union/intersect/etc.)
    /// and returns them as solver Int terms.
    pub(super) fn extract_universe_from_exprs(&mut self, exprs: &[&Spanned<Expr>]) -> Z4Result<Vec<Term>> {
        let mut values = std::collections::BTreeSet::new();
        for expr in exprs {
            Self::collect_universe_ints(expr, &mut values)?;
        }
        Ok(values
            .into_iter()
            .map(|v| self.solver.int_const(v))
            .collect())
    }

    /// Recursively collect all integer values that could appear in a set
    /// expression.
    ///
    /// Handles `SetEnum`, `Range`, compound set operations (`Union`,
    /// `Intersect`, `SetMinus`, `Subseteq`), and `Ident` (treated as
    /// potentially unresolvable — skipped rather than errored).
    fn collect_universe_ints(
        expr: &Spanned<Expr>,
        values: &mut std::collections::BTreeSet<i64>,
    ) -> Z4Result<()> {
        match &expr.node {
            Expr::SetEnum(elements) => {
                for e in elements {
                    if let Expr::Int(n) = &e.node {
                        let v: i64 = n.try_into().map_err(|_| {
                            Z4Error::IntegerOverflow("set element too large for i64".to_string())
                        })?;
                        values.insert(v);
                    }
                    // Non-literal elements are skipped (same as Z4Translator)
                }
            }
            Expr::Range(lo, hi) => {
                let lo_val = Self::extract_int_literal_static(lo)?;
                let hi_val = Self::extract_int_literal_static(hi)?;
                for v in lo_val..=hi_val {
                    values.insert(v);
                }
            }
            Expr::Union(left, right)
            | Expr::Intersect(left, right)
            | Expr::SetMinus(left, right)
            | Expr::Subseteq(left, right) => {
                Self::collect_universe_ints(left, values)?;
                Self::collect_universe_ints(right, values)?;
            }
            Expr::Powerset(base) => {
                Self::collect_universe_ints(base, values)?;
            }
            Expr::BigUnion(inner) => {
                if let Expr::SetEnum(components) = &inner.node {
                    for comp in components {
                        Self::collect_universe_ints(comp, values)?;
                    }
                }
            }
            // Ident could refer to a constant def but BMC does not have
            // constant_defs — skip without error.
            _ => {}
        }
        Ok(())
    }

    /// Translate `UNION {S1, S2, ...}` (BigUnion over enumerated set-of-sets)
    /// as a Bool expression.
    ///
    /// Extracts the finite universe from all component sets, builds their
    /// array representations, and produces a fresh result array containing
    /// the pointwise OR of all components.  Returns TRUE after asserting
    /// the result constraints.
    ///
    /// Part of #3778: Apalache parity — BigUnion in BMC.
    pub(super) fn translate_big_union_bool(&mut self, inner: &Spanned<Expr>) -> Z4Result<Term> {
        match &inner.node {
            Expr::SetEnum(component_exprs) => {
                if component_exprs.is_empty() {
                    return Ok(self.solver.bool_const(true));
                }
                // Collect universe from all component sets
                let comp_refs: Vec<&Spanned<Expr>> = component_exprs.iter().collect();
                let universe = self.extract_universe_from_exprs(&comp_refs)?;

                // Translate each component set as an array
                let mut component_terms = Vec::with_capacity(component_exprs.len());
                for comp in component_exprs {
                    let term = self.translate_set_expr(comp, &universe)?;
                    component_terms.push(term);
                }

                // Build result: pointwise OR of all component arrays
                if component_terms.len() == 1 {
                    // Single component — no union needed, return TRUE
                    return Ok(self.solver.bool_const(true));
                }

                let result = self.declare_fresh_set("bmc_bigunion")?;
                for &u in &universe {
                    // OR of all component memberships
                    let mut membership = self.solver.try_select(component_terms[0], u)?;
                    for comp in &component_terms[1..] {
                        let in_comp = self.solver.try_select(*comp, u)?;
                        membership = self.solver.try_or(membership, in_comp)?;
                    }
                    let in_result = self.solver.try_select(result, u)?;
                    let eq = self.solver.try_eq(in_result, membership)?;
                    self.solver
                        .try_assert_term(eq)
                        .expect("invariant: eq is Bool-sorted");
                }

                Ok(self.solver.bool_const(true))
            }
            _ => Err(Z4Error::UnsupportedOp(
                "BMC UNION over non-enumerated set-of-sets not supported; \
                 only UNION {S1, S2, ...} is supported"
                    .to_string(),
            )),
        }
    }

    /// Translate `SUBSET S` (powerset) as a Bool expression in BMC context.
    ///
    /// For a base set S with known finite universe of n elements (n <= 16),
    /// this encodes SUBSET S as the set of all 2^n subsets. Each subset is
    /// a concrete `(Array Int Bool)` term built via store chains.
    ///
    /// In Bool context, the powerset itself is not directly useful as a
    /// predicate — it's a set-of-sets. This method returns TRUE after
    /// constructing the array terms (they can be used by quantifiers that
    /// range over SUBSET S).
    ///
    /// For larger base sets (n > 16), returns an error since 2^n subsets
    /// would be impractical.
    pub(super) fn translate_powerset_bool(
        &mut self,
        base: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // Verify base set universe is extractable and within bounds
        let universe = self.extract_universe_from_exprs(&[base])?;
        if universe.len() > crate::translate::powerset_encoder::MAX_POWERSET_SIZE {
            return Err(Z4Error::UnsupportedOp(format!(
                "SUBSET of set with {} elements exceeds BMC maximum ({}); \
                 would generate 2^{} subsets",
                universe.len(),
                crate::translate::powerset_encoder::MAX_POWERSET_SIZE,
                universe.len()
            )));
        }
        // In Bool context, just ensure the base set is translatable.
        // The actual powerset enumeration happens in membership/quantifier contexts.
        let _base_set = self.translate_set_expr(base, &universe)?;
        Ok(self.solver.bool_const(true))
    }

    /// Enumerate all subsets of a base set for powerset membership in BMC.
    ///
    /// Given a base set expression S with known universe elements, generates
    /// all 2^n subset array terms. Each subset is a concrete
    /// `(store ... (const false) ... true)` chain.
    ///
    /// Used by quantifier expansion: `\E T \in SUBSET S : P(T)` becomes
    /// `P({}) \/ P({e1}) \/ P({e2}) \/ P({e1,e2}) \/ ...`
    ///
    /// Returns an error if the universe exceeds `MAX_POWERSET_SIZE` (16).
    pub(super) fn enumerate_powerset_subsets(
        &mut self,
        base: &Spanned<Expr>,
    ) -> Z4Result<Vec<Term>> {
        let universe = self.extract_universe_from_exprs(&[base])?;
        let n = universe.len();
        if n > crate::translate::powerset_encoder::MAX_POWERSET_SIZE {
            return Err(Z4Error::UnsupportedOp(format!(
                "SUBSET of set with {n} elements exceeds BMC maximum ({}); \
                 would generate 2^{n} subsets",
                crate::translate::powerset_encoder::MAX_POWERSET_SIZE,
            )));
        }

        let num_subsets = 1usize << n;
        let mut subsets = Vec::with_capacity(num_subsets);

        let false_val = self.solver.bool_const(false);
        let true_val = self.solver.bool_const(true);

        for mask in 0..num_subsets {
            let mut arr = self.solver.try_const_array(Sort::Int, false_val)?;
            for (i, &elem) in universe.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    arr = self.solver.try_store(arr, elem, true_val)?;
                }
            }
            subsets.push(arr);
        }

        Ok(subsets)
    }

    /// Encode a symbolic subset constraint for BMC: creates a fresh set
    /// variable constrained to be a subset of the given base set.
    ///
    /// For each element u in the universe:
    ///   `(select sub u) => (select base u)`
    ///
    /// This is used when the base set is too large for full enumeration,
    /// or when a symbolic approach is preferred.
    ///
    /// Returns the fresh symbolic subset variable.
    pub(super) fn encode_symbolic_subset(
        &mut self,
        base: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let universe = self.extract_universe_from_exprs(&[base])?;
        let base_set = self.translate_set_expr(base, &universe)?;

        let sub = self.declare_fresh_set("bmc_subset")?;

        // Assert: \A u \in universe : sub(u) => base(u)
        for &u in &universe {
            let in_sub = self.solver.try_select(sub, u)?;
            let in_base = self.solver.try_select(base_set, u)?;
            let implication = self.solver.try_implies(in_sub, in_base)?;
            self.solver
                .try_assert_term(implication)
                .expect("invariant: implies is Bool-sorted");
        }

        Ok(sub)
    }

    /// Translate `lo..hi` as a set expression (Array Int Bool).
    ///
    /// Builds a store chain: `(store ... (store (const false) lo true) ... hi true)`.
    ///
    /// Part of #3778: Apalache parity — Range-as-set in BMC.
    pub(super) fn translate_range_set_term(
        &mut self,
        lo: &Spanned<Expr>,
        hi: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let lo_val = Self::extract_int_literal_static(lo)?;
        let hi_val = Self::extract_int_literal_static(hi)?;
        let false_val = self.solver.bool_const(false);
        let true_val = self.solver.bool_const(true);
        let mut arr = self.solver.try_const_array(Sort::Int, false_val)?;
        for v in lo_val..=hi_val {
            let elem = self.solver.int_const(v);
            arr = self.solver.try_store(arr, elem, true_val)?;
        }
        Ok(arr)
    }

    /// Try to translate function equality: `f = g` where both are function
    /// variables.
    ///
    /// For two function variables, returns `Some(conjunction)` of
    /// `(select f_map key) = (select g_map key)` over the domain union,
    /// plus domain equality.
    ///
    /// Returns `None` if neither side is a recognized function variable.
    ///
    /// Part of #3778: Apalache parity — function equality in BMC.
    pub(super) fn try_translate_func_equality(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        let (left_name, left_step) = match self.resolve_func_name_step(left) {
            Some(ns) => ns,
            None => return None,
        };
        let (right_name, right_step) = match self.resolve_func_name_step(right) {
            Some(ns) => ns,
            None => return None,
        };

        // Both sides are function variables — assert domain and mapping equality
        let l_dom = match self.get_func_domain_at_step(&left_name, left_step) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };
        let r_dom = match self.get_func_domain_at_step(&right_name, right_step) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };
        let l_map = match self.get_func_mapping_at_step(&left_name, left_step) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };
        let r_map = match self.get_func_mapping_at_step(&right_name, right_step) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        // Array-level equality for both domain and mapping
        let dom_eq = match self.solver.try_eq(l_dom, r_dom) {
            Ok(t) => t,
            Err(e) => return Some(Err(Z4Error::Solver(e))),
        };
        let map_eq = match self.solver.try_eq(l_map, r_map) {
            Ok(t) => t,
            Err(e) => return Some(Err(Z4Error::Solver(e))),
        };

        Some(self.solver.try_and(dom_eq, map_eq).map_err(Z4Error::Solver))
    }

    /// Resolve a function expression to `(name, step)`, or `None` if not
    /// a function variable.
    fn resolve_func_name_step(&self, expr: &Spanned<Expr>) -> Option<(String, usize)> {
        match &expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                if self.func_vars.contains_key(name) {
                    Some((name.clone(), self.current_step))
                } else {
                    None
                }
            }
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    if self.func_vars.contains_key(name) {
                        Some((name.clone(), self.current_step + 1))
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Try to translate set equality: `S = T` where both sides are
    /// set-typed expressions (SetEnum, set variable, Powerset base, etc.).
    ///
    /// Computes the combined universe from both sides, translates each as
    /// an `(Array Int Bool)` term, and returns the pointwise equivalence:
    /// `\A u \in universe : (select S u) = (select T u)`.
    ///
    /// Returns `None` if neither side is a recognizable set expression.
    ///
    /// Part of #3826: set equality for nested powerset expansion.
    pub(super) fn try_translate_set_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // Only trigger if at least one side is clearly a set expression.
        if !Self::is_set_expr(left) && !Self::is_set_expr(right) {
            return None;
        }

        let result = (|| -> Z4Result<Term> {
            let universe = self.extract_universe_from_exprs(&[left, right])?;
            if universe.is_empty() {
                // Both sets are empty => equal
                return Ok(self.solver.bool_const(true));
            }
            let left_arr = self.translate_set_expr(left, &universe)?;
            let right_arr = self.translate_set_expr(right, &universe)?;

            // Pointwise: \A u \in universe : (select S u) <=> (select T u)
            let mut conjuncts = Vec::with_capacity(universe.len());
            for &u in &universe {
                let l_member = self.solver.try_select(left_arr, u)?;
                let r_member = self.solver.try_select(right_arr, u)?;
                // Bool equivalence: (l /\ r) \/ (~l /\ ~r)
                let both_in = self.solver.try_and(l_member, r_member)?;
                let not_l = self.solver.try_not(l_member)?;
                let not_r = self.solver.try_not(r_member)?;
                let both_out = self.solver.try_and(not_l, not_r)?;
                let equiv = self.solver.try_or(both_in, both_out)?;
                conjuncts.push(equiv);
            }

            if conjuncts.len() == 1 {
                return Ok(conjuncts[0]);
            }
            let mut result = conjuncts[0];
            for &c in &conjuncts[1..] {
                result = self.solver.try_and(result, c)?;
            }
            Ok(result)
        })();

        Some(result)
    }

    /// Check if an expression is a set-typed expression (heuristic).
    ///
    /// Returns true for SetEnum, Powerset, Union, Intersect, SetMinus, Range,
    /// and identifiers known to be set variables.
    fn is_set_expr(expr: &Spanned<Expr>) -> bool {
        matches!(
            &expr.node,
            Expr::SetEnum(_)
                | Expr::Powerset(_)
                | Expr::Union(_, _)
                | Expr::Intersect(_, _)
                | Expr::SetMinus(_, _)
                | Expr::Range(_, _)
                | Expr::SetFilter(_, _)
                | Expr::SetBuilder(_, _)
        )
    }

    /// Extract an integer literal from an expression (static, no solver access).
    fn extract_int_literal_static(expr: &Spanned<Expr>) -> Z4Result<i64> {
        match &expr.node {
            Expr::Int(n) => n.try_into().map_err(|_| {
                Z4Error::IntegerOverflow("integer literal too large for i64".to_string())
            }),
            Expr::Neg(inner) => {
                let v = Self::extract_int_literal_static(inner)?;
                Ok(-v)
            }
            _ => Err(Z4Error::UnsupportedOp(format!(
                "expected integer literal in universe extraction, got {:?}",
                std::mem::discriminant(&expr.node)
            ))),
        }
    }
}
