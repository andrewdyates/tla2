// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier translation for Z4.
//!
//! Handles translation of TLA+ quantified formulas (`\A`, `\E`) and `CHOOSE`
//! expressions over finite domains. Two strategies are used:
//!
//! 1. **Expansion** (original) — enumerate domain elements and build a
//!    conjunction/disjunction of substituted bodies. Works for small domains.
//!
//! 2. **Skolemization** (Apalache-style) — for `\E x \in S: P(x)`, introduce
//!    a fresh constant `__sk_x_N` and assert `__sk_x_N \in S /\ P[__sk_x_N/x]`.
//!    Replaces O(|S|) disjuncts with 2 constraints. Used for larger domains
//!    and integer ranges.
//!
//! `CHOOSE x \in S: P(x)` uses the same Skolem encoding but returns the
//! witness constant as the result term.
//!
//! # Expansion threshold
//!
//! Domains with `<= SKOLEM_THRESHOLD` elements use direct expansion.
//! Larger finite domains and all integer ranges use Skolemization.

use std::collections::HashMap;

use num_bigint::BigInt;
use tla_core::ast::{BoundVar, Expr};
use tla_core::name_intern::NameId;
use tla_core::Spanned;
use tla_core::{ExprFold, SpanPolicy, SubstituteExpr};
use z4_dpll::api::{Sort, Term};

use crate::error::{Z4Error, Z4Result};

use super::Z4Translator;

/// Maximum domain size for direct expansion. Domains larger than this
/// use Skolemization instead. The value 16 balances formula size (16
/// disjuncts is manageable) against solver load.
const SKOLEM_THRESHOLD: i64 = 16;

/// Maximum integer range size that will be expanded directly for `\A`.
/// Beyond this, the conjunction is too large and we fall back to
/// unsupported (no native `\forall` in QF_LIA).
const FORALL_RANGE_EXPANSION_LIMIT: i64 = 100;

impl Z4Translator {
    // ------------------------------------------------------------------
    // Public entry points
    // ------------------------------------------------------------------

    /// Translate a quantified formula (`\A` or `\E`).
    pub(super) fn translate_quantifier(
        &mut self,
        bounds: &[BoundVar],
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Term> {
        // For finite domains, expand or Skolemize the quantifier
        if let Some(expanded) = self.try_expand_finite_quantifier(bounds, body, is_forall)? {
            return Ok(expanded);
        }

        Err(Z4Error::UnsupportedOp(
            "quantifiers over infinite domains not supported in QF_LIA".to_string(),
        ))
    }

    /// Translate `CHOOSE x \in S : P(x)` as an Int-sorted result.
    ///
    /// Introduces a fresh Skolem constant `__ch_x_N`, asserts membership
    /// and the predicate, and returns the constant as the result term.
    ///
    /// Supported domains: `SetEnum`, `Range`, `BOOLEAN`, `SetFilter`.
    /// For `SetFilter({z \in S : Q(z)})`, rewrites to
    /// `CHOOSE x \in S : Q[x/z] /\ body`.
    pub(super) fn translate_choose_int(
        &mut self,
        bound: &BoundVar,
        body: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let var_name = &bound.name.node;
        let domain = bound
            .domain
            .as_ref()
            .ok_or_else(|| Z4Error::UnsupportedOp("CHOOSE without domain".to_string()))?;

        // SetFilter: CHOOSE x \in {z \in S : Q(z)} : body
        // Rewrite to CHOOSE x \in S : Q[x/z] /\ body
        if let Expr::SetFilter(filter_bound, pred) = &domain.node {
            if let Some(inner_domain) = &filter_bound.domain {
                let filter_var = &filter_bound.name.node;

                let replacement =
                    Spanned::new(Expr::Ident(var_name.clone(), NameId::INVALID), pred.span);
                let mut sub = SubstituteExpr {
                    subs: HashMap::from([(filter_var.as_str(), &replacement)]),
                    span_policy: SpanPolicy::Preserve,
                };
                let pred_spanned = sub.fold_expr(*pred.clone());

                // New body: filter_pred /\ original_body
                let new_body = Expr::And(Box::new(pred_spanned), Box::new(body.clone()));
                let new_body_spanned = Spanned::new(new_body, body.span);

                let new_bound = BoundVar {
                    name: bound.name.clone(),
                    domain: Some(inner_domain.clone()),
                    pattern: bound.pattern.clone(),
                };

                return self.translate_choose_int(&new_bound, &new_body_spanned);
            }
        }

        // Create a fresh Int Skolem constant
        let sk_name = self.fresh_name(&format!("ch_{var_name}"));
        let sk_term = self.solver.declare_const(&sk_name, Sort::Int);

        // Register the Skolem constant in our var map BEFORE translating
        // the predicate, since the substituted body will reference it.
        self.vars
            .insert(sk_name.clone(), (super::TlaSort::Int, sk_term));

        // Assert membership constraint
        self.assert_skolem_membership(sk_term, domain)?;

        // Assert P[sk/x]
        let sk_expr = Expr::Ident(sk_name, NameId::INVALID);
        let pred = self.substitute_and_translate(body, var_name, &sk_expr)?;
        self.assert(pred);

        Ok(sk_term)
    }

    /// Translate `CHOOSE x \in S : P(x)` as a Bool-sorted result.
    ///
    /// Same as [`translate_choose_int`] but for Boolean-valued CHOOSE.
    pub(super) fn translate_choose_bool(
        &mut self,
        bound: &BoundVar,
        body: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let var_name = &bound.name.node;
        let domain = bound
            .domain
            .as_ref()
            .ok_or_else(|| Z4Error::UnsupportedOp("CHOOSE without domain".to_string()))?;

        // For BOOLEAN domain, the Skolem constant is Bool-sorted
        if let Expr::Ident(name, _) = &domain.node {
            if name == "BOOLEAN" {
                let sk_name = self.fresh_name(&format!("ch_{var_name}"));
                let sk_term = self.solver.declare_const(&sk_name, Sort::Bool);
                self.vars
                    .insert(sk_name.clone(), (super::TlaSort::Bool, sk_term));

                // Assert P[sk/x]
                let sk_expr = Expr::Ident(sk_name, NameId::INVALID);
                let pred = self.substitute_and_translate(body, var_name, &sk_expr)?;
                self.assert(pred);

                return Ok(sk_term);
            }
        }

        Err(Z4Error::UnsupportedOp(
            "CHOOSE with non-BOOLEAN domain returning Bool not supported".to_string(),
        ))
    }

    // ------------------------------------------------------------------
    // Finite quantifier dispatch
    // ------------------------------------------------------------------

    /// Try to expand a bounded quantifier over a finite domain.
    ///
    /// Returns `Ok(Some(term))` if the domain was recognized and handled,
    /// `Ok(None)` if the domain form is not supported.
    fn try_expand_finite_quantifier(
        &mut self,
        bounds: &[BoundVar],
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Option<Term>> {
        // Only handle single bound for now
        if bounds.len() != 1 {
            return Ok(None);
        }

        let bound = &bounds[0];
        let domain = match &bound.domain {
            Some(d) => d,
            None => return Ok(None),
        };

        // Check for BOOLEAN domain (always expand — only 2 elements)
        if let Expr::Ident(name, _) = &domain.node {
            if name == "BOOLEAN" {
                return self
                    .expand_boolean_quantifier(bound, body, is_forall)
                    .map(Some);
            }
        }

        // Check for finite set enumeration {e1, e2, ...}
        if let Expr::SetEnum(elements) = &domain.node {
            if is_forall {
                // \A always expands (conjunction over elements)
                return self
                    .expand_set_enum_quantifier(bound, elements, body, is_forall)
                    .map(Some);
            }
            // \E: Skolemize for large sets, expand for small
            if elements.len() as i64 > SKOLEM_THRESHOLD {
                return self
                    .skolemize_exists_set_enum(bound, elements, body)
                    .map(Some);
            }
            return self
                .expand_set_enum_quantifier(bound, elements, body, is_forall)
                .map(Some);
        }

        // Check for range lo..hi
        if let Expr::Range(lo, hi) = &domain.node {
            if let (Expr::Int(lo_val), Expr::Int(hi_val)) = (&lo.node, &hi.node) {
                let range_size = hi_val - lo_val + BigInt::from(1);
                if let Ok(size) = i64::try_from(&range_size) {
                    if size <= 0 {
                        // Empty range
                        return Ok(Some(self.solver.bool_const(is_forall)));
                    }
                    if !is_forall {
                        // \E x \in a..b : P(x) — Skolemize for large, expand for small
                        if size > SKOLEM_THRESHOLD {
                            return self
                                .skolemize_exists_range(bound, lo_val, hi_val, body)
                                .map(Some);
                        }
                        return self
                            .expand_range_quantifier(bound, lo_val, hi_val, body, false)
                            .map(Some);
                    }
                    // \A x \in a..b — expand if small enough
                    if size <= FORALL_RANGE_EXPANSION_LIMIT {
                        return self
                            .expand_range_quantifier(bound, lo_val, hi_val, body, true)
                            .map(Some);
                    }
                }
            }
        }

        // Check for RecordSet domain: \Q r \in [a : S, b : T] : body
        // Expand via Cartesian product over field domains.
        if let Expr::RecordSet(fields) = &domain.node {
            return self
                .expand_record_set_quantifier(bound, fields, body, is_forall)
                .map(Some);
        }

        // Check for SetFilter domain: \Q y \in {z \in S : P(z)} : body
        if let Expr::SetFilter(filter_bound, pred) = &domain.node {
            if let Some(inner_domain) = &filter_bound.domain {
                let filter_var = &filter_bound.name.node;
                let bound_var = &bound.name.node;

                // Substitute filter variable with bound variable in predicate
                let replacement =
                    Spanned::new(Expr::Ident(bound_var.clone(), NameId::INVALID), pred.span);
                let mut sub = SubstituteExpr {
                    subs: HashMap::from([(filter_var.as_str(), &replacement)]),
                    span_policy: SpanPolicy::Preserve,
                };
                let pred_spanned = sub.fold_expr(*pred.clone());

                let new_body = if is_forall {
                    // \A y \in {z \in S : P(z)} : Q(y) => \A y \in S : P(y) => Q(y)
                    Expr::Implies(Box::new(pred_spanned), Box::new(body.clone()))
                } else {
                    // \E y \in {z \in S : P(z)} : Q(y) => \E y \in S : P(y) /\ Q(y)
                    Expr::And(Box::new(pred_spanned), Box::new(body.clone()))
                };
                let new_body_spanned = Spanned::new(new_body, body.span);

                let new_bound = BoundVar {
                    name: bound.name.clone(),
                    domain: Some(inner_domain.clone()),
                    pattern: bound.pattern.clone(),
                };

                return self.try_expand_finite_quantifier(
                    &[new_bound],
                    &new_body_spanned,
                    is_forall,
                );
            }
        }

        // Check for Powerset domain: \Q x \in SUBSET S : P(x)
        // Part of #3826: wire nested SUBSET encoding into z4 Init enumeration
        if let Expr::Powerset(base) = &domain.node {
            return self
                .expand_powerset_quantifier(bound, base, body, is_forall)
                .map(Some);
        }

        Ok(None)
    }

    // ------------------------------------------------------------------
    // Powerset quantifier expansion (Part of #3826)
    // ------------------------------------------------------------------

    /// Maximum elements in the inner set for simple SUBSET expansion.
    ///
    /// With |S| = n, `SUBSET S` has 2^n elements. At n=16, that is
    /// 65536 subsets — still tractable for expansion but getting large.
    const MAX_POWERSET_SIZE: usize = 16;

    /// Maximum inner set size for nested SUBSET(SUBSET S) without
    /// cardinality filter. With |S| = n, the unfiltered base has 2^n
    /// elements and enumeration produces 2^(2^n) solutions.
    const MAX_NESTED_INNER_UNFILTERED: usize = 4;

    /// Expand a quantifier over a powerset domain: `\Q x \in SUBSET S : P(x)`.
    ///
    /// Detects nested `SUBSET(SUBSET S)` and routes to the
    /// [`NestedPowersetEncoder`]-based handler. For simple `SUBSET S`,
    /// enumerates all 2^|S| subsets and expands the body for each.
    fn expand_powerset_quantifier(
        &mut self,
        bound: &BoundVar,
        base: &Spanned<Expr>,
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Term> {
        // Detect nested SUBSET pattern: base is SUBSET(inner)
        // meaning the original domain was SUBSET(SUBSET(inner))
        if let Expr::Powerset(inner) = &base.node {
            return self.expand_nested_powerset_quantifier(bound, inner, body, is_forall);
        }

        // Simple SUBSET S: enumerate all subsets of S
        let var_name = &bound.name.node;

        // Extract concrete integer elements from the base set
        let universe = self.extract_universe_ints_for_quantifier(base)?;
        if universe.is_empty() {
            // SUBSET {} = {{}}, only one value: the empty set
            let empty_set = Expr::SetEnum(Vec::new());
            return self.substitute_and_translate(body, var_name, &empty_set);
        }

        if universe.len() > Self::MAX_POWERSET_SIZE {
            return Err(Z4Error::UnsupportedOp(format!(
                "SUBSET of set with {} elements produces {} subsets; \
                 exceeds expansion limit of 2^{}",
                universe.len(),
                1u64 << universe.len(),
                Self::MAX_POWERSET_SIZE,
            )));
        }

        // Enumerate all 2^n subsets
        let num_subsets = 1usize << universe.len();
        let mut results = Vec::with_capacity(num_subsets);

        for mask in 0..num_subsets {
            // Build the subset as a SetEnum expression
            let mut members = Vec::new();
            for (i, &elem) in universe.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    members.push(Spanned::dummy(Expr::Int(BigInt::from(elem))));
                }
            }
            let subset_expr = Expr::SetEnum(members);
            let body_term = self.substitute_and_translate(body, var_name, &subset_expr)?;
            results.push(body_term);
        }

        self.combine_bool_terms(&results, is_forall)
    }

    /// Expand a quantifier over a nested powerset domain:
    /// `\Q T \in SUBSET(SUBSET S) : P(T)`.
    ///
    /// Uses [`NestedPowersetEncoder`] to enumerate solutions efficiently:
    ///
    /// 1. Extract the inner universe S (e.g., Nodes = {1..5})
    /// 2. Try to detect a cardinality filter from the body:
    ///    `\A e \in T : Cardinality(e) = K` reduces base to C(|S|, K) elements
    /// 3. Compute filtered base elements (k-subsets) or all subsets
    /// 4. Use `NestedPowersetEncoder` to enumerate all valid outer sets
    /// 5. For each outer set, substitute a concrete `SetEnum(SetEnum(...))`
    ///    value into the body and translate
    ///
    /// For SpanTreeTest5Nodes: S = {1..5}, K = 2, base = C(5,2) = 10 edges,
    /// solutions = 2^10 = 1024 edge sets.
    fn expand_nested_powerset_quantifier(
        &mut self,
        bound: &BoundVar,
        inner_base: &Spanned<Expr>,
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Term> {
        use super::nested_powerset::{NestedPowersetConfig, NestedPowersetEncoder};

        let var_name = &bound.name.node;

        // Step 1: Extract inner universe as concrete integers
        let inner_universe = self.extract_universe_ints_for_quantifier(inner_base)?;
        if inner_universe.is_empty() {
            // SUBSET(SUBSET {}) = {{}}, only one value: the empty set
            let empty_set = Expr::SetEnum(Vec::new());
            return self.substitute_and_translate(body, var_name, &empty_set);
        }

        // Step 2: Try to detect cardinality filter from body
        let cardinality_k = detect_cardinality_filter(body, var_name);

        // Step 3: Compute base elements
        let base_elements = if let Some(k) = cardinality_k {
            // Filtered: only k-element subsets of inner universe
            super::nested_powerset::k_subsets(&inner_universe, k)
        } else if inner_universe.len() <= Self::MAX_NESTED_INNER_UNFILTERED {
            // Small enough for all subsets (2^n base elements)
            Self::all_subsets_as_base_elements(&inner_universe)
        } else {
            return Err(Z4Error::UnsupportedOp(format!(
                "SUBSET(SUBSET S) with |S| = {} and no cardinality filter is too large; \
                 would produce 2^{} base elements. Add a Cardinality filter or reduce S.",
                inner_universe.len(),
                inner_universe.len()
            )));
        };

        if base_elements.is_empty() {
            // Only one outer set: the empty set
            let empty_set = Expr::SetEnum(Vec::new());
            return self.substitute_and_translate(body, var_name, &empty_set);
        }

        // Step 4: Enumerate all outer sets using NestedPowersetEncoder
        let mut encoder = NestedPowersetEncoder::new(base_elements)?;
        let config = NestedPowersetConfig {
            max_solutions: 2_000_000,
            solve_timeout: Some(std::time::Duration::from_secs(60)),
        };
        let solutions = encoder.enumerate_all(&config)?;

        if solutions.solutions.is_empty() {
            return Ok(self.solver.bool_const(is_forall));
        }

        // Step 5: For each solution, build a concrete Expr and substitute
        let mut results = Vec::with_capacity(solutions.solutions.len());

        for solution in &solutions.solutions {
            let set_of_sets_expr = Self::base_elements_to_set_enum(solution);
            let body_term = self.substitute_and_translate(body, var_name, &set_of_sets_expr)?;
            results.push(body_term);
        }

        self.combine_bool_terms(&results, is_forall)
    }

    /// Extract concrete integer values from a set expression for quantifier
    /// expansion. Supports `SetEnum`, `Range`, `Ident` (constant defs), and
    /// compound set ops.
    fn extract_universe_ints_for_quantifier(&self, expr: &Spanned<Expr>) -> Z4Result<Vec<i64>> {
        let mut values = std::collections::BTreeSet::new();
        self.collect_universe_ints_recursive(expr, &mut values)?;
        Ok(values.into_iter().collect())
    }

    /// Recursively collect integer values from a set expression.
    fn collect_universe_ints_recursive(
        &self,
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
                }
            }
            Expr::Range(lo, hi) => {
                let lo_val = self.extract_int_literal(lo)?;
                let hi_val = self.extract_int_literal(hi)?;
                for v in lo_val..=hi_val {
                    values.insert(v);
                }
            }
            Expr::Powerset(base) => {
                self.collect_universe_ints_recursive(base, values)?;
            }
            Expr::Union(left, right)
            | Expr::Intersect(left, right)
            | Expr::SetMinus(left, right) => {
                self.collect_universe_ints_recursive(left, values)?;
                self.collect_universe_ints_recursive(right, values)?;
            }
            Expr::Ident(name, _) => {
                if let Some(def) = self.constant_defs.get(name).cloned() {
                    self.collect_universe_ints_recursive(&def, values)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Compute all subsets of a set as BaseElements (for small inner sets).
    fn all_subsets_as_base_elements(
        elements: &[i64],
    ) -> Vec<super::nested_powerset::BaseElement> {
        let n = elements.len();
        let num_subsets = 1usize << n;
        let mut result = Vec::with_capacity(num_subsets);
        for mask in 0..num_subsets {
            let mut members = Vec::new();
            for (i, &elem) in elements.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    members.push(elem);
                }
            }
            result.push(super::nested_powerset::BaseElement { members });
        }
        result
    }

    /// Convert a list of BaseElements to an `Expr::SetEnum` of `Expr::SetEnum`s.
    fn base_elements_to_set_enum(elements: &[super::nested_powerset::BaseElement]) -> Expr {
        let inner_sets: Vec<Spanned<Expr>> = elements
            .iter()
            .map(|elem| {
                let members: Vec<Spanned<Expr>> = elem
                    .members
                    .iter()
                    .map(|&m| Spanned::dummy(Expr::Int(BigInt::from(m))))
                    .collect();
                Spanned::dummy(Expr::SetEnum(members))
            })
            .collect();
        Expr::SetEnum(inner_sets)
    }

    // ------------------------------------------------------------------
    // Skolemization for \E
    // ------------------------------------------------------------------

    /// Skolemize `\E x \in {e1, ..., en} : P(x)`.
    ///
    /// Introduces a fresh Int constant `__sk_x_N` and asserts:
    ///   `__sk_x_N \in {e1,...,en} /\ P[__sk_x_N/x]`
    ///
    /// This replaces O(n) disjuncts with 2 constraints.
    fn skolemize_exists_set_enum(
        &mut self,
        bound: &BoundVar,
        elements: &[Spanned<Expr>],
        body: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let var_name = &bound.name.node;

        // Create Skolem constant
        let sk_name = self.fresh_name(&format!("sk_{var_name}"));
        let sk_term = self.solver.declare_const(&sk_name, Sort::Int);

        // Assert membership: sk \in {e1, ..., en}
        // Encoded as: sk = e1 \/ sk = e2 \/ ... \/ sk = en
        // Uses balanced tree for large membership disjunctions.
        let mut membership_terms = Vec::with_capacity(elements.len());
        for elem in elements {
            let elem_term = self.translate_int(elem)?;
            let eq = self.solver.try_eq(sk_term, elem_term)?;
            membership_terms.push(eq);
        }
        let membership = self.combine_bool_terms(&membership_terms, false)?;
        self.assert(membership);

        // Register the Skolem constant
        self.vars
            .insert(sk_name.clone(), (super::TlaSort::Int, sk_term));

        // Assert P[sk/x]
        let sk_expr = Expr::Ident(sk_name, NameId::INVALID);
        let pred = self.substitute_and_translate(body, var_name, &sk_expr)?;
        self.assert(pred);

        // The quantifier itself is now trivially TRUE (constraints are
        // side-asserted). Return TRUE so that the enclosing formula
        // remains well-formed.
        Ok(self.solver.bool_const(true))
    }

    /// Skolemize `\E x \in lo..hi : P(x)`.
    ///
    /// Introduces a fresh Int constant `__sk_x_N` and asserts:
    ///   `lo <= __sk_x_N /\ __sk_x_N <= hi /\ P[__sk_x_N/x]`
    fn skolemize_exists_range(
        &mut self,
        bound: &BoundVar,
        lo: &BigInt,
        hi: &BigInt,
        body: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let var_name = &bound.name.node;

        // Create Skolem constant
        let sk_name = self.fresh_name(&format!("sk_{var_name}"));
        let sk_term = self.solver.declare_const(&sk_name, Sort::Int);

        // Assert bounds: lo <= sk /\ sk <= hi
        let lo_i64 = i64::try_from(lo)
            .map_err(|_| Z4Error::IntegerOverflow(format!("range lower bound too large: {lo}")))?;
        let hi_i64 = i64::try_from(hi)
            .map_err(|_| Z4Error::IntegerOverflow(format!("range upper bound too large: {hi}")))?;
        let lo_term = self.solver.int_const(lo_i64);
        let hi_term = self.solver.int_const(hi_i64);
        let ge_lo = self.solver.try_ge(sk_term, lo_term)?;
        let le_hi = self.solver.try_le(sk_term, hi_term)?;
        self.assert(ge_lo);
        self.assert(le_hi);

        // Register the Skolem constant
        self.vars
            .insert(sk_name.clone(), (super::TlaSort::Int, sk_term));

        // Assert P[sk/x]
        let sk_expr = Expr::Ident(sk_name, NameId::INVALID);
        let pred = self.substitute_and_translate(body, var_name, &sk_expr)?;
        self.assert(pred);

        Ok(self.solver.bool_const(true))
    }

    // ------------------------------------------------------------------
    // Direct expansion (original algorithms)
    // ------------------------------------------------------------------

    /// Combine a list of Bool terms into a conjunction (is_forall=true) or
    /// disjunction (is_forall=false) using a balanced binary tree.
    ///
    /// Optimizations applied:
    /// - **Empty list**: returns the identity element (TRUE for AND, FALSE for OR).
    /// - **Singleton**: returns the single term directly.
    /// - **Constant folding**: drops identity elements; short-circuits on
    ///   absorbing element (FALSE in AND, TRUE in OR).
    /// - **Balanced tree**: splits remaining terms at the midpoint so the
    ///   solver sees a balanced tree instead of a left-skewed chain. This
    ///   helps DPLL unit propagation and clause learning.
    fn combine_bool_terms(&mut self, terms: &[Term], is_forall: bool) -> Z4Result<Term> {
        let identity = self.solver.bool_const(is_forall);
        let absorb = self.solver.bool_const(!is_forall);

        // Constant-fold: remove identity elements, short-circuit on absorb.
        let mut filtered = Vec::with_capacity(terms.len());
        for &t in terms {
            if t == absorb {
                return Ok(absorb);
            }
            if t != identity {
                filtered.push(t);
            }
        }

        match filtered.len() {
            0 => Ok(identity),
            1 => Ok(filtered[0]),
            _ => self.combine_balanced(&filtered, is_forall),
        }
    }

    /// Recursively build a balanced binary tree of AND/OR from a non-empty slice.
    fn combine_balanced(&mut self, terms: &[Term], is_forall: bool) -> Z4Result<Term> {
        debug_assert!(!terms.is_empty());
        if terms.len() == 1 {
            return Ok(terms[0]);
        }
        if terms.len() == 2 {
            return if is_forall {
                Ok(self.solver.try_and(terms[0], terms[1])?)
            } else {
                Ok(self.solver.try_or(terms[0], terms[1])?)
            };
        }
        let mid = terms.len() / 2;
        let left = self.combine_balanced(&terms[..mid], is_forall)?;
        let right = self.combine_balanced(&terms[mid..], is_forall)?;
        if is_forall {
            Ok(self.solver.try_and(left, right)?)
        } else {
            Ok(self.solver.try_or(left, right)?)
        }
    }

    /// Expand a quantifier over BOOLEAN.
    fn expand_boolean_quantifier(
        &mut self,
        bound: &BoundVar,
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Term> {
        let var_name = &bound.name.node;

        let body_true = self.substitute_and_translate(body, var_name, &Expr::Bool(true))?;
        let body_false = self.substitute_and_translate(body, var_name, &Expr::Bool(false))?;

        self.combine_bool_terms(&[body_true, body_false], is_forall)
    }

    /// Expand a quantifier over a finite set enumeration.
    fn expand_set_enum_quantifier(
        &mut self,
        bound: &BoundVar,
        elements: &[Spanned<Expr>],
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Term> {
        if elements.is_empty() {
            return Ok(self.solver.bool_const(is_forall));
        }

        // Singleton fast path: skip combine machinery entirely.
        if elements.len() == 1 {
            return self.substitute_and_translate(body, &bound.name.node, &elements[0].node);
        }

        let var_name = &bound.name.node;
        let mut substituted_bodies = Vec::with_capacity(elements.len());

        for elem in elements {
            let substituted = self.substitute_and_translate(body, var_name, &elem.node)?;
            substituted_bodies.push(substituted);
        }

        self.combine_bool_terms(&substituted_bodies, is_forall)
    }

    /// Expand a quantifier over an integer range.
    fn expand_range_quantifier(
        &mut self,
        bound: &BoundVar,
        lo: &BigInt,
        hi: &BigInt,
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Term> {
        if lo > hi {
            return Ok(self.solver.bool_const(is_forall));
        }

        // Singleton fast path.
        if lo == hi {
            return self.substitute_and_translate(body, &bound.name.node, &Expr::Int(lo.clone()));
        }

        let var_name = &bound.name.node;
        let mut substituted_bodies = Vec::new();

        let mut i = lo.clone();
        while &i <= hi {
            let substituted =
                self.substitute_and_translate(body, var_name, &Expr::Int(i.clone()))?;
            substituted_bodies.push(substituted);
            i += 1;
        }

        self.combine_bool_terms(&substituted_bodies, is_forall)
    }

    // ------------------------------------------------------------------
    // Membership constraints for Skolem constants
    // ------------------------------------------------------------------

    /// Assert that a Skolem constant is a member of a given domain.
    ///
    /// Handles `SetEnum`, `Range`, and `BOOLEAN` domains.
    fn assert_skolem_membership(&mut self, sk_term: Term, domain: &Spanned<Expr>) -> Z4Result<()> {
        match &domain.node {
            Expr::Ident(name, _) if name == "BOOLEAN" => {
                // BOOLEAN membership is trivial for Bool sort —
                // sk is already Bool-sorted so no constraint needed.
                // For Int sort, this is an error (handled by caller).
                Ok(())
            }
            Expr::SetEnum(elements) => {
                if elements.is_empty() {
                    // Empty domain — CHOOSE in empty set is a TLA+ error,
                    // but we assert FALSE to make solver detect it.
                    let f = self.solver.bool_const(false);
                    self.assert(f);
                    return Ok(());
                }
                let mut disj = Vec::with_capacity(elements.len());
                for elem in elements {
                    let elem_term = self.translate_int(elem)?;
                    let eq = self.solver.try_eq(sk_term, elem_term)?;
                    disj.push(eq);
                }
                // Uses balanced tree for large membership disjunctions.
                let membership = self.combine_bool_terms(&disj, false)?;
                self.assert(membership);
                Ok(())
            }
            Expr::Range(lo, hi) => {
                let lo_term = self.translate_int(lo)?;
                let hi_term = self.translate_int(hi)?;
                let ge_lo = self.solver.try_ge(sk_term, lo_term)?;
                let le_hi = self.solver.try_le(sk_term, hi_term)?;
                self.assert(ge_lo);
                self.assert(le_hi);
                Ok(())
            }
            // SetFilter: sk \in {z \in S : Q(z)} => sk \in S /\ Q[sk/z]
            Expr::SetFilter(filter_bound, pred) => {
                if let Some(inner_domain) = &filter_bound.domain {
                    // Assert membership in the inner domain
                    self.assert_skolem_membership(sk_term, inner_domain)?;

                    // Find the Skolem constant name so we can substitute
                    let sk_name = self
                        .vars
                        .iter()
                        .find(|(_, (_, t))| *t == sk_term)
                        .map(|(name, _)| name.clone())
                        .unwrap_or_else(|| "sk".to_string());

                    // Assert the filter predicate with sk substituted for the bound var
                    let filter_var = &filter_bound.name.node;
                    let replacement =
                        Spanned::new(Expr::Ident(sk_name, NameId::INVALID), pred.span);
                    let mut sub = SubstituteExpr {
                        subs: HashMap::from([(filter_var.as_str(), &replacement)]),
                        span_policy: SpanPolicy::Preserve,
                    };
                    let pred_substituted = sub.fold_expr(*pred.clone());
                    let pred_term = self.translate_bool(&pred_substituted)?;
                    self.assert(pred_term);
                    Ok(())
                } else {
                    Err(Z4Error::UnsupportedOp(
                        "CHOOSE over SetFilter without domain".to_string(),
                    ))
                }
            }
            _ => Err(Z4Error::UnsupportedOp(format!(
                "CHOOSE over unsupported domain type: {:?}",
                super::extended_ops::expr_variant_name(&domain.node)
            ))),
        }
    }

    // ------------------------------------------------------------------
    // RecordSet quantifier expansion (Cartesian product)
    // ------------------------------------------------------------------

    /// Expand a quantifier over a record set domain via Cartesian product.
    ///
    /// `\A r \in [a : S, b : T] : P(r)` becomes the conjunction/disjunction
    /// over all combinations of field values from the Cartesian product S x T.
    fn expand_record_set_quantifier(
        &mut self,
        bound: &BoundVar,
        fields: &[(Spanned<String>, Spanned<Expr>)],
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<Term> {
        let var_name = &bound.name.node;

        // Extract domain elements for each field
        let mut field_domains: Vec<(String, Vec<Spanned<Expr>>)> = Vec::new();
        for (field_name, field_domain) in fields {
            let elements = self.extract_domain_elements(field_domain)?;
            if elements.is_empty() {
                // Empty field domain -> vacuous truth for \A, false for \E
                return Ok(self.solver.bool_const(is_forall));
            }
            field_domains.push((field_name.node.clone(), elements));
        }

        // Compute Cartesian product of all field domains
        let field_names: Vec<String> = field_domains.iter().map(|(n, _)| n.clone()).collect();
        let element_lists: Vec<&[Spanned<Expr>]> = field_domains
            .iter()
            .map(|(_, elems)| elems.as_slice())
            .collect();
        let combos = cartesian_product(&element_lists);

        if combos.is_empty() {
            return Ok(self.solver.bool_const(is_forall));
        }

        // For each combination, build a record literal and substitute
        let mut results = Vec::with_capacity(combos.len());
        for combo in &combos {
            // Build record literal: [a |-> v1, b |-> v2, ...]
            let record_fields: Vec<(Spanned<String>, Spanned<Expr>)> = field_names
                .iter()
                .zip(combo.iter())
                .map(|(name, val)| (Spanned::new(name.clone(), body.span), (*val).clone()))
                .collect();
            let record_expr = Expr::Record(record_fields);

            let substituted = self.substitute_and_translate(body, var_name, &record_expr)?;
            results.push(substituted);
        }

        self.combine_bool_terms(&results, is_forall)
    }

    /// Extract concrete domain elements from a set expression.
    ///
    /// Supports `SetEnum`, `Range`, and `BOOLEAN`.
    fn extract_domain_elements(&self, expr: &Spanned<Expr>) -> Z4Result<Vec<Spanned<Expr>>> {
        match &expr.node {
            Expr::SetEnum(elements) => Ok(elements.clone()),
            Expr::Range(lo, hi) => {
                if let (Expr::Int(lo_val), Expr::Int(hi_val)) = (&lo.node, &hi.node) {
                    let lo_i64: i64 = lo_val.try_into().map_err(|_| {
                        Z4Error::IntegerOverflow("range lower bound too large".to_string())
                    })?;
                    let hi_i64: i64 = hi_val.try_into().map_err(|_| {
                        Z4Error::IntegerOverflow("range upper bound too large".to_string())
                    })?;
                    let elements: Vec<Spanned<Expr>> = (lo_i64..=hi_i64)
                        .map(|i| Spanned::new(Expr::Int(BigInt::from(i)), expr.span))
                        .collect();
                    Ok(elements)
                } else {
                    Err(Z4Error::UnsupportedOp(
                        "non-literal range bounds in record set domain".to_string(),
                    ))
                }
            }
            Expr::Ident(name, _) if name == "BOOLEAN" => Ok(vec![
                Spanned::new(Expr::Bool(true), expr.span),
                Spanned::new(Expr::Bool(false), expr.span),
            ]),
            _ => Err(Z4Error::UnsupportedOp(format!(
                "cannot extract finite domain elements from {}",
                super::extended_ops::expr_variant_name(&expr.node)
            ))),
        }
    }

    // ------------------------------------------------------------------
    // Shared substitution helper
    // ------------------------------------------------------------------

    /// Substitute a value for a variable and translate the result to Bool.
    pub(super) fn substitute_and_translate(
        &mut self,
        expr: &Spanned<Expr>,
        var_name: &str,
        replacement: &Expr,
    ) -> Z4Result<Term> {
        let replacement_spanned = Spanned::new(replacement.clone(), expr.span);
        let mut sub = SubstituteExpr {
            subs: HashMap::from([(var_name, &replacement_spanned)]),
            span_policy: SpanPolicy::Preserve,
        };
        let substituted = sub.fold_expr(expr.clone());
        let mut state_var_sub = SubstituteStateVar {
            var_name,
            replacement,
        };
        let substituted = state_var_sub.fold_expr(substituted);
        self.translate_bool(&substituted)
    }
}

/// Compute the Cartesian product of multiple element lists.
///
/// Returns a vector of combinations, where each combination is a vector
/// of references to the elements from each input list.
///
/// Example: `cartesian_product(&[&[a, b], &[x, y]])` returns
/// `[[a, x], [a, y], [b, x], [b, y]]`.
fn cartesian_product<'a, T>(lists: &[&'a [T]]) -> Vec<Vec<&'a T>> {
    if lists.is_empty() {
        return vec![vec![]];
    }
    let mut result: Vec<Vec<&'a T>> = vec![vec![]];
    for list in lists {
        let mut new_result = Vec::new();
        for combo in &result {
            for item in *list {
                let mut new_combo = combo.clone();
                new_combo.push(item);
                new_result.push(new_combo);
            }
        }
        result = new_result;
    }
    result
}

struct SubstituteStateVar<'a> {
    var_name: &'a str,
    replacement: &'a Expr,
}

impl ExprFold for SubstituteStateVar<'_> {
    fn fold_state_var(
        &mut self,
        name: String,
        idx: u16,
        id: tla_core::name_intern::NameId,
    ) -> Expr {
        if name == self.var_name {
            self.replacement.clone()
        } else {
            Expr::StateVar(name, idx, id)
        }
    }
}

// ------------------------------------------------------------------
// Cardinality filter detection for nested powerset (Part of #3826)
// ------------------------------------------------------------------

/// Detect a cardinality filter pattern in the body of a nested powerset
/// quantifier.
///
/// Looks for the pattern:
/// `... /\ \A e \in Var : Cardinality(e) = K /\ ...`
///
/// where `Var` is the bound variable of the outer quantifier.
/// Returns `Some(K)` if found, `None` otherwise.
fn detect_cardinality_filter(body: &Spanned<Expr>, var_name: &str) -> Option<usize> {
    detect_cardinality_in_expr(&body.node, var_name)
}

/// Recursively search for a cardinality filter in an expression tree.
fn detect_cardinality_in_expr(expr: &Expr, var_name: &str) -> Option<usize> {
    match expr {
        // Conjunction: check both sides
        Expr::And(left, right) => detect_cardinality_in_expr(&left.node, var_name)
            .or_else(|| detect_cardinality_in_expr(&right.node, var_name)),
        // \A e \in Var : Cardinality(e) = K
        Expr::Forall(bounds, inner_body) => {
            if bounds.len() == 1 {
                let bound = &bounds[0];
                // Check if domain is our variable
                if let Some(domain) = &bound.domain {
                    let domain_is_var = matches!(
                        &domain.node,
                        Expr::Ident(name, _) | Expr::StateVar(name, ..)
                        if name == var_name
                    );
                    if domain_is_var {
                        // Check if body is Cardinality(e) = K
                        return extract_cardinality_eq(&inner_body.node, &bound.name.node);
                    }
                }
            }
            None
        }
        // Also check inside Implies (from SetFilter desugaring of \A)
        Expr::Implies(_, consequent) => {
            detect_cardinality_in_expr(&consequent.node, var_name)
        }
        _ => None,
    }
}

/// Extract K from `Cardinality(var) = K` pattern.
fn extract_cardinality_eq(expr: &Expr, elem_var: &str) -> Option<usize> {
    if let Expr::Eq(left, right) = expr {
        // Try both orders: Cardinality(e) = K and K = Cardinality(e)
        if let Some(k) = match_cardinality_eq_inner(&left.node, &right.node, elem_var) {
            return Some(k);
        }
        if let Some(k) = match_cardinality_eq_inner(&right.node, &left.node, elem_var) {
            return Some(k);
        }
    }
    // Also handle conjunction: Cardinality(e) = K /\ more_stuff
    if let Expr::And(left, right) = expr {
        if let Some(k) = extract_cardinality_eq(&left.node, elem_var) {
            return Some(k);
        }
        return extract_cardinality_eq(&right.node, elem_var);
    }
    None
}

/// Match `Cardinality(var) = int_literal` pattern.
fn match_cardinality_eq_inner(maybe_card: &Expr, maybe_k: &Expr, elem_var: &str) -> Option<usize> {
    // Check if left side is Cardinality(var)
    if let Expr::Apply(op, args) = maybe_card {
        if let Expr::Ident(name, _) = &op.node {
            if name == "Cardinality" && args.len() == 1 {
                // Check if argument is our element variable
                let arg_is_var = matches!(
                    &args[0].node,
                    Expr::Ident(n, _) | Expr::StateVar(n, ..)
                    if n == elem_var
                );
                if arg_is_var {
                    // Extract K from the other side
                    if let Expr::Int(k) = maybe_k {
                        if let Ok(k_val) = usize::try_from(k) {
                            return Some(k_val);
                        }
                    }
                }
            }
        }
    }
    None
}
