// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression conversion: CHC expressions to z4-core terms.

use super::context::{SmtContext, MAX_CONVERSION_NODES};
use crate::term_bridge::sort::chc_sort_to_core;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use num_bigint::BigInt;
use std::fmt::Write;
use z4_core::term::Symbol;
use z4_core::{Sort, TermId};

impl SmtContext {
    pub fn preprocess(expr: &ChcExpr) -> ChcExpr {
        // #6360: Single-pass feature scan replaces 6 individual `contains_*` walks.
        let features = expr.scan_features();

        // Simplify select-store chains FIRST (#6047): reduces
        // select(store(a, i, v), i) → v via ROW axioms at the expression level,
        // avoiding the massive eager axiom expansion in the SMT executor.
        let array_simplified = if features.has_array_ops {
            expr.simplify_array_ops()
        } else {
            expr.clone()
        };
        let simplified = array_simplified.propagate_constants();
        // #6360: shared core normalization chain (mixed-sort eq → ITE → mod →
        // negation → strict comparison).
        features.core_normalize(simplified)
    }

    /// Convert a CHC sort to a z4-core sort
    pub fn convert_sort(sort: &ChcSort) -> Sort {
        chc_sort_to_core(sort)
    }

    /// Get or create a term for a CHC variable.
    ///
    /// #6100: Always uses sort-qualified names (`{name}_{sort}`) as var_map keys
    /// to ensure deterministic TermId assignment regardless of variable encounter
    /// order. This eliminates warm/fresh context divergence where accumulated
    /// var_map entries from prior PDR iterations changed which sort got the
    /// unqualified name.
    ///
    /// The original CHC variable name is stored in `var_original_names` so that
    /// model extraction can emit original names for downstream lookups.
    fn get_or_create_var(&mut self, var: &ChcVar) -> TermId {
        // #6363: Build the sort-qualified key in a reusable scratch buffer
        // instead of allocating a fresh String on every lookup. On cache hits
        // (the common case), zero allocations occur.
        self.qualified_name_buf.clear();
        let _ = write!(self.qualified_name_buf, "{}_{}", var.name, var.sort);

        if let Some(&term) = self.var_map.get(self.qualified_name_buf.as_str()) {
            return term;
        }

        // Cache miss: allocate the key string for map insertion.
        let qualified_name: String = self.qualified_name_buf.clone();
        let sort = Self::convert_sort(&var.sort);
        let term = self.terms.mk_var(&qualified_name, sort);
        self.var_original_names
            .insert(qualified_name.clone(), var.name.clone());
        self.var_map.insert(qualified_name, term);
        term
    }

    /// Convert a CHC expression to a z4-core term
    pub fn convert_expr(&mut self, expr: &ChcExpr) -> TermId {
        // Guard against stack overflow on deep expression trees (e.g., from PDKind
        // iterations building deep conjunctions). Uses stacker to grow onto heap
        // when the thread stack runs low — matching the protection in expr.rs
        // traversals (#2759).
        crate::expr::maybe_grow_expr_stack(|| self.convert_expr_inner(expr))
    }

    /// Reset the conversion budget for a new conversion session.
    pub(crate) fn reset_conversion_budget(&mut self) {
        self.conversion_node_count = 0;
        self.conversion_budget_exceeded = false;
        self.ill_typed_bv_count = 0;
    }

    /// Return whether the conversion budget was exceeded in the current session.
    pub(crate) fn conversion_budget_exceeded(&self) -> bool {
        self.conversion_budget_exceeded
    }

    /// Return whether the conversion budget has been exhausted across multiple
    /// consecutive `check_sat` calls (#2472).
    ///
    /// Once this returns `true`, all future `check_sat` calls on this context
    /// will short-circuit to `Unknown`. Engines should check this in their main
    /// loops to terminate early rather than retrying doomed queries.
    pub(crate) fn is_budget_exhausted(&self) -> bool {
        self.conversion_budget_strikes >= super::context::MAX_CONVERSION_STRIKES
    }

    /// Check if all terms in the slice have BitVec sort.
    ///
    /// #6047: Array-sorted variables can appear in BV operations due to
    /// `translate_to_canonical_names` followed by `propagate_var_equalities`
    /// in `propagate_constants`. This defensive check prevents panics in
    /// z4-core's BV constructors (mk_bvult, mk_bvadd, etc.).
    fn all_bv_sorted(&self, terms: &[TermId]) -> bool {
        terms
            .iter()
            .all(|t| matches!(self.terms.sort(*t), Sort::BitVec(_)))
    }

    /// Record an ill-typed BV operation and return the budget-exceeded sentinel.
    ///
    /// #6047 soundness fix: Previously returned `mk_bool(false)` which injects
    /// `false` into the formula. This is unsound in predecessor/inductiveness
    /// queries where false makes the query artificially UNSAT (same pattern as
    /// #5508 Bool ordering bug). Instead, set `conversion_budget_exceeded` so
    /// the caller returns `SmtResult::Unknown`, letting PDR handle the uncertainty
    /// conservatively at each call site.
    fn ill_typed_bv_sentinel(&mut self) -> TermId {
        self.ill_typed_bv_count += 1;
        self.conversion_budget_exceeded = true;
        self.terms.mk_bool(true)
    }

    /// Coerce a pair of terms to matching sorts (#6084).
    ///
    /// When scalarization or CHC preprocessing introduces sort mismatches
    /// (e.g., `(= bv_var int_literal)` or `(= Array(BV,Bool) Array(Int,Bool))`),
    /// the z4-core layer requires both sides to have identical sorts. This inserts
    /// `int2bv` or `bv2nat` conversions as needed. For array sort mismatches, we
    /// accept `a` as the canonical sort (keeping `a` unchanged).
    fn coerce_int_bv_pair(&mut self, a: TermId, b: TermId) -> (TermId, TermId) {
        let sort_a = self.terms.sort(a).clone();
        let sort_b = self.terms.sort(b).clone();
        if sort_a == sort_b {
            return (a, b);
        }
        match (&sort_a, &sort_b) {
            (Sort::BitVec(bv), Sort::Int) => {
                let b_coerced = self.terms.mk_int2bv(bv.width, b);
                (a, b_coerced)
            }
            (Sort::Int, Sort::BitVec(bv)) => {
                let a_coerced = self.terms.mk_int2bv(bv.width, a);
                (a_coerced, b)
            }
            // Array sort mismatches: key sort differs (e.g., Array(BV32,Bool) vs
            // Array(Int,Bool)) from ConstArray conversion defaulting to Int key.
            // Recreate the const array with the correct key sort (#6084).
            (Sort::Array(arr_a), Sort::Array(arr_b))
                if arr_a.element_sort == arr_b.element_sort
                    && arr_a.index_sort != arr_b.index_sort =>
            {
                // Prefer `a`'s sort — recreate `b` as const array with `a`'s key sort.
                if let Some(default_val) = self.terms.get_const_array(b) {
                    let b_fixed = self
                        .terms
                        .mk_const_array(arr_a.index_sort.clone(), default_val);
                    (a, b_fixed)
                } else if let Some(default_val) = self.terms.get_const_array(a) {
                    let a_fixed = self
                        .terms
                        .mk_const_array(arr_b.index_sort.clone(), default_val);
                    (a_fixed, b)
                } else {
                    (a, b)
                }
            }
            _ => (a, b),
        }
    }

    fn convert_expr_inner(&mut self, expr: &ChcExpr) -> TermId {
        // Budget check: prevent unbounded expression tree growth (#2771).
        self.conversion_node_count += 1;
        if self.conversion_node_count > MAX_CONVERSION_NODES {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        }

        match expr {
            ChcExpr::Bool(b) => self.terms.mk_bool(*b),

            ChcExpr::Int(n) => self.terms.mk_int(BigInt::from(*n)),

            ChcExpr::BitVec(val, width) => self.terms.mk_bitvec(BigInt::from(*val), *width),

            ChcExpr::Real(num, denom) => {
                use num_rational::BigRational;
                let r = BigRational::new(BigInt::from(*num), BigInt::from(*denom));
                self.terms.mk_rational(r)
            }

            ChcExpr::Var(v) => self.get_or_create_var(v),

            ChcExpr::PredicateApp(name, id, args) => {
                // Serialize arguments for uniqueness key
                let arg_strs: Vec<String> = args.iter().map(|a| format!("{a}")).collect();
                let key = (*id, arg_strs);

                if let Some(&term) = self.pred_app_map.get(&key) {
                    return term;
                }

                // Create a fresh boolean variable for this predicate application
                let var_name = format!("{}_{}", name, self.pred_app_counter);
                self.pred_app_counter += 1;
                let term = self.terms.mk_var(&var_name, Sort::Bool);
                self.pred_app_map.insert(key, term);
                term
            }

            ChcExpr::FuncApp(name, sort, args) => {
                let term_args: Vec<TermId> = args.iter().map(|a| self.convert_expr(a)).collect();
                // Budget may have been exceeded during child conversion (#2771).
                if self.conversion_budget_exceeded {
                    return self.terms.mk_bool(true);
                }
                let term_sort = Self::convert_sort(sort);
                self.terms
                    .mk_app(Symbol::named(name.clone()), term_args, term_sort)
            }

            ChcExpr::Op(op, args) => {
                let term_args: Vec<TermId> = args.iter().map(|a| self.convert_expr(a)).collect();
                // Budget may have been exceeded during child conversion (#2771).
                // Return sentinel before passing mixed-sort children to term constructors
                // that would panic (e.g., mk_gt(int, bool)).
                if self.conversion_budget_exceeded {
                    return self.terms.mk_bool(true);
                }

                match op {
                    ChcOp::Not => {
                        assert_eq!(term_args.len(), 1);
                        // Guard: mk_not requires Bool-sorted argument. Array/BV
                        // expressions can reach here during CHC cube negation
                        // for problems with array predicate parameters. (#6047)
                        let arg = term_args[0];
                        if self.terms.sort(arg) == &Sort::Bool {
                            self.terms.mk_not(arg)
                        } else {
                            // Non-Bool under Not: treat as unsupported, return
                            // true (which makes the containing formula weaker,
                            // preserving soundness).
                            self.terms.mk_bool(true)
                        }
                    }
                    ChcOp::And => self.terms.mk_and(term_args),
                    ChcOp::Or => self.terms.mk_or(term_args),
                    ChcOp::Implies => {
                        assert_eq!(term_args.len(), 2);
                        self.terms.mk_implies(term_args[0], term_args[1])
                    }
                    ChcOp::Iff => {
                        assert_eq!(term_args.len(), 2);
                        // a <-> b is (a => b) /\ (b => a)
                        let ab = self.terms.mk_implies(term_args[0], term_args[1]);
                        let ba = self.terms.mk_implies(term_args[1], term_args[0]);
                        self.terms.mk_and(vec![ab, ba])
                    }
                    ChcOp::Add => self.terms.mk_add(term_args),
                    ChcOp::Sub => self.terms.mk_sub(term_args),
                    ChcOp::Mul => self.terms.mk_mul(term_args),
                    ChcOp::Div => {
                        assert_eq!(term_args.len(), 2);
                        self.terms.mk_intdiv(term_args[0], term_args[1])
                    }
                    ChcOp::Mod => {
                        assert_eq!(term_args.len(), 2);
                        self.terms.mk_mod(term_args[0], term_args[1])
                    }
                    ChcOp::Neg => {
                        assert_eq!(term_args.len(), 1);
                        self.terms.mk_neg(term_args[0])
                    }
                    ChcOp::Eq => {
                        assert_eq!(term_args.len(), 2);
                        let (a, b) = self.coerce_int_bv_pair(term_args[0], term_args[1]);
                        // #6047: After coercion, sorts may still differ (e.g., Array vs BV
                        // from ill-typed formulas in PDR interpolation). Propagate Unknown
                        // via budget mechanism to avoid unsound false injection (#5508 pattern).
                        if self.terms.sort(a) != self.terms.sort(b) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_eq(a, b)
                        }
                    }
                    ChcOp::Ne => {
                        assert_eq!(term_args.len(), 2);
                        // Encode `a != b` as `not (a = b)` rather than `distinct(a, b)`.
                        //
                        // `distinct` is a theory atom and requires explicit disequality support in
                        // theory solvers. Encoding as `not (= ...)` allows DPLL(T) to treat it as a
                        // Boolean negation of an equality atom, which is more robust for Z4's CHC
                        // auxiliary queries (e.g., invariant preservation checks).
                        let (a, b) = self.coerce_int_bv_pair(term_args[0], term_args[1]);
                        // #6047: Sort mismatch after coercion → trivially not-equal (true).
                        if self.terms.sort(a) != self.terms.sort(b) {
                            self.terms.mk_bool(true)
                        } else {
                            let eq = self.terms.mk_eq(a, b);
                            self.terms.mk_not(eq)
                        }
                    }
                    ChcOp::Lt => {
                        assert_eq!(term_args.len(), 2);
                        match self.terms.sort(term_args[0]).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_lt(term_args[0], term_args[1]),
                            Sort::BitVec(_) => {
                                // #6047: BV ordering from model substitution → unsigned compare
                                self.terms.mk_bvult(term_args[0], term_args[1])
                            }
                            Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool ordering semantics.
                                // For Bool (false=0, true=1): a < b ≡ ¬a ∧ b
                                let not_a = self.terms.mk_not(term_args[0]);
                                self.terms.mk_and(vec![not_a, term_args[1]])
                            }
                            _ => {
                                // #6047: Array/unsupported sort ordering → true (weaken)
                                self.terms.mk_bool(true)
                            }
                        }
                    }
                    ChcOp::Le => {
                        assert_eq!(term_args.len(), 2);
                        match self.terms.sort(term_args[0]).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_le(term_args[0], term_args[1]),
                            Sort::BitVec(_) => {
                                // #6047: BV ordering from model substitution → unsigned compare
                                self.terms.mk_bvule(term_args[0], term_args[1])
                            }
                            Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool Le semantics.
                                // a <= b ≡ a ⟹ b ≡ ¬a ∨ b
                                let not_a = self.terms.mk_not(term_args[0]);
                                self.terms.mk_or(vec![not_a, term_args[1]])
                            }
                            _ => {
                                // #6047: Array/unsupported sort ordering → true (weaken)
                                self.terms.mk_bool(true)
                            }
                        }
                    }
                    ChcOp::Gt => {
                        assert_eq!(term_args.len(), 2);
                        match self.terms.sort(term_args[0]).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_gt(term_args[0], term_args[1]),
                            Sort::BitVec(_) => {
                                // #6047: BV ordering from model substitution → unsigned compare
                                self.terms.mk_bvugt(term_args[0], term_args[1])
                            }
                            Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool Gt semantics.
                                // a > b ≡ a ∧ ¬b
                                let not_b = self.terms.mk_not(term_args[1]);
                                self.terms.mk_and(vec![term_args[0], not_b])
                            }
                            _ => {
                                // #6047: Array/unsupported sort ordering → true (weaken)
                                self.terms.mk_bool(true)
                            }
                        }
                    }
                    ChcOp::Ge => {
                        assert_eq!(term_args.len(), 2);
                        match self.terms.sort(term_args[0]).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_ge(term_args[0], term_args[1]),
                            Sort::BitVec(_) => {
                                // #6047: BV ordering from model substitution → unsigned compare
                                self.terms.mk_bvuge(term_args[0], term_args[1])
                            }
                            Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool Ge semantics.
                                // a >= b ≡ b ⟹ a ≡ ¬b ∨ a
                                let not_b = self.terms.mk_not(term_args[1]);
                                self.terms.mk_or(vec![not_b, term_args[0]])
                            }
                            _ => {
                                // #6047: Array/unsupported sort ordering → true (weaken)
                                self.terms.mk_bool(true)
                            }
                        }
                    }
                    ChcOp::Ite => {
                        assert_eq!(term_args.len(), 3);
                        // Coerce ITE branches to same sort (#6084).
                        let (then_br, else_br) =
                            self.coerce_int_bv_pair(term_args[1], term_args[2]);
                        self.terms.mk_ite(term_args[0], then_br, else_br)
                    }
                    ChcOp::Select => {
                        assert_eq!(term_args.len(), 2);
                        let array = term_args[0];
                        let mut index = term_args[1];
                        // Coerce index sort to match array's key sort (#6084).
                        // CHC expressions may mix Int/BitVec sorts across
                        // preprocessing; the z4-core layer requires exact match.
                        let Sort::Array(arr) = self.terms.sort(array).clone() else {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        };
                        let idx_sort = self.terms.sort(index).clone();
                        match (&arr.index_sort, &idx_sort) {
                            (Sort::BitVec(bv), Sort::Int) => {
                                index = self.terms.mk_int2bv(bv.width, index);
                            }
                            (Sort::Int, Sort::BitVec(_)) => {
                                index = self.terms.mk_bv2nat(index);
                            }
                            _ => {}
                        }
                        if self.terms.sort(index) != &arr.index_sort {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        }
                        self.terms.mk_select(array, index)
                    }
                    ChcOp::Store => {
                        assert_eq!(term_args.len(), 3);
                        let array = term_args[0];
                        let mut index = term_args[1];
                        let mut value = term_args[2];
                        // Coerce index and value sorts to match array sort (#6084).
                        let Sort::Array(arr) = self.terms.sort(array).clone() else {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        };
                        let idx_sort = self.terms.sort(index).clone();
                        match (&arr.index_sort, &idx_sort) {
                            (Sort::BitVec(bv), Sort::Int) => {
                                index = self.terms.mk_int2bv(bv.width, index);
                            }
                            (Sort::Int, Sort::BitVec(_)) => {
                                index = self.terms.mk_bv2nat(index);
                            }
                            _ => {}
                        }
                        let val_sort = self.terms.sort(value).clone();
                        match (&arr.element_sort, &val_sort) {
                            (Sort::BitVec(bv), Sort::Int) => {
                                value = self.terms.mk_int2bv(bv.width, value);
                            }
                            (Sort::Int, Sort::BitVec(_)) => {
                                value = self.terms.mk_bv2nat(value);
                            }
                            _ => {}
                        }
                        if self.terms.sort(index) != &arr.index_sort
                            || self.terms.sort(value) != &arr.element_sort
                        {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        }
                        self.terms.mk_store(array, index, value)
                    }
                    // Bitvector operations
                    //
                    // #6047: All BV operations have defensive sort guards. When
                    // Array-sorted canonical variables end up in BV expressions (due
                    // to name-based variable translation in PDR interpolation), the
                    // z4-core BV constructors would panic. Propagate Unknown via
                    // budget mechanism rather than injecting false (unsound in
                    // predecessor/inductiveness queries — #5508 pattern).
                    ChcOp::BvAdd
                    | ChcOp::BvSub
                    | ChcOp::BvMul
                    | ChcOp::BvUDiv
                    | ChcOp::BvURem
                    | ChcOp::BvSDiv
                    | ChcOp::BvSRem
                    | ChcOp::BvSMod
                    | ChcOp::BvAnd
                    | ChcOp::BvOr
                    | ChcOp::BvXor
                    | ChcOp::BvNand
                    | ChcOp::BvNor
                    | ChcOp::BvXnor
                    | ChcOp::BvShl
                    | ChcOp::BvLShr
                    | ChcOp::BvAShr
                    | ChcOp::BvConcat
                        if !self.all_bv_sorted(&term_args) =>
                    {
                        self.ill_typed_bv_sentinel()
                    }
                    ChcOp::BvAdd => self.terms.mk_bvadd(term_args),
                    ChcOp::BvSub => self.terms.mk_bvsub(term_args),
                    ChcOp::BvMul => self.terms.mk_bvmul(term_args),
                    ChcOp::BvUDiv => self.terms.mk_bvudiv(term_args),
                    ChcOp::BvURem => self.terms.mk_bvurem(term_args),
                    ChcOp::BvSDiv => self.terms.mk_bvsdiv(term_args),
                    ChcOp::BvSRem => self.terms.mk_bvsrem(term_args),
                    ChcOp::BvSMod => self.terms.mk_bvsmod(term_args),
                    ChcOp::BvAnd => self.terms.mk_bvand(term_args),
                    ChcOp::BvOr => self.terms.mk_bvor(term_args),
                    ChcOp::BvXor => self.terms.mk_bvxor(term_args),
                    ChcOp::BvNand => self.terms.mk_bvnand(term_args),
                    ChcOp::BvNor => self.terms.mk_bvnor(term_args),
                    ChcOp::BvXnor => self.terms.mk_bvxnor(term_args),
                    ChcOp::BvShl => self.terms.mk_bvshl(term_args),
                    ChcOp::BvLShr => self.terms.mk_bvlshr(term_args),
                    ChcOp::BvAShr => self.terms.mk_bvashr(term_args),
                    ChcOp::BvConcat => self.terms.mk_bvconcat(term_args),
                    ChcOp::BvNot => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvnot(term_args[0])
                        }
                    }
                    ChcOp::BvNeg => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvneg(term_args[0])
                        }
                    }
                    ChcOp::BvULt => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvult(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvULe => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvule(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvUGt => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvugt(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvUGe => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvuge(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSLt => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvslt(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSLe => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsle(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSGt => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsgt(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSGe => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsge(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvComp => {
                        assert_eq!(term_args.len(), 2);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvcomp(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::Bv2Nat => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bv2nat(term_args[0])
                        }
                    }
                    ChcOp::BvExtract(hi, lo) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvextract(*hi, *lo, term_args[0])
                        }
                    }
                    ChcOp::BvZeroExtend(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvzero_extend(*n, term_args[0])
                        }
                    }
                    ChcOp::BvSignExtend(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsign_extend(*n, term_args[0])
                        }
                    }
                    ChcOp::BvRotateLeft(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvrotate_left(*n, term_args[0])
                        }
                    }
                    ChcOp::BvRotateRight(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvrotate_right(*n, term_args[0])
                        }
                    }
                    ChcOp::BvRepeat(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvrepeat(*n, term_args[0])
                        }
                    }
                    ChcOp::Int2Bv(w) => {
                        assert_eq!(term_args.len(), 1);
                        // Int2Bv legitimately takes Int arg, no BV sort check
                        self.terms.mk_int2bv(*w, term_args[0])
                    }
                }
            }

            ChcExpr::ConstArrayMarker(_) => {
                // Marker shouldn't appear in real expressions - return a placeholder
                self.terms.mk_bool(true)
            }

            ChcExpr::IsTesterMarker(_) => {
                // Marker shouldn't appear in real expressions - return a placeholder
                self.terms.mk_bool(true)
            }

            ChcExpr::ConstArray(key_sort, val) => {
                // Create a constant array with the parsed key sort (#6084).
                let val_term = self.convert_expr(val);
                let core_key_sort = chc_sort_to_core(key_sort);
                self.terms.mk_const_array(core_key_sort, val_term)
            }
        }
    }
}
