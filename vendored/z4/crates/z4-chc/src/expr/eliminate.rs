// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression elimination transformations (ITE, mod/div, mixed-sort, array simplification).

use std::sync::Arc;

use super::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, ChcVar, ExprDepthGuard,
    MAX_EXPR_RECURSION_DEPTH, MAX_PREPROCESSING_NODES,
};

/// Shared state for expression elimination transformations (ITE, mod/div).
///
/// Both `eliminate_ite` and `eliminate_mod` need: a fresh-variable counter,
/// a list of collected definitional constraints, and a node budget (#2774).
struct EliminationState {
    /// Counter for generating unique variable names
    counter: u32,
    /// Collected definitional constraints
    constraints: Vec<ChcExpr>,
    /// Node traversal budget (#2774). Returns original expression when exhausted.
    budget: usize,
}

impl EliminationState {
    fn new() -> Self {
        Self {
            counter: 0,
            constraints: Vec::new(),
            budget: MAX_PREPROCESSING_NODES,
        }
    }

    /// Decrement budget by one. Returns false if budget is exhausted.
    fn tick(&mut self) -> bool {
        if self.budget == 0 {
            return false;
        }
        self.budget -= 1;
        true
    }

    fn fresh_var(&mut self, prefix: &str, sort: ChcSort) -> ChcVar {
        let name = format!("{}_{}", prefix, self.counter);
        self.counter += 1;
        ChcVar::new(name, sort)
    }
}

impl ChcExpr {
    /// Eliminate arithmetic ite expressions by introducing auxiliary variables and constraints.
    ///
    /// The CHC SMT backend ultimately relies on the LIA solver, which only supports linear
    /// integer/real arithmetic terms. Arithmetic-valued ite terms (e.g. `(ite c 1 0)`) create
    /// non-linear theory atoms like `(= x (ite ...))`, which can force the backend to return
    /// `unknown`. This pass rewrites arithmetic ite expressions into a fresh variable `v` with:
    /// - (=> c (= v t))
    /// - (=> (not c) (= v e))
    ///
    /// Boolean-valued ite expressions are left intact.
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn eliminate_ite(&self) -> Self {
        let mut state = EliminationState::new();
        let Some(transformed) = self.eliminate_ite_recursive(&mut state) else {
            return self.clone();
        };

        if state.constraints.is_empty() {
            transformed
        } else {
            let mut all_conjuncts = state.constraints;
            all_conjuncts.push(transformed);
            Self::and_vec(all_conjuncts)
        }
    }

    /// Eliminate mod expressions by introducing auxiliary variables and constraints.
    ///
    /// For each `(mod x k)` where k is a constant:
    /// - Introduces a fresh quotient variable q
    /// - Rewrites `(mod x k)` to `(x - k*q)` with constraints:
    ///   `0 <= (x - k*q)` and `(x - k*q) < |k|`
    ///
    /// For each `(div x k)` where k is a constant:
    /// - Introduces a fresh quotient variable q
    /// - Adds the same bounded-remainder constraints as for mod elimination
    /// - Replaces the div term with q
    ///
    /// For k = 0, follows SMT-LIB total semantics:
    /// - (mod x 0) = x
    /// - (div x 0) = 0
    ///
    /// Returns the transformed expression with all definitional constraints ANDed.
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn eliminate_mod(&self) -> Self {
        let mut state = EliminationState::new();
        let Some(transformed) = self.eliminate_mod_recursive(&mut state) else {
            return self.clone();
        };

        if state.constraints.is_empty() {
            transformed
        } else {
            // AND all constraints together with the transformed expression
            let mut all_conjuncts = state.constraints;
            all_conjuncts.push(transformed);
            Self::and_vec(all_conjuncts)
        }
    }

    /// Euclidean decomposition for mod/div elimination.
    ///
    /// Given `x` and non-zero divisor `k`, creates fresh variables `q` (quotient)
    /// and `r` (remainder) and adds constraints:
    ///   x = k * q + r, r >= 0, r < |k|
    ///
    /// Using named remainder/quotient variables (instead of inlining `x - k*q`)
    /// prevents expression tree duplication that causes conversion budget
    /// exhaustion in TPA's exponential composition.
    ///
    /// Returns `(quotient_var, remainder_var)`. Caller picks which to use:
    /// mod returns the remainder, div returns the quotient.
    fn euclidean_decompose(
        state: &mut EliminationState,
        x: Self,
        k: i64,
        prefix: &str,
    ) -> (ChcVar, ChcVar) {
        let q = state.fresh_var(&format!("_{prefix}_q"), ChcSort::Int);
        let r = state.fresh_var(&format!("_{prefix}_r"), ChcSort::Int);

        let k_abs_expr = Self::Int(k.saturating_abs());
        let q_expr = Self::Var(q.clone());
        let r_expr = Self::Var(r.clone());

        // x = k * q + r
        let k_times_q = Self::mul(Self::Int(k), q_expr);
        state
            .constraints
            .push(Self::eq(x, Self::add(k_times_q, r_expr.clone())));
        // r >= 0
        state
            .constraints
            .push(Self::ge(r_expr.clone(), Self::Int(0)));
        // r < |k|
        state.constraints.push(Self::lt(r_expr, k_abs_expr));

        (q, r)
    }

    /// Recursive helper for ite elimination.
    /// Returns `None` if the node budget is exhausted (#2774).
    fn eliminate_ite_recursive(&self, state: &mut EliminationState) -> Option<Self> {
        maybe_grow_expr_stack(|| {
            ExprDepthGuard::check()?;
            if !state.tick() {
                return None;
            }
            Some(match self {
                Self::Bool(_) | Self::Int(_) | Self::Real(_, _) | Self::Var(_) => self.clone(),

                Self::Op(ChcOp::Ite, args) if args.len() == 3 => {
                    let cond = args[0]
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| args[0].as_ref().clone());
                    let then_ = args[1]
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| args[1].as_ref().clone());
                    let else_ = args[2]
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| args[2].as_ref().clone());

                    let then_sort = then_.sort();
                    let else_sort = else_.sort();
                    if then_sort == else_sort && matches!(then_sort, ChcSort::Int | ChcSort::Real) {
                        let v = state.fresh_var("_ite", then_sort);
                        let v_expr = Self::Var(v);

                        let eq_then = Self::eq(v_expr.clone(), then_);
                        let eq_else = Self::eq(v_expr.clone(), else_);

                        state.constraints.push(Self::implies(cond.clone(), eq_then));
                        state
                            .constraints
                            .push(Self::implies(Self::not(cond), eq_else));

                        return Some(v_expr);
                    }

                    Self::ite(cond, then_, else_)
                }

                _ => self.map_children_with(|child| {
                    child
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| child.clone())
                }),
            })
        })
    }

    /// Recursive helper for mod elimination.
    /// Returns `None` if the node budget is exhausted (#2774).
    fn eliminate_mod_recursive(&self, state: &mut EliminationState) -> Option<Self> {
        maybe_grow_expr_stack(|| {
            ExprDepthGuard::check()?;
            if !state.tick() {
                return None;
            }
            Some(match self {
                Self::Op(ChcOp::Mod, args)
                    if args.len() == 2 && matches!(args[1].as_ref(), Self::Int(_)) =>
                {
                    let Self::Int(k) = args[1].as_ref() else {
                        return None; // #6091: defensive
                    };
                    if *k == 0 {
                        // SMT-LIB total semantics: (mod x 0) = x
                        return args[0].eliminate_mod_recursive(state);
                    }
                    let x = args[0]
                        .eliminate_mod_recursive(state)
                        .unwrap_or_else(|| args[0].as_ref().clone());
                    let (_, r) = Self::euclidean_decompose(state, x, *k, "mod");
                    Self::Var(r)
                }

                Self::Op(ChcOp::Div, args)
                    if args.len() == 2 && matches!(args[1].as_ref(), Self::Int(_)) =>
                {
                    let Self::Int(k) = args[1].as_ref() else {
                        return None; // #6091: defensive
                    };
                    if *k == 0 {
                        // SMT-LIB total semantics: (div x 0) = 0
                        return Some(Self::Int(0));
                    }
                    let x = args[0]
                        .eliminate_mod_recursive(state)
                        .unwrap_or_else(|| args[0].as_ref().clone());
                    let (q, _) = Self::euclidean_decompose(state, x, *k, "div");
                    Self::Var(q)
                }

                _ => self.map_children_with(|child| {
                    child
                        .eliminate_mod_recursive(state)
                        .unwrap_or_else(|| child.clone())
                }),
            })
        })
    }

    /// Rewrite mixed-sort equalities `(= Int_expr Bool_expr)` into
    /// `(= Int_expr (ite Bool_expr 1 0))`.
    ///
    /// CHC benchmarks (e.g., id_o20) contain patterns like `(= D (= E 0))` where D has sort
    /// Int and `(= E 0)` has sort Bool. When sent to the LRA solver as a theory atom, the
    /// Bool sub-expression marks the atom as unsupported, causing Unknown results (#6167).
    ///
    /// This pass lifts the Bool-to-Int coercion to an ITE, which `eliminate_ite` then handles
    /// by introducing a fresh Int variable with definitional constraints. This is the same
    /// pattern used by FlatZinc `bool2int` (#5925).
    ///
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged.
    pub(crate) fn eliminate_mixed_sort_eq(&self) -> Self {
        use std::cell::Cell;

        const MAX_NODES: usize = MAX_PREPROCESSING_NODES;
        let budget = Cell::new(MAX_NODES);

        fn rewrite_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::Var(_) => expr.clone(),

                    ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                        let a = rewrite_inner(&args[0], budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        let b = rewrite_inner(&args[1], budget, depth + 1)
                            .unwrap_or_else(|| args[1].as_ref().clone());

                        let sa = a.sort();
                        let sb = b.sort();

                        if sa == ChcSort::Bool && matches!(sb, ChcSort::Int | ChcSort::Real) {
                            // (= Bool_expr Int_expr) → (= (ite Bool_expr 1 0) Int_expr)
                            let coerced = if sb == ChcSort::Real {
                                ChcExpr::ite(a, ChcExpr::Real(1, 1), ChcExpr::Real(0, 1))
                            } else {
                                ChcExpr::ite(a, ChcExpr::Int(1), ChcExpr::Int(0))
                            };
                            ChcExpr::eq(coerced, b)
                        } else if sb == ChcSort::Bool && matches!(sa, ChcSort::Int | ChcSort::Real)
                        {
                            // (= Int_expr Bool_expr) → (= Int_expr (ite Bool_expr 1 0))
                            let coerced = if sa == ChcSort::Real {
                                ChcExpr::ite(b, ChcExpr::Real(1, 1), ChcExpr::Real(0, 1))
                            } else {
                                ChcExpr::ite(b, ChcExpr::Int(1), ChcExpr::Int(0))
                            };
                            ChcExpr::eq(a, coerced)
                        } else {
                            ChcExpr::eq(a, b)
                        }
                    }

                    _ => expr.map_children_with(|child| {
                        rewrite_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        rewrite_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }

    /// Simplify array operations using McCarthy's read-over-write axioms.
    ///
    /// Applies these rewrite rules bottom-up:
    ///
    /// 1. **ROW1 (same index):** `select(store(a, i, v), j)` → `v` when `i == j`
    ///    syntactically.
    /// 2. **ROW2 (different index):** `select(store(a, i, v), j)` → `select(a, j)`
    ///    when `i ≠ j` is provable from distinct constants.
    /// 3. **Const-array select:** `select(ConstArray(val), _)` → `val`.
    ///
    /// ROW1 recurses on nested stores: `select(store(store(a, 0, x), 1, y), 0)`
    /// first applies ROW2 (outer: idx=1, sel=0, different) yielding
    /// `select(store(a, 0, x), 0)`, then ROW1 (same index) yielding `x`.
    ///
    /// This eliminates select-store chains that would otherwise require the SMT
    /// solver's eager array axiom generation, which creates massive term expansion
    /// for BV-indexed arrays (#6047).
    ///
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged.
    pub(crate) fn simplify_array_ops(&self) -> Self {
        use std::cell::Cell;

        const MAX_NODES: usize = MAX_PREPROCESSING_NODES;
        let budget = Cell::new(MAX_NODES);

        fn simplify_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::Var(_) => expr.clone(),

                    // select(arr, idx) — try to reduce after simplifying children.
                    ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                        let arr = simplify_inner(&args[0], budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        let idx = simplify_inner(&args[1], budget, depth + 1)
                            .unwrap_or_else(|| args[1].as_ref().clone());
                        reduce_select(&arr, &idx)
                    }

                    // Recurse into all other expressions.
                    _ => expr.map_children_with(|child| {
                        simplify_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        /// Reduce `select(arr, idx)` using ROW axioms.
        ///
        /// Recurses on nested stores: checks the outermost store first,
        /// then peels it off (ROW2) or returns the stored value (ROW1).
        fn reduce_select(arr: &ChcExpr, idx: &ChcExpr) -> ChcExpr {
            match arr {
                // select(store(base, store_idx, val), idx)
                ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                    let base = &args[0];
                    let store_idx = &args[1];
                    let val = &args[2];

                    if store_idx.as_ref() == idx {
                        // ROW1: same index → return stored value.
                        val.as_ref().clone()
                    } else if are_distinct_constants(store_idx, idx) {
                        // ROW2: provably different indices → look through store.
                        reduce_select(base, idx)
                    } else {
                        // Indices are symbolic and not provably equal/different.
                        // Return the select unreduced.
                        ChcExpr::select(arr.clone(), idx.clone())
                    }
                }
                // select(ConstArray(val), _) → val
                ChcExpr::ConstArray(_, val) => val.as_ref().clone(),
                // No reduction possible.
                _ => ChcExpr::select(arr.clone(), idx.clone()),
            }
        }

        /// Check if two constant expressions are provably distinct.
        ///
        /// Returns true when both are ground values of the same sort with
        /// different values: Int literals, BitVec literals, or Bool literals.
        fn are_distinct_constants(a: &Arc<ChcExpr>, b: &ChcExpr) -> bool {
            match (a.as_ref(), b) {
                (ChcExpr::Int(x), ChcExpr::Int(y)) => x != y,
                (ChcExpr::BitVec(x, xw), ChcExpr::BitVec(y, yw)) => xw == yw && x != y,
                (ChcExpr::Bool(x), ChcExpr::Bool(y)) => x != y,
                _ => false,
            }
        }

        simplify_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }
}
