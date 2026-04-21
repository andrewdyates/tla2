// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression tree predicate checks: contains_array_ops, contains_uf_apps, etc.

use super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, ChcVar, MAX_EXPR_RECURSION_DEPTH};

impl ChcExpr {
    /// Check if the expression contains any array operations (select, store)
    pub fn contains_array_ops(&self) -> bool {
        fn contains_array_ops_inner(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true;
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _) => false,
                ChcExpr::Var(v) => matches!(v.sort, ChcSort::Array(_, _)),
                ChcExpr::Op(op, args) => {
                    matches!(op, ChcOp::Select | ChcOp::Store)
                        || args
                            .iter()
                            .any(|a| contains_array_ops_inner(a.as_ref(), depth + 1))
                }
                ChcExpr::PredicateApp(_, _, args) => args
                    .iter()
                    .any(|a| contains_array_ops_inner(a.as_ref(), depth + 1)),
                ChcExpr::FuncApp(_, sort, args) => {
                    matches!(sort, ChcSort::Array(_, _))
                        || args
                            .iter()
                            .any(|a| contains_array_ops_inner(a.as_ref(), depth + 1))
                }
                ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => false,
                ChcExpr::ConstArray(_, _) => true,
            })
        }

        contains_array_ops_inner(self, 0)
    }

    /// Check if the expression contains any datatype-sorted variables or
    /// function applications (constructors, selectors, testers).
    pub(crate) fn contains_dt_ops(&self) -> bool {
        self.scan_features().has_dt
    }

    /// Whether this expression contains uninterpreted function applications.
    ///
    /// BvToInt abstraction converts BV operations to UF applications (e.g.
    /// `__bv2int_and_1_w32`). These require an EUF solver in the DPLL(T) loop
    /// to maintain congruence closure and prevent the LIA solver from flagging
    /// them as unsupported (#6047).
    pub fn contains_uf_apps(&self) -> bool {
        fn contains_uf_inner(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true;
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => false,
                ChcExpr::FuncApp(_, _, _) => true,
                ChcExpr::Op(_, args) => args
                    .iter()
                    .any(|a| contains_uf_inner(a.as_ref(), depth + 1)),
                ChcExpr::PredicateApp(_, _, args) => args
                    .iter()
                    .any(|a| contains_uf_inner(a.as_ref(), depth + 1)),
                ChcExpr::ConstArray(_, val) => contains_uf_inner(val, depth + 1),
            })
        }

        contains_uf_inner(self, 0)
    }

    /// Recursive check: does any `Op` node in this expression satisfy `predicate`?
    ///
    /// This is the single implementation backing all `contains_mod`, `contains_ite`,
    /// etc. methods. Each public method is a thin wrapper supplying its predicate.
    ///
    /// Returns `true` conservatively if recursion depth is exceeded.
    fn contains_op_matching(&self, predicate: &dyn Fn(&ChcOp) -> bool) -> bool {
        fn inner(expr: &ChcExpr, predicate: &dyn Fn(&ChcOp) -> bool, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true;
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_) => false,
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    args.iter().any(|a| inner(a, predicate, depth + 1))
                }
                ChcExpr::Op(op, args) => {
                    predicate(op) || args.iter().any(|a| inner(a, predicate, depth + 1))
                }
                ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => false,
                ChcExpr::ConstArray(_ks, val) => inner(val, predicate, depth + 1),
            })
        }

        inner(self, predicate, 0)
    }

    /// Check if expression contains any `mod` operations.
    pub(crate) fn contains_mod(&self) -> bool {
        self.contains_op_matching(&|op| matches!(op, ChcOp::Mod))
    }

    /// Check if expression contains `mod` or `div` operations.
    pub(crate) fn contains_mod_or_div(&self) -> bool {
        self.contains_op_matching(&|op| matches!(op, ChcOp::Mod | ChcOp::Div))
    }

    /// Check if all `mod`/`div` operations in this expression have constant
    /// (integer literal) divisors. Returns `true` if the expression contains
    /// mod/div AND all divisors are `ChcExpr::Int(_)`.
    ///
    /// When this returns `true`, the SMT solver's LIA theory can handle the
    /// mod/div natively, so pre-elimination is unnecessary. Skipping elimination
    /// preserves the modular structure that PDR needs for synthesizing invariants
    /// like `A mod 6 = 0` (#1362, designs/2026-03-20-unsolved-benchmark-root-cause-analysis.md).
    pub(crate) fn all_mod_div_have_constant_divisors(&self) -> bool {
        fn check(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return false; // Conservative: assume non-constant if too deep
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::Mod | ChcOp::Div, args) if args.len() == 2 => {
                    // Divisor must be a constant integer
                    if !matches!(args[1].as_ref(), ChcExpr::Int(_)) {
                        return false;
                    }
                    // Recurse into the dividend (which may contain nested mod/div)
                    check(args[0].as_ref(), depth + 1)
                }
                ChcExpr::Op(_, args) => args.iter().all(|a| check(a.as_ref(), depth + 1)),
                _ => true, // Leaf nodes or non-op nodes are fine
            })
        }
        self.contains_mod_or_div() && check(self, 0)
    }

    /// Check if expression contains mod/div auxiliary variables from TS-level
    /// mod elimination (names starting with `_mod_q_` or `_mod_r_`).
    ///
    /// These variables are introduced by `TransitionSystem::eliminate_mod_tracking_vars`
    /// and carry Euclidean decomposition constraints. When such variables are present
    /// in expressions being model-verified, the model must contain their values for
    /// evaluation to be complete. Missing aux var values cause `Indeterminate`
    /// verification results that should not be accepted as SAT (#7380).
    pub fn has_mod_aux_vars(&self) -> bool {
        self.vars()
            .iter()
            .any(|v| v.name.starts_with("_mod_q_") || v.name.starts_with("_mod_r_"))
    }

    /// Check if expression contains BV operations that BvToInt cannot encode
    /// exactly (bitwise, shift, rotation, signed div/rem/mod). These operations
    /// are over-approximated as uninterpreted functions by BvToInt, losing
    /// precision. When absent, BvToInt is exact and BvToBool bit-blasting can
    /// be skipped to avoid predicate arity explosion (#5877).
    pub(crate) fn contains_bv_bitwise_ops(&self) -> bool {
        self.contains_op_matching(&|op| {
            matches!(
                op,
                ChcOp::BvAnd
                    | ChcOp::BvOr
                    | ChcOp::BvXor
                    | ChcOp::BvNand
                    | ChcOp::BvNor
                    | ChcOp::BvXnor
                    | ChcOp::BvNot
                    | ChcOp::BvShl
                    | ChcOp::BvLShr
                    | ChcOp::BvAShr
                    | ChcOp::BvRotateLeft(_)
                    | ChcOp::BvRotateRight(_)
                    | ChcOp::BvRepeat(_)
                    | ChcOp::BvSDiv
                    | ChcOp::BvSRem
                    | ChcOp::BvSMod
            )
        })
    }

    /// Check if expression contains nonlinear integer multiplication (Mul of two
    /// non-constant sub-expressions). These produce Unknown from the LIA solver.
    pub(crate) fn contains_nonlinear_mul(&self) -> bool {
        fn inner(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true; // Conservative: assume nonlinear if too deep
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::Mul, args) => {
                    let non_const_count = args
                        .iter()
                        .filter(|a| !matches!(a.as_ref(), ChcExpr::Int(_) | ChcExpr::Real(_, _)))
                        .count();
                    if non_const_count >= 2 {
                        return true;
                    }
                    args.iter().any(|a| inner(a, depth + 1))
                }
                ChcExpr::Op(_, args) => args.iter().any(|a| inner(a, depth + 1)),
                ChcExpr::ConstArray(_ks, val) => inner(val, depth + 1),
                ChcExpr::PredicateApp(_, _, args) => args.iter().any(|a| inner(a, depth + 1)),
                ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| inner(a, depth + 1)),
                _ => false,
            })
        }
        inner(self, 0)
    }

    /// Check if expression contains any `ite` operations.
    ///
    /// Production callers use `scan_features().has_ite` instead (#6360).
    /// Retained for test assertions.
    #[cfg(test)]
    pub(crate) fn contains_ite(&self) -> bool {
        self.contains_op_matching(&|op| matches!(op, ChcOp::Ite))
    }

    /// Check if expression contains `Not` (the pattern `normalize_negations` transforms).
    ///
    /// Production callers use `scan_features().has_negation` instead (#6360).
    /// Retained for test assertions.
    #[cfg(test)]
    pub(crate) fn contains_negation(&self) -> bool {
        self.contains_op_matching(&|op| matches!(op, ChcOp::Not))
    }

    /// Check if expression contains strict integer comparisons (`<` or `>`),
    /// which `normalize_strict_int_comparisons` rewrites to `<=`/`>=`.
    ///
    /// Production callers use `scan_features().has_strict_int_comparison`
    /// instead (#6360). Retained for test assertions.
    #[cfg(test)]
    pub(crate) fn contains_strict_int_comparison(&self) -> bool {
        self.contains_op_matching(&|op| matches!(op, ChcOp::Lt | ChcOp::Gt))
    }

    /// Check if expression contains mixed-sort equalities `(= Int Bool)` or `(= Bool Int)`.
    ///
    /// These are created by CHC benchmarks with patterns like `(= D (= E 0))` where D is Int
    /// and `(= E 0)` has sort Bool. The LRA solver cannot handle Bool sub-expressions in
    /// arithmetic atoms, marking them as unsupported and causing Unknown results (#5925, #6167).
    pub(crate) fn contains_mixed_sort_eq(&self) -> bool {
        fn inner(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true; // Conservative: assume mixed-sort if too deep
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_) => false,
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    let s0 = args[0].sort();
                    let s1 = args[1].sort();
                    let is_mixed = (s0 == ChcSort::Bool) != (s1 == ChcSort::Bool)
                        && (matches!(s0, ChcSort::Int | ChcSort::Real)
                            || matches!(s1, ChcSort::Int | ChcSort::Real));
                    is_mixed || args.iter().any(|a| inner(a, depth + 1))
                }
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    args.iter().any(|a| inner(a, depth + 1))
                }
                ChcExpr::Op(_, args) => args.iter().any(|a| inner(a, depth + 1)),
                ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => false,
                ChcExpr::ConstArray(_ks, val) => inner(val, depth + 1),
            })
        }

        inner(self, 0)
    }

    /// Extract a simple `(= var const)` or `(= const var)` equality from a single expression.
    ///
    /// Returns `Some((variable, constant))` if the expression is exactly a variable-integer
    /// equality. This is the canonical implementation — use it instead of per-file copies.
    pub(crate) fn extract_var_int_equality(&self) -> Option<(ChcVar, i64)> {
        match self {
            Self::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (Self::Var(v), Self::Int(n)) | (Self::Int(n), Self::Var(v)) => {
                        Some((v.clone(), *n))
                    }
                    // BV constants: treat as integers for relational generalization.
                    (Self::Var(v), Self::BitVec(val, _)) | (Self::BitVec(val, _), Self::Var(v)) => {
                        i64::try_from(*val).ok().map(|n| (v.clone(), n))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Check if expression tree contains a variable with the given name.
    ///
    /// This is the single canonical implementation; callers in mbp, parity,
    /// and lemma_cluster should delegate here instead of maintaining copies.
    pub(crate) fn contains_var_name(&self, name: &str) -> bool {
        fn inner(expr: &ChcExpr, name: &str, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true;
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Var(v) => v.name == name,
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _) => false,
                ChcExpr::Op(_, args)
                | ChcExpr::PredicateApp(_, _, args)
                | ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| inner(a, name, depth + 1)),
                ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => false,
                ChcExpr::ConstArray(_ks, val) => inner(val, name, depth + 1),
            })
        }
        inner(self, name, 0)
    }
}
