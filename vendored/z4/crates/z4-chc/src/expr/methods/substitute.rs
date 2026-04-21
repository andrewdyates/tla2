// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression tree rewriting: substitution, renaming, and disequality replacement.

use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcVar, MAX_EXPR_RECURSION_DEPTH,
    MAX_PREPROCESSING_NODES,
};

impl ChcExpr {
    /// Rebuild this expression by applying a transform to each direct child node.
    pub(crate) fn map_children_with<F>(&self, mut map_child: F) -> Self
    where
        F: FnMut(&Self) -> Self,
    {
        match self {
            Self::Bool(_)
            | Self::Int(_)
            | Self::Real(_, _)
            | Self::BitVec(_, _)
            | Self::Var(_)
            | Self::ConstArrayMarker(_)
            | Self::IsTesterMarker(_) => self.clone(),
            Self::Op(op, args) => Self::Op(
                op.clone(),
                args.iter().map(|arg| Arc::new(map_child(arg))).collect(),
            ),
            Self::PredicateApp(name, id, args) => Self::PredicateApp(
                name.clone(),
                *id,
                args.iter().map(|arg| Arc::new(map_child(arg))).collect(),
            ),
            Self::FuncApp(name, sort, args) => Self::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter().map(|arg| Arc::new(map_child(arg))).collect(),
            ),
            Self::ConstArray(ks, val) => Self::ConstArray(ks.clone(), Arc::new(map_child(val))),
        }
    }

    /// Substitute variables in the expression
    pub fn substitute(&self, subst: &[(ChcVar, Self)]) -> Self {
        if subst.is_empty() {
            return self.clone();
        }
        let map: FxHashMap<&ChcVar, &Self> = subst.iter().map(|(v, e)| (v, e)).collect();
        self.substitute_map(&map)
    }

    /// Substitute variables using a pre-built map (O(1) lookup per variable).
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn substitute_map(&self, map: &FxHashMap<&ChcVar, &Self>) -> Self {
        self.substitute_with_lookup(&|v| map.get(v).map(|e| (*e).clone()))
    }

    /// Substitute variables by variable name (O(1) lookup per variable name).
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn substitute_name_map(&self, map: &FxHashMap<String, Self>) -> Self {
        if map.is_empty() {
            return self.clone();
        }
        self.substitute_with_lookup(&|v| map.get(&v.name).cloned())
    }

    /// Rename variables by name, preserving sorts (#3577).
    /// Maps old variable names to new variable names. Variables not in the map
    /// are left unchanged. If the expression tree exceeds 1M nodes, returns
    /// `self` unchanged.
    pub(crate) fn rename_vars(&self, map: &FxHashMap<String, String>) -> Self {
        if map.is_empty() {
            return self.clone();
        }
        self.substitute_with_lookup(&|v| {
            map.get(&v.name)
                .map(|new_name| Self::var(ChcVar::new(new_name, v.sort.clone())))
        })
    }

    /// Substitute sub-expressions by structural equality (#3577).
    /// Each `(from, to)` pair replaces occurrences of `from` with `to`.
    /// Matching is checked at each node before recursing into children.
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged.
    pub(crate) fn substitute_expr_pairs(&self, pairs: &[(Self, Self)]) -> Self {
        if pairs.is_empty() {
            return self.clone();
        }
        use std::cell::Cell;
        let budget = Cell::new(MAX_PREPROCESSING_NODES);
        Self::subst_expr_inner(self, &budget, 0, pairs).unwrap_or_else(|| self.clone())
    }

    fn subst_expr_inner(
        expr: &Self,
        budget: &std::cell::Cell<usize>,
        depth: usize,
        pairs: &[(Self, Self)],
    ) -> Option<Self> {
        maybe_grow_expr_stack(|| {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return None;
            }
            let remaining = budget.get();
            if remaining == 0 {
                return None;
            }
            budget.set(remaining - 1);

            // Check whole-expression matches before recursing
            for (from, to) in pairs {
                if expr == from {
                    return Some(to.clone());
                }
            }

            Some(match expr {
                Self::Bool(_)
                | Self::Int(_)
                | Self::Real(_, _)
                | Self::BitVec(_, _)
                | Self::Var(_) => expr.clone(),
                Self::Op(op, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(
                                Self::subst_expr_inner(a, budget, depth + 1, pairs)
                                    .unwrap_or_else(|| a.as_ref().clone()),
                            )
                        })
                        .collect();
                    Self::Op(op.clone(), new_args)
                }
                Self::PredicateApp(name, id, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(
                                Self::subst_expr_inner(a, budget, depth + 1, pairs)
                                    .unwrap_or_else(|| a.as_ref().clone()),
                            )
                        })
                        .collect();
                    Self::PredicateApp(name.clone(), *id, new_args)
                }
                Self::FuncApp(name, sort, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(
                                Self::subst_expr_inner(a, budget, depth + 1, pairs)
                                    .unwrap_or_else(|| a.as_ref().clone()),
                            )
                        })
                        .collect();
                    Self::FuncApp(name.clone(), sort.clone(), new_args)
                }
                Self::ConstArrayMarker(_) | Self::IsTesterMarker(_) => expr.clone(),
                Self::ConstArray(ks, val) => Self::ConstArray(
                    ks.clone(),
                    Arc::new(
                        Self::subst_expr_inner(val, budget, depth + 1, pairs)
                            .unwrap_or_else(|| val.as_ref().clone()),
                    ),
                ),
            })
        })
    }

    pub(crate) fn substitute_with_lookup<F>(&self, lookup: &F) -> Self
    where
        F: Fn(&ChcVar) -> Option<Self>,
    {
        use std::cell::Cell;
        let budget = Cell::new(MAX_PREPROCESSING_NODES);
        Self::subst_inner(self, &budget, 0, lookup).unwrap_or_else(|| self.clone())
    }

    fn subst_inner<F>(
        expr: &Self,
        budget: &std::cell::Cell<usize>,
        depth: usize,
        lookup: &F,
    ) -> Option<Self>
    where
        F: Fn(&ChcVar) -> Option<Self>,
    {
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
                Self::Var(v) => lookup(v).unwrap_or_else(|| expr.clone()),
                _ => expr.map_children_with(|child| {
                    Self::subst_inner(child, budget, depth + 1, lookup)
                        .unwrap_or_else(|| child.clone())
                }),
            })
        })
    }

    /// Replace a disequality (not (= lhs rhs)) with a replacement expression.
    ///
    /// This is used for disequality splitting: (not (= a b)) -> (< a b) or (> a b).
    pub(crate) fn replace_diseq(
        &self,
        target_lhs: &Self,
        target_rhs: &Self,
        replacement: Self,
    ) -> Self {
        fn replace_diseq_inner(
            expr: &ChcExpr,
            depth: usize,
            target_lhs: &ChcExpr,
            target_rhs: &ChcExpr,
            replacement: &ChcExpr,
        ) -> ChcExpr {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return expr.clone();
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                        if eq_args.len() == 2 {
                            let lhs = &*eq_args[0];
                            let rhs = &*eq_args[1];
                            if (lhs == target_lhs && rhs == target_rhs)
                                || (lhs == target_rhs && rhs == target_lhs)
                            {
                                return replacement.clone();
                            }
                        }
                    }
                    ChcExpr::Op(
                        ChcOp::Not,
                        vec![Arc::new(replace_diseq_inner(
                            args[0].as_ref(),
                            depth + 1,
                            target_lhs,
                            target_rhs,
                            replacement,
                        ))],
                    )
                }
                ChcExpr::Op(op, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(replace_diseq_inner(
                                a.as_ref(),
                                depth + 1,
                                target_lhs,
                                target_rhs,
                                replacement,
                            ))
                        })
                        .collect();
                    ChcExpr::Op(op.clone(), new_args)
                }
                _ => expr.clone(),
            })
        }

        replace_diseq_inner(self, 0, target_lhs, target_rhs, &replacement)
    }
}
