// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cube extraction from SMT models.
//!
//! Functions for building cubes (conjunctive state descriptions) from SMT
//! solver models. Extracted from core.rs for file size management.
//!
//! Submodules:
//! - `mbp`: Model-based projection (MBP) cube extraction strategies.

use super::{cube, Arc, ChcExpr, ChcSort, ChcVar, FxHashMap, PdrSolver, PredicateId, SmtValue};

mod mbp;

impl PdrSolver {
    /// Build a concrete cube over canonical vars for a predicate, using `model` values for `args`.
    /// Array-sorted variables generate `select(arr, idx) = val` constraints from model entries.
    pub(in crate::pdr::solver) fn cube_from_model(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }

        let mut conjuncts = Vec::with_capacity(args.len());
        for (canon, arg) in vars.iter().zip(args.iter()) {
            if matches!(canon.sort, ChcSort::Array(_, _)) {
                let array_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(select_conjuncts) =
                    Self::array_select_constraints_from_model(canon, array_model_val)
                {
                    conjuncts.extend(select_conjuncts);
                }
                continue;
            }
            if matches!(canon.sort, ChcSort::Datatype { .. }) {
                let dt_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(dt_conjuncts) = Self::dt_constraints_from_model(canon, dt_model_val) {
                    conjuncts.extend(dt_conjuncts);
                }
                continue;
            }
            let value = cube::value_expr_from_model(arg, model)?;
            match (&canon.sort, value) {
                (ChcSort::Bool, ChcExpr::Bool(true)) => conjuncts.push(ChcExpr::var(canon.clone())),
                (ChcSort::Bool, ChcExpr::Bool(false)) => {
                    conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                }
                (_, v) => conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), v)),
            }
        }
        if conjuncts.is_empty() {
            return None;
        }
        Some(ChcExpr::and_all(conjuncts))
    }

    /// #6047: Convert an array model value to constraints over array contents.
    pub(in crate::pdr) fn array_select_constraints_from_model(
        canon: &ChcVar,
        model_val: Option<&SmtValue>,
    ) -> Option<Vec<ChcExpr>> {
        let ChcSort::Array(ref idx_sort, ref val_sort) = canon.sort else {
            return None;
        };
        let model_val = model_val?;
        match model_val {
            SmtValue::ConstArray(default) => {
                let default_expr = Self::smt_value_to_scalar_expr(default, val_sort)?;
                let const_arr = ChcExpr::ConstArray(*idx_sort.clone(), Arc::new(default_expr));
                Some(vec![ChcExpr::eq(ChcExpr::var(canon.clone()), const_arr)])
            }
            SmtValue::ArrayMap {
                default, entries, ..
            } => {
                if entries.is_empty() {
                    let default_expr = Self::smt_value_to_scalar_expr(default, val_sort)?;
                    let const_arr = ChcExpr::ConstArray(*idx_sort.clone(), Arc::new(default_expr));
                    return Some(vec![ChcExpr::eq(ChcExpr::var(canon.clone()), const_arr)]);
                }
                let mut conjuncts = Vec::with_capacity(entries.len());
                for (idx_val, elem_val) in entries {
                    let idx_expr = Self::smt_value_to_scalar_expr(idx_val, idx_sort)?;
                    let val_expr = Self::smt_value_to_scalar_expr(elem_val, val_sort)?;
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::select(ChcExpr::var(canon.clone()), idx_expr),
                        val_expr,
                    ));
                }
                Some(conjuncts)
            }
            _ => None,
        }
    }

    fn smt_value_to_scalar_expr(val: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
        match (val, sort) {
            (SmtValue::Int(n), ChcSort::Int | ChcSort::Real) => Some(ChcExpr::int(*n)),
            (SmtValue::Real(r), ChcSort::Real) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64().unwrap_or(0);
                let d = r.denom().to_i64().unwrap_or(1);
                Some(ChcExpr::Real(n, d))
            }
            (SmtValue::Bool(b), ChcSort::Bool) => Some(ChcExpr::Bool(*b)),
            (SmtValue::BitVec(v, w), ChcSort::BitVec(_)) => Some(ChcExpr::BitVec(*v, *w)),
            _ => None,
        }
    }

    fn dt_constraints_from_model(
        canon: &ChcVar,
        model_val: Option<&SmtValue>,
    ) -> Option<Vec<ChcExpr>> {
        let model_val = model_val?;
        match model_val {
            SmtValue::Datatype(ctor, fields) => {
                let field_exprs: Vec<Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_any_expr(f).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?;
                let ctor_app = ChcExpr::FuncApp(ctor.clone(), canon.sort.clone(), field_exprs);
                Some(vec![ChcExpr::eq(ChcExpr::var(canon.clone()), ctor_app)])
            }
            SmtValue::Opaque(name) => {
                let ctor_app = ChcExpr::FuncApp(name.clone(), canon.sort.clone(), vec![]);
                Some(vec![ChcExpr::eq(ChcExpr::var(canon.clone()), ctor_app)])
            }
            _ => None,
        }
    }

    fn smt_value_to_any_expr(val: &SmtValue) -> Option<ChcExpr> {
        match val {
            SmtValue::Int(n) => Some(ChcExpr::int(*n)),
            SmtValue::Bool(b) => Some(ChcExpr::Bool(*b)),
            SmtValue::BitVec(v, w) => Some(ChcExpr::BitVec(*v, *w)),
            SmtValue::Real(r) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64().unwrap_or(0);
                let d = r.denom().to_i64().unwrap_or(1);
                Some(ChcExpr::Real(n, d))
            }
            SmtValue::Datatype(ctor, fields) => {
                let field_exprs: Vec<Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_any_expr(f).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?;
                Some(ChcExpr::FuncApp(
                    ctor.clone(),
                    ChcSort::Uninterpreted(ctor.clone()),
                    field_exprs,
                ))
            }
            SmtValue::Opaque(name) => Some(ChcExpr::FuncApp(
                name.clone(),
                ChcSort::Uninterpreted(name.clone()),
                vec![],
            )),
            _ => None,
        }
    }

    /// Extract a cube, prioritizing constraint extraction when model is empty.
    pub(in crate::pdr::solver) fn cube_from_model_or_constraints(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let mut augmented = model.clone();
        cube::augment_model_from_equalities(constraint, &mut augmented);
        self.cube_from_model(pred, args, &augmented)
            .or_else(|| self.cube_from_equalities(pred, args, constraint))
            .or_else(|| self.cube_from_model_partial(pred, args, &augmented))
    }

    /// Build a best-effort partial cube, skipping variables that can't be evaluated.
    pub(super) fn cube_from_model_partial(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let mut conjuncts = Vec::with_capacity(args.len());
        for (canon, arg) in vars.iter().zip(args.iter()) {
            if matches!(canon.sort, ChcSort::Array(_, _)) {
                let array_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(select_conjuncts) =
                    Self::array_select_constraints_from_model(canon, array_model_val)
                {
                    conjuncts.extend(select_conjuncts);
                }
                continue;
            }
            if matches!(canon.sort, ChcSort::Datatype { .. }) {
                let dt_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(dt_conjuncts) = Self::dt_constraints_from_model(canon, dt_model_val) {
                    conjuncts.extend(dt_conjuncts);
                }
                continue;
            }
            let value = match cube::value_expr_from_model(arg, model) {
                Some(v) => v,
                None => continue,
            };
            match (&canon.sort, value) {
                (ChcSort::Bool, ChcExpr::Bool(true)) => conjuncts.push(ChcExpr::var(canon.clone())),
                (ChcSort::Bool, ChcExpr::Bool(false)) => {
                    conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                }
                (_, v) => conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), v)),
            }
        }
        if conjuncts.is_empty() {
            return None;
        }
        Some(ChcExpr::and_all(conjuncts))
    }

    /// Compute a predecessor cube using MBP (unified entry point).
    pub(in crate::pdr::solver) fn cube_with_mbp(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let point_cube = self.cube_from_model_or_constraints(pred, args, constraint, model);
        if model.is_empty() || !self.config.use_mbp {
            return point_cube;
        }
        let Some(inputs) = self.prepare_cube_mbp_inputs(pred, args, constraint, model) else {
            return point_cube;
        };
        if !Self::should_attempt_cube_mbp(&inputs) {
            return point_cube;
        }
        let mbp_cube = self.cube_from_model_mbp_with_inputs(pred, args, constraint, model, inputs);
        mbp_cube.or(point_cube)
    }

    /// Extract a cube from equality constraints in a formula.
    pub(in crate::pdr::solver) fn cube_from_equalities(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let var_values = cube::extract_equalities_and_propagate(constraint);
        let expr_model: FxHashMap<String, SmtValue> = var_values
            .iter()
            .map(|(name, value): (&String, &i64)| (name.clone(), SmtValue::Int(*value)))
            .collect();
        let mut conjuncts = Vec::with_capacity(args.len());
        for (canon, arg) in vars.iter().zip(args.iter()) {
            if matches!(canon.sort, ChcSort::Array(_, _) | ChcSort::Datatype { .. }) {
                continue;
            }
            match arg {
                ChcExpr::Var(v) => {
                    if let Some(&value) = var_values.get(&v.name) {
                        conjuncts.push(ChcExpr::eq(
                            ChcExpr::var(canon.clone()),
                            ChcExpr::int(value),
                        ));
                    } else {
                        return None;
                    }
                }
                ChcExpr::Int(n) => {
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(*n)));
                }
                ChcExpr::Bool(b) => {
                    if *b {
                        conjuncts.push(ChcExpr::var(canon.clone()));
                    } else {
                        conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                    }
                }
                expr => {
                    let value = crate::expr::evaluate_expr(expr, &expr_model)?;
                    match (&canon.sort, value) {
                        (ChcSort::Int, SmtValue::Int(n)) => {
                            conjuncts
                                .push(ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(n)));
                        }
                        (ChcSort::Bool, SmtValue::Bool(true)) => {
                            conjuncts.push(ChcExpr::var(canon.clone()));
                        }
                        (ChcSort::Bool, SmtValue::Bool(false)) => {
                            conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                        }
                        _ => return None,
                    }
                }
            }
        }
        Some(ChcExpr::and_all(conjuncts))
    }

    #[cfg(test)]
    pub(in crate::pdr::solver) fn extract_integer_only_cube(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let mut conjuncts = Vec::new();
        for (canon, arg) in vars.iter().zip(args.iter()) {
            if matches!(canon.sort, ChcSort::Array(_, _)) {
                continue;
            }
            match arg {
                ChcExpr::Var(v) => {
                    if matches!(v.sort, ChcSort::Array(_, _)) {
                        continue;
                    }
                    if let Some(SmtValue::Int(value)) = model.get(&v.name) {
                        conjuncts.push(ChcExpr::eq(
                            ChcExpr::var(canon.clone()),
                            ChcExpr::int(*value),
                        ));
                    } else if let Some(SmtValue::Bool(value)) = model.get(&v.name) {
                        if *value {
                            conjuncts.push(ChcExpr::var(canon.clone()));
                        } else {
                            conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                        }
                    } else {
                        return None;
                    }
                }
                ChcExpr::Int(n) => {
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(*n)));
                }
                ChcExpr::Bool(b) => {
                    if *b {
                        conjuncts.push(ChcExpr::var(canon.clone()));
                    } else {
                        conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                    }
                }
                _ => {
                    if let Some(v) = cube::value_expr_from_model(arg, model) {
                        match v {
                            ChcExpr::Int(n) => {
                                conjuncts.push(ChcExpr::eq(
                                    ChcExpr::var(canon.clone()),
                                    ChcExpr::int(n),
                                ));
                            }
                            ChcExpr::Bool(b) => {
                                if b {
                                    conjuncts.push(ChcExpr::var(canon.clone()));
                                } else {
                                    conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                                }
                            }
                            _ => return None,
                        }
                    } else {
                        return None;
                    }
                }
            }
        }
        if conjuncts.is_empty() {
            Some(ChcExpr::Bool(true))
        } else {
            Some(ChcExpr::and_all(conjuncts))
        }
    }

    /// Extract equalities from a formula and populate an SMT model.
    pub(in crate::pdr) fn extract_equalities_from_formula(
        expr: &ChcExpr,
        model: &mut FxHashMap<String, SmtValue>,
    ) {
        let int_values = cube::extract_equalities_and_propagate(expr);
        for (name, value) in int_values {
            model.insert(name, SmtValue::Int(value));
        }
    }
}
