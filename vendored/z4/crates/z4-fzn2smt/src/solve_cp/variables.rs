// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// FlatZinc variable and parameter registration for the CP context.

use anyhow::{bail, Result};
use z4_cp::variable::IntVarId;
use z4_cp::Domain;
use z4_flatzinc_parser::ast::*;

use super::{CpContext, CpOutputVar};

impl CpContext {
    pub(super) fn register_parameter(&mut self, par: &ParDecl) {
        match &par.ty {
            FznType::Bool => {
                if let Expr::Bool(b) = &par.value {
                    self.par_ints.insert(par.id.clone(), i64::from(*b));
                }
            }
            FznType::Int | FznType::IntRange(..) | FznType::IntSet(_) => {
                if let Some(v) = self.eval_const_int(&par.value) {
                    self.par_ints.insert(par.id.clone(), v);
                }
            }
            FznType::SetOfInt | FznType::SetOfIntRange(..) | FznType::SetOfIntSet(_) => {
                self.par_sets.insert(par.id.clone(), par.value.clone());
            }
            FznType::ArrayOf { elem, .. } => {
                self.register_array_parameter(par, elem);
            }
            _ => {}
        }
    }

    fn register_array_parameter(&mut self, par: &ParDecl, elem: &FznType) {
        let elems = match &par.value {
            Expr::ArrayLit(e) => e,
            _ => return,
        };
        match elem {
            FznType::Int | FznType::IntRange(..) | FznType::IntSet(_) | FznType::Bool => {
                let vals: Vec<i64> = elems
                    .iter()
                    .map(|e| self.eval_const_int(e).unwrap_or(0))
                    .collect();
                self.par_int_arrays.insert(par.id.clone(), vals);
            }
            FznType::SetOfInt | FznType::SetOfIntRange(..) | FznType::SetOfIntSet(_) => {
                let sets: Vec<Vec<i64>> = elems.iter().map(eval_set_elements).collect();
                self.par_set_arrays.insert(par.id.clone(), sets);
            }
            _ => {}
        }
    }

    pub(super) fn create_variable(&mut self, var: &VarDecl) -> Result<()> {
        let is_output = has_output_annotation(&var.annotations);
        let array_range = get_output_array_range(&var.annotations);

        match &var.ty {
            FznType::Bool => {
                let id = self.create_scalar_var(&var.id, Domain::new(0, 1), &var.value)?;
                if is_output {
                    self.push_scalar_output(&var.id, id, true);
                }
            }
            FznType::Int => {
                let domain = Domain::new(-1_000_000, 1_000_000);
                let id = self.create_scalar_var(&var.id, domain, &var.value)?;
                if is_output {
                    self.push_scalar_output(&var.id, id, false);
                }
            }
            FznType::IntRange(lo, hi) => {
                let id = self.create_scalar_var(&var.id, Domain::new(*lo, *hi), &var.value)?;
                if is_output {
                    self.push_scalar_output(&var.id, id, false);
                }
            }
            FznType::IntSet(vals) => {
                let id = self.create_scalar_var(&var.id, Domain::from_values(vals), &var.value)?;
                if is_output {
                    self.push_scalar_output(&var.id, id, false);
                }
            }
            FznType::SetOfIntRange(lo, hi) => {
                self.create_set_variable(&var.id, *lo, *hi)?;
            }
            FznType::SetOfInt => {
                // Unbounded set — use a default range
                self.create_set_variable(&var.id, 0, 100)?;
            }
            FznType::SetOfIntSet(vals) => {
                let lo = vals.iter().copied().min().unwrap_or(0);
                let hi = vals.iter().copied().max().unwrap_or(0);
                self.create_set_variable(&var.id, lo, hi)?;
            }
            FznType::ArrayOf { index, elem } => {
                if is_set_type(elem) {
                    self.create_set_array_variable(var, index, array_range)?;
                } else {
                    self.create_array_variable(var, index, elem, array_range)?;
                }
            }
            _ => {} // Float — skip silently
        }
        Ok(())
    }

    fn push_scalar_output(&mut self, name: &str, id: IntVarId, is_bool: bool) {
        self.output_vars.push(CpOutputVar {
            fzn_name: name.to_string(),
            var_ids: vec![id],
            is_array: false,
            array_range: None,
            is_bool,
            set_var_names: Vec::new(),
        });
    }

    /// Create a set variable as N boolean indicator variables.
    /// For `var set of lo..hi`, creates `hi - lo + 1` boolean vars.
    fn create_set_variable(&mut self, name: &str, lo: i64, hi: i64) -> Result<()> {
        let n = (hi - lo + 1).max(0) as usize;
        let mut indicators = Vec::with_capacity(n);
        for j in 0..n {
            let elem = lo + j as i64;
            let var_name = format!("{name}_has_{elem}");
            let id = self.engine.new_bool_var(Some(&var_name));
            self.var_bounds.insert(id, (0, 1));
            indicators.push(id);
        }
        self.set_var_map.insert(name.to_string(), (lo, indicators));
        Ok(())
    }

    /// Create an array of set variables, registering each element set var.
    fn create_set_array_variable(
        &mut self,
        var: &VarDecl,
        index: &IndexSet,
        array_output: Option<(i64, i64)>,
    ) -> Result<()> {
        let range = match index {
            IndexSet::Range(lo, hi) => (*lo, *hi),
            IndexSet::Int => (1, 1),
        };

        let elems = match &var.value {
            Some(Expr::ArrayLit(e)) => e,
            _ => return Ok(()),
        };

        let mut set_names = Vec::with_capacity(elems.len());
        for e in elems {
            if let Expr::Ident(name) = e {
                if self.set_var_map.contains_key(name) {
                    set_names.push(name.clone());
                }
            }
        }

        if let Some(out_range) = array_output {
            if !set_names.is_empty() {
                self.output_vars.push(CpOutputVar {
                    fzn_name: var.id.clone(),
                    var_ids: Vec::new(),
                    is_array: true,
                    array_range: Some(out_range),
                    is_bool: false,
                    set_var_names: set_names,
                });
            }
        }
        let _ = range;
        Ok(())
    }

    fn create_scalar_var(
        &mut self,
        name: &str,
        domain: Domain,
        value: &Option<Expr>,
    ) -> Result<IntVarId> {
        if let Some(expr) = value {
            if let Some(v) = self.eval_const_int(expr) {
                let id = self.engine.new_int_var(Domain::singleton(v), Some(name));
                self.var_map.insert(name.to_string(), id);
                self.var_bounds.insert(id, (v, v));
                return Ok(id);
            }
            if let Expr::Ident(ref_name) = expr {
                if let Some(&existing) = self.var_map.get(ref_name) {
                    self.var_map.insert(name.to_string(), existing);
                    return Ok(existing);
                }
            }
        }
        let lb = domain.lb();
        let ub = domain.ub();
        let id = self.engine.new_int_var(domain, Some(name));
        self.var_map.insert(name.to_string(), id);
        self.var_bounds.insert(id, (lb, ub));
        Ok(id)
    }

    fn create_array_variable(
        &mut self,
        var: &VarDecl,
        index: &IndexSet,
        elem: &FznType,
        array_output: Option<(i64, i64)>,
    ) -> Result<()> {
        let is_bool = matches!(elem, FznType::Bool);
        let range = match index {
            IndexSet::Range(lo, hi) => (*lo, *hi),
            IndexSet::Int => (1, 1),
        };

        let elems = match &var.value {
            Some(Expr::ArrayLit(e)) => e,
            _ => return Ok(()),
        };

        let mut ids = Vec::with_capacity(elems.len());
        for (i, e) in elems.iter().enumerate() {
            let elem_name = format!("{}_{}", var.id, range.0 as usize + i);
            let id = self.resolve_array_element(e, &elem_name)?;
            ids.push(id);
        }

        self.array_var_map.insert(var.id.clone(), ids.clone());

        if let Some(out_range) = array_output {
            self.output_vars.push(CpOutputVar {
                fzn_name: var.id.clone(),
                var_ids: ids,
                is_array: true,
                array_range: Some(out_range),
                is_bool,
                set_var_names: Vec::new(),
            });
        }
        Ok(())
    }

    fn resolve_array_element(&mut self, expr: &Expr, elem_name: &str) -> Result<IntVarId> {
        match expr {
            Expr::Ident(name) => {
                if let Some(&existing) = self.var_map.get(name) {
                    self.var_map.insert(elem_name.to_string(), existing);
                    Ok(existing)
                } else if let Some(&v) = self.par_ints.get(name) {
                    let id = self
                        .engine
                        .new_int_var(Domain::singleton(v), Some(elem_name));
                    self.var_map.insert(elem_name.to_string(), id);
                    Ok(id)
                } else {
                    bail!("unknown variable in array element: {name}")
                }
            }
            Expr::Int(n) => {
                let id = self
                    .engine
                    .new_int_var(Domain::singleton(*n), Some(elem_name));
                self.var_map.insert(elem_name.to_string(), id);
                Ok(id)
            }
            Expr::Bool(b) => {
                let val = i64::from(*b);
                let id = self
                    .engine
                    .new_int_var(Domain::singleton(val), Some(elem_name));
                self.var_map.insert(elem_name.to_string(), id);
                Ok(id)
            }
            _ => bail!("unsupported array element expression: {expr:?}"),
        }
    }
}

fn has_output_annotation(annotations: &[Annotation]) -> bool {
    annotations
        .iter()
        .any(|a| matches!(a, Annotation::Atom(s) if s == "output_var"))
}

fn is_set_type(ty: &FznType) -> bool {
    matches!(
        ty,
        FznType::SetOfInt | FznType::SetOfIntRange(..) | FznType::SetOfIntSet(..)
    )
}

/// Extract the integer elements from a constant set expression.
fn eval_set_elements(expr: &Expr) -> Vec<i64> {
    match expr {
        Expr::SetLit(elems) => elems
            .iter()
            .filter_map(|e| match e {
                Expr::Int(n) => Some(*n),
                _ => None,
            })
            .collect(),
        Expr::IntRange(lo, hi) => (*lo..=*hi).collect(),
        Expr::EmptySet => Vec::new(),
        _ => Vec::new(),
    }
}

fn get_output_array_range(annotations: &[Annotation]) -> Option<(i64, i64)> {
    for a in annotations {
        if let Annotation::Call(name, call_args) = a {
            if name == "output_array" {
                if let Some(Expr::ArrayLit(ranges)) = call_args.first() {
                    if let Some(Expr::IntRange(lo, hi)) = ranges.first() {
                        return Some((*lo, *hi));
                    }
                }
            }
        }
    }
    None
}
