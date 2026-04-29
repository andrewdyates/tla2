// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CHC problem construction and solver dispatch
//!
//! Contains the non-trait `impl ChcTranslator` methods: constructor,
//! clause building (Init/Next/Safety), and PDR solver invocation.

use std::collections::HashMap;

use tla_core::ast::Expr;
use tla_core::{dispatch_translate_bool, Spanned};
use z4_chc::{ChcEngineResult, ChcExpr, ClauseBody, ClauseHead, HornClause, PdrConfig};

use super::result::{format_counterexample, format_invariant, PdrCheckResult};
use super::support::{and_all, domain_key_to_var_suffix, normalize_domain_key, tla_sort_to_chc};
use super::{ChcFuncVarInfo, ChcRecordVarInfo, ChcTranslator};
use crate::error::{Z4Error, Z4Result};
use crate::TlaSort;

impl ChcTranslator {
    /// Create a new CHC translator for the given state variables
    ///
    /// # Arguments
    /// * `state_vars` - List of (name, sort) pairs for state variables
    ///
    /// # Example
    /// ```no_run
    /// use tla_z4::chc::ChcTranslator;
    /// use tla_z4::TlaSort;
    ///
    /// let trans = ChcTranslator::new(&[
    ///     ("x", TlaSort::Int),
    ///     ("y", TlaSort::Bool),
    /// ]).unwrap();
    /// ```
    pub fn new(state_vars: &[(&str, TlaSort)]) -> Z4Result<Self> {
        let mut problem = z4_chc::ChcProblem::new();

        // Build the invariant predicate signature
        let mut inv_sorts = Vec::new();
        for (_, sort) in state_vars {
            let sort = sort.clone().canonicalized();
            match &sort {
                TlaSort::Function { domain_keys, range } => {
                    let range_sort = tla_sort_to_chc(range)?;
                    inv_sorts.extend(std::iter::repeat_n(range_sort, domain_keys.len()));
                }
                TlaSort::Record { field_sorts } => {
                    for (_, field_sort) in field_sorts {
                        inv_sorts.push(tla_sort_to_chc(field_sort)?);
                    }
                }
                _ => inv_sorts.push(tla_sort_to_chc(&sort)?),
            }
        }

        let inv_pred = problem.declare_predicate("Inv", inv_sorts);

        // Create variable mappings and flatten finite-domain function state
        // into the invariant predicate's argument list in declaration order.
        let mut vars = HashMap::new();
        let mut next_vars = HashMap::new();
        let mut var_sorts = HashMap::new();
        let mut func_vars = HashMap::new();
        let mut record_vars = HashMap::new();
        let mut pred_vars = Vec::new();
        let mut pred_next_vars = Vec::new();

        for (name, sort) in state_vars {
            let sort = sort.clone().canonicalized();
            match &sort {
                TlaSort::Function { domain_keys, range } => {
                    let normalized_keys: Vec<String> = domain_keys
                        .iter()
                        .map(|key| normalize_domain_key(key))
                        .collect();
                    let chc_sort = tla_sort_to_chc(range)?;
                    let mut element_vars = HashMap::new();
                    let mut element_next_vars = HashMap::new();

                    for key in &normalized_keys {
                        let elem_name = format!("{name}__{}", domain_key_to_var_suffix(key));
                        let elem_var = z4_chc::ChcVar::new(&elem_name, chc_sort.clone());
                        let elem_next_var = elem_var.primed();

                        pred_vars.push(elem_var.clone());
                        pred_next_vars.push(elem_next_var.clone());
                        element_vars.insert(key.clone(), elem_var);
                        element_next_vars.insert(key.clone(), elem_next_var);
                    }

                    func_vars.insert(
                        (*name).to_string(),
                        ChcFuncVarInfo {
                            domain_keys: normalized_keys.clone(),
                            range_sort: (**range).clone(),
                            element_vars,
                            element_next_vars,
                        },
                    );
                    var_sorts.insert(
                        name.to_string(),
                        TlaSort::Function {
                            domain_keys: normalized_keys,
                            range: range.clone(),
                        },
                    );
                }
                TlaSort::Record { field_sorts } => {
                    let mut field_vars = HashMap::new();
                    let mut field_next_vars = HashMap::new();

                    for (field_name, field_sort) in field_sorts {
                        let chc_sort = tla_sort_to_chc(field_sort)?;
                        let field_var = z4_chc::ChcVar::new(
                            &format!(
                                "{name}__{}",
                                domain_key_to_var_suffix(&format!("field:{field_name}"))
                            ),
                            chc_sort.clone(),
                        );
                        let field_next_var = field_var.primed();

                        pred_vars.push(field_var.clone());
                        pred_next_vars.push(field_next_var.clone());
                        field_vars.insert(field_name.clone(), field_var);
                        field_next_vars.insert(field_name.clone(), field_next_var);
                    }

                    record_vars.insert(
                        (*name).to_string(),
                        ChcRecordVarInfo {
                            field_sorts: field_sorts.clone(),
                            field_vars,
                            field_next_vars,
                        },
                    );
                    var_sorts.insert(name.to_string(), sort.clone());
                }
                _ => {
                    let chc_sort = tla_sort_to_chc(&sort)?;
                    let var = z4_chc::ChcVar::new(*name, chc_sort.clone());
                    let next_var = var.primed();

                    pred_vars.push(var.clone());
                    pred_next_vars.push(next_var.clone());
                    vars.insert(name.to_string(), var);
                    next_vars.insert(name.to_string(), next_var);
                    var_sorts.insert(name.to_string(), sort.clone());
                }
            }
        }

        Ok(Self {
            problem,
            inv_pred,
            vars,
            next_vars,
            func_vars,
            record_vars,
            pred_vars,
            pred_next_vars,
            var_sorts,
            atom_intern: HashMap::new(),
            allow_primed: false,
            use_primed_vars: false,
        })
    }

    /// Add the initiation clause: Init(vars) => Inv(vars)
    ///
    /// Translates the TLA+ Init predicate to a CHC clause that establishes
    /// the invariant holds for all initial states.
    pub fn add_init(&mut self, init_expr: &Spanned<Expr>) -> Z4Result<()> {
        self.allow_primed = false;
        self.use_primed_vars = false;
        let init_chc = dispatch_translate_bool(self, init_expr)?;

        // Get invariant arguments in declaration order (NOT HashMap iteration order)
        let inv_args = self.current_state_args();

        // Init(vars) => Inv(vars)
        let clause = HornClause::new(
            ClauseBody::constraint(init_chc),
            ClauseHead::Predicate(self.inv_pred, inv_args),
        );

        self.problem.add_clause(clause);
        Ok(())
    }

    /// Add the consecution clause: Inv(vars) ∧ Next(vars,vars') => Inv(vars')
    ///
    /// Translates the TLA+ Next relation to a CHC clause that ensures
    /// the invariant is preserved by transitions.
    pub fn add_next(&mut self, next_expr: &Spanned<Expr>) -> Z4Result<()> {
        self.allow_primed = true;
        self.use_primed_vars = false;
        let next_chc = dispatch_translate_bool(self, next_expr)?;

        // Current state args for Inv(vars) in body (declaration order)
        let curr_args = self.current_state_args();

        // Next state args for Inv(vars') in head (declaration order)
        let next_args = self.next_state_args();

        // Inv(vars) ∧ Next(vars,vars') => Inv(vars')
        let clause = HornClause::new(
            ClauseBody::new(vec![(self.inv_pred, curr_args)], Some(next_chc)),
            ClauseHead::Predicate(self.inv_pred, next_args),
        );

        self.problem.add_clause(clause);
        Ok(())
    }

    /// Add the query clause: Inv(vars) ∧ ¬Safety(vars) => false
    ///
    /// Translates the TLA+ safety property (invariant) to a CHC query.
    /// If PDR can prove this clause unsatisfiable, the property holds.
    pub fn add_safety(&mut self, safety_expr: &Spanned<Expr>) -> Z4Result<()> {
        self.allow_primed = false;
        self.use_primed_vars = false;
        let safety_chc = dispatch_translate_bool(self, safety_expr)?;

        // Current state args for Inv(vars) in body (declaration order)
        let curr_args = self.current_state_args();

        // Inv(vars) ∧ ¬Safety(vars) => false
        let clause = HornClause::new(
            ClauseBody::new(
                vec![(self.inv_pred, curr_args)],
                Some(ChcExpr::not(safety_chc)),
            ),
            ClauseHead::False,
        );

        self.problem.add_clause(clause);
        Ok(())
    }

    /// Get current state variables as CHC expressions in declaration order
    pub(super) fn current_state_args(&self) -> Vec<ChcExpr> {
        self.pred_vars.iter().cloned().map(ChcExpr::var).collect()
    }

    /// Get next state variables as CHC expressions in declaration order
    pub(super) fn next_state_args(&self) -> Vec<ChcExpr> {
        self.pred_next_vars
            .iter()
            .cloned()
            .map(ChcExpr::var)
            .collect()
    }

    /// Get the built CHC problem
    pub fn into_problem(self) -> z4_chc::ChcProblem {
        self.problem
    }

    /// Run PDR solver with default configuration and return result
    pub fn solve_pdr_default(self) -> Z4Result<PdrCheckResult> {
        self.solve_pdr(PdrConfig::default())
    }

    /// Run CHC solver with custom PDR configuration and return result.
    ///
    /// Uses the portfolio solver (PDR + BMC + KIND cross-validation) instead
    /// of bare PDR to avoid false Safe results from PDR soundness bugs.
    pub fn solve_pdr(self, config: PdrConfig) -> Z4Result<PdrCheckResult> {
        let portfolio_config = z4_chc::PortfolioConfig::default().timeout(config.solve_timeout);
        let solver = z4_chc::testing::new_portfolio_solver(self.problem, portfolio_config);
        let result = solver.solve();

        match result {
            ChcEngineResult::Safe(inv_model) => Ok(PdrCheckResult::Safe {
                invariant: format_invariant(&inv_model),
            }),
            ChcEngineResult::Unsafe(cex) => Ok(PdrCheckResult::Unsafe {
                trace: format_counterexample(&cex),
            }),
            ChcEngineResult::Unknown | ChcEngineResult::NotApplicable => {
                Ok(PdrCheckResult::Unknown {
                    reason: "solver reached resource limits or is not applicable".to_string(),
                })
            }
            _ => Ok(PdrCheckResult::Unknown {
                reason: "Unrecognized solver result variant".to_string(),
            }),
        }
    }

    /// Translate UNCHANGED expression for CHC
    pub(super) fn translate_unchanged_chc(&self, var_expr: &Spanned<Expr>) -> Z4Result<ChcExpr> {
        match &var_expr.node {
            Expr::StateVar(name, _, _) | Expr::Ident(name, _) => {
                if let Some(info) = self.func_vars.get(name) {
                    let mut eqs = Vec::with_capacity(info.domain_keys.len());
                    for key in &info.domain_keys {
                        let curr = info
                            .element_vars
                            .get(key)
                            .ok_or_else(|| Z4Error::UnknownVariable(format!("{name}[{key}]")))?;
                        let next = info
                            .element_next_vars
                            .get(key)
                            .ok_or_else(|| Z4Error::UnknownVariable(format!("{name}'[{key}]")))?;
                        eqs.push(ChcExpr::eq(
                            ChcExpr::var(next.clone()),
                            ChcExpr::var(curr.clone()),
                        ));
                    }
                    Ok(and_all(eqs))
                } else if let Some(info) = self.record_vars.get(name) {
                    let mut eqs = Vec::with_capacity(info.field_sorts.len());
                    for (field_name, _) in &info.field_sorts {
                        let curr = info.field_vars.get(field_name).ok_or_else(|| {
                            Z4Error::UnknownVariable(format!("{name}.{field_name}"))
                        })?;
                        let next = info.field_next_vars.get(field_name).ok_or_else(|| {
                            Z4Error::UnknownVariable(format!("{name}'.{field_name}"))
                        })?;
                        eqs.push(ChcExpr::eq(
                            ChcExpr::var(next.clone()),
                            ChcExpr::var(curr.clone()),
                        ));
                    }
                    Ok(and_all(eqs))
                } else if let (Some(curr), Some(next)) =
                    (self.vars.get(name), self.next_vars.get(name))
                {
                    Ok(ChcExpr::eq(
                        ChcExpr::var(next.clone()),
                        ChcExpr::var(curr.clone()),
                    ))
                } else {
                    Err(Z4Error::UnknownVariable(name.clone()))
                }
            }
            Expr::Tuple(vars) => {
                let mut eqs = Vec::new();
                for var_item in vars {
                    if matches!(&var_item.node, Expr::StateVar(..) | Expr::Ident(..)) {
                        eqs.push(self.translate_unchanged_chc(var_item)?);
                    } else {
                        return Err(Z4Error::UntranslatableExpr(
                            "UNCHANGED tuple elements must be state variables".to_string(),
                        ));
                    }
                }
                Ok(and_all(eqs))
            }
            _ => Err(Z4Error::UntranslatableExpr(
                "UNCHANGED requires state variable or tuple of state variables".to_string(),
            )),
        }
    }
}
