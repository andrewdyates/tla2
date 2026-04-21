// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Persistent executor wrapper for repeated array-heavy CHC queries.

#![cfg_attr(not(test), allow(dead_code))]

use super::context::SmtContext;
use super::executor_adapter::{
    accept_reparsed_sat_model, detect_logic, parse_model_into, quote_symbol, sort_to_smtlib,
};
use super::types::{SmtResult, SmtValue};
use crate::pdr::model::InvariantModel;
use crate::{ChcExpr, ChcSort, ChcVar};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::time::Duration;
use z4_dpll::Executor;
use z4_frontend::{Command, ParseError};

#[derive(Debug, thiserror::Error)]
enum PersistentExecutorError {
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),
    #[error("executor error: {0}")]
    Execute(#[from] z4_dpll::ExecutorError),
    #[error("sort mismatch for persistent symbol {name}: {existing} vs {new}")]
    SortMismatch {
        name: String,
        existing: ChcSort,
        new: ChcSort,
    },
    #[error("check-sat produced no result")]
    MissingResult,
}

struct PersistentExecutorAdapter {
    exec: Executor,
    background: Option<ChcExpr>,
    background_hash: Option<u64>,
    logic: Option<String>,
    declared_vars: FxHashMap<String, ChcSort>,
    query_count: usize,
}

impl PersistentExecutorAdapter {
    fn new() -> Self {
        Self {
            exec: Executor::new(),
            background: None,
            background_hash: None,
            logic: None,
            declared_vars: FxHashMap::default(),
            query_count: 0,
        }
    }

    fn reset(&mut self) {
        *self = Self::new();
    }

    fn ensure_background(
        &mut self,
        background: &ChcExpr,
        logic: &str,
        timeout: Duration,
    ) -> Result<(), PersistentExecutorError> {
        let background_hash = expr_hash(background);
        if self.background_hash == Some(background_hash) && self.logic.as_deref() == Some(logic) {
            return Ok(());
        }

        self.reset();

        let namespace = format!("bg{background_hash}");
        let normalized = SmtContext::preprocess_incremental_assumption(background, &namespace);
        let vars = collect_unique_vars(std::slice::from_ref(&normalized));

        let mut script = String::new();
        script.push_str(&format!("(set-logic {logic})\n"));
        script.push_str("(set-option :produce-models true)\n");
        script.push_str(&format_timeout_option(timeout));
        append_var_declarations(&mut script, &vars);
        append_assertion(&mut script, &normalized);

        self.execute_script(&script)?;
        self.background = Some(background.clone());
        self.background_hash = Some(background_hash);
        self.logic = Some(logic.to_string());
        self.declared_vars = vars
            .into_iter()
            .map(|var| (var.name, var.sort))
            .collect::<FxHashMap<_, _>>();
        Ok(())
    }

    fn declare_missing_vars(&mut self, expr: &ChcExpr) -> Result<(), PersistentExecutorError> {
        let vars = collect_unique_vars(std::slice::from_ref(expr));
        let mut missing = Vec::new();

        for var in vars {
            if let Some(existing) = self.declared_vars.get(&var.name) {
                if existing != &var.sort {
                    return Err(PersistentExecutorError::SortMismatch {
                        name: var.name,
                        existing: existing.clone(),
                        new: var.sort,
                    });
                }
                continue;
            }
            missing.push(var);
        }

        if missing.is_empty() {
            return Ok(());
        }

        let mut script = String::new();
        append_var_declarations(&mut script, &missing);
        self.execute_script(&script)?;
        for var in missing {
            self.declared_vars.insert(var.name, var.sort);
        }
        Ok(())
    }

    fn execute_script(&mut self, script: &str) -> Result<(), PersistentExecutorError> {
        if script.trim().is_empty() {
            return Ok(());
        }
        let commands = z4_frontend::parse(script)?;
        self.exec.execute_all(&commands)?;
        Ok(())
    }
}

pub(crate) struct PersistentExecutorSmtContext {
    scratch: SmtContext,
    backend: PersistentExecutorAdapter,
}

impl Default for PersistentExecutorSmtContext {
    fn default() -> Self {
        Self::new()
    }
}

impl PersistentExecutorSmtContext {
    pub(crate) fn new() -> Self {
        Self {
            scratch: SmtContext::new(),
            backend: PersistentExecutorAdapter::new(),
        }
    }

    pub(crate) fn ensure_background(&mut self, background: &ChcExpr, timeout: Duration) -> bool {
        let vars = collect_unique_vars(std::slice::from_ref(background));
        let logic = detect_logic(&vars, background);
        match self.backend.ensure_background(background, logic, timeout) {
            Ok(()) => true,
            Err(error) => {
                tracing::debug!("persistent executor background setup failed: {error}");
                self.reset_backend();
                false
            }
        }
    }

    pub(crate) fn check_query(
        &mut self,
        query_delta: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: Duration,
    ) -> SmtResult {
        let Some(background) = self.backend.background.clone() else {
            return SmtResult::Unknown;
        };

        let namespace = format!("q{}", self.backend.query_count);
        let normalized_query =
            SmtContext::preprocess_incremental_assumption(query_delta, &namespace);
        let combined = ChcExpr::and(background.clone(), normalized_query.clone());
        let vars = collect_unique_vars(&[background.clone(), normalized_query.clone()]);
        let required_logic = detect_logic(&vars, &combined);

        if self.backend.logic.as_deref() != Some(required_logic) {
            if let Err(error) = self
                .backend
                .ensure_background(&background, required_logic, timeout)
            {
                tracing::debug!("persistent executor logic upgrade failed: {error}");
                self.reset_backend();
                return SmtResult::Unknown;
            }
        }

        if let Err(error) = self.backend.declare_missing_vars(&normalized_query) {
            tracing::debug!("persistent executor declaration failed: {error}");
            self.reset_backend();
            return SmtResult::Unknown;
        }

        if let Err(error) = self.backend.execute_script(&format_timeout_option(timeout)) {
            tracing::debug!("persistent executor timeout update failed: {error}");
            self.reset_backend();
            return SmtResult::Unknown;
        }

        let mut pushed = false;
        let result = (|| -> Result<SmtResult, PersistentExecutorError> {
            self.backend.exec.execute(&Command::Push(1))?;
            pushed = true;

            let mut query_script = String::new();
            append_assertion(&mut query_script, &normalized_query);
            self.backend.execute_script(&query_script)?;

            let status = self
                .backend
                .exec
                .execute(&Command::CheckSat)?
                .ok_or(PersistentExecutorError::MissingResult)?;

            match status.as_str() {
                "sat" => {
                    let model_output = self
                        .backend
                        .exec
                        .execute(&Command::GetModel)?
                        .unwrap_or_default();
                    let mut model = propagated_model.clone();
                    parse_model_into(&mut model, &model_output, &FxHashSet::default());
                    let validation_exprs = [&background, &normalized_query];
                    Ok(
                        if let Some(model) = accept_reparsed_sat_model(
                            &validation_exprs,
                            model,
                            "persistent executor",
                        ) {
                            SmtResult::Sat(model)
                        } else {
                            SmtResult::Unknown
                        },
                    )
                }
                "unsat" => Ok(SmtResult::Unsat),
                "unknown" => Ok(SmtResult::Unknown),
                other => {
                    tracing::warn!(
                        "persistent executor: unexpected result string {other:?}; treating as Unknown"
                    );
                    Ok(SmtResult::Unknown)
                }
            }
        })();

        if pushed {
            match self.backend.exec.execute(&Command::Pop(1)) {
                Ok(None) => {}
                Ok(Some(_)) => {
                    tracing::debug!("persistent executor pop produced unexpected output");
                    self.reset_backend();
                    return SmtResult::Unknown;
                }
                Err(error) => {
                    tracing::debug!("persistent executor pop failed: {error}");
                    self.reset_backend();
                    return SmtResult::Unknown;
                }
            }
        }

        match result {
            Ok(result) => {
                self.backend.query_count += 1;
                result
            }
            Err(error) => {
                tracing::debug!("persistent executor query failed: {error}");
                self.reset_backend();
                SmtResult::Unknown
            }
        }
    }

    pub(crate) fn reset_backend(&mut self) {
        self.scratch.reset();
        self.backend.reset();
    }

    #[cfg(test)]
    pub(crate) fn query_count(&self) -> usize {
        self.backend.query_count
    }
}

fn expr_hash(expr: &ChcExpr) -> u64 {
    let mut hasher = DefaultHasher::new();
    expr.hash(&mut hasher);
    hasher.finish()
}

fn collect_unique_vars(exprs: &[ChcExpr]) -> Vec<ChcVar> {
    let mut seen = FxHashSet::default();
    let mut vars = Vec::new();

    for expr in exprs {
        for var in expr.vars() {
            if seen.insert(var.clone()) {
                vars.push(var);
            }
        }
    }

    vars
}

fn format_timeout_option(timeout: Duration) -> String {
    if timeout.is_zero() {
        return String::new();
    }
    let timeout_ms = timeout.as_millis().min(u128::from(u64::MAX));
    format!("(set-option :timeout {timeout_ms})\n")
}

fn append_var_declarations(script: &mut String, vars: &[ChcVar]) {
    for var in vars {
        let sort_str = sort_to_smtlib(&var.sort);
        let name = quote_symbol(&var.name);
        script.push_str(&format!("(declare-const {name} {sort_str})\n"));
    }
}

fn append_assertion(script: &mut String, expr: &ChcExpr) {
    let expr_str = InvariantModel::expr_to_smtlib(expr);
    script.push_str(&format!("(assert {expr_str})\n"));
}

#[cfg(test)]
#[path = "persistent_tests.rs"]
mod tests;
