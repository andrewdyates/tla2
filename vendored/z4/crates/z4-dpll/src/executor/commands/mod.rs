// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB command handlers for the executor.
//!
//! This module contains implementations for SMT-LIB query commands:
//! - `get-info`: Return solver metadata and statistics
//! - `get-option`: Return option values
//! - `get-assertions`: Return current assertions
//! - `simplify`: Simplify and format a term
//! - `get-assignment`: Return truth values of named formulas
//! - `get-unsat-core`: Return unsatisfiable core
//! - `get-unsat-assumptions`: Return unsat subset from check-sat-assuming

use z4_core::term::{Constant, TermData};
use z4_core::{quote_symbol, string_literal, TermId};
use z4_frontend::OptionValue;

use crate::executor::model::EvalValue;
use crate::executor_format::{format_bigint, format_rational, format_sort, format_symbol};
use crate::executor_types::{SolveResult, StatValue, UnknownReason};

use super::Executor;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

impl Executor {
    /// Generate output for get-info command
    pub(super) fn get_info(&self, keyword: &str) -> String {
        // Keywords may come with or without the colon prefix
        let key = keyword.trim_start_matches(':');
        match key {
            "name" => "(:name \"z4\")".to_string(),
            "version" => format!("(:version \"{}\")", env!("CARGO_PKG_VERSION")),
            "authors" => "(:authors \"Z4 Authors\")".to_string(),
            "error-behavior" => "(:error-behavior immediate-exit)".to_string(),
            "reason-unknown" => {
                // Return reason for 'unknown' result if applicable
                match self.last_result {
                    Some(SolveResult::Unknown) => {
                        let reason = self.last_unknown_reason.unwrap_or(UnknownReason::Unknown);
                        format!("(:reason-unknown {reason})")
                    }
                    _ => "(error \"no unknown result to explain\")".to_string(),
                }
            }
            "all-statistics" => {
                // Return solver statistics in SMT-LIB format (Z3-compatible)
                self.format_statistics_smt2()
            }
            "assertion-stack-levels" => {
                format!("(:assertion-stack-levels {})", self.assertion_count())
            }
            _ => format!("(error \"unsupported info keyword: {keyword}\")"),
        }
    }

    /// Format statistics as an SMT-LIB s-expression (Z3-compatible format)
    ///
    /// Outputs keyword-value pairs sorted alphabetically:
    /// ```text
    /// (:conflicts        42
    ///  :decisions        100
    ///  :propagations     512
    ///  ...)
    /// ```
    fn format_statistics_smt2(&self) -> String {
        let stats = &self.last_statistics;
        // Fixed fields
        let mut entries: Vec<(String, String)> = vec![
            ("conflicts".to_string(), stats.conflicts.to_string()),
            ("decisions".to_string(), stats.decisions.to_string()),
            (
                "deleted-clauses".to_string(),
                stats.deleted_clauses.to_string(),
            ),
            (
                "learned-clauses".to_string(),
                stats.learned_clauses.to_string(),
            ),
            (
                "num-assertions".to_string(),
                stats.num_assertions.to_string(),
            ),
            ("num-clauses".to_string(), stats.num_clauses.to_string()),
            ("num-vars".to_string(), stats.num_vars.to_string()),
            ("propagations".to_string(), stats.propagations.to_string()),
            ("restarts".to_string(), stats.restarts.to_string()),
            (
                "theory-conflicts".to_string(),
                stats.theory_conflicts.to_string(),
            ),
            (
                "theory-propagations".to_string(),
                stats.theory_propagations.to_string(),
            ),
        ];

        // Extra fields (BTreeMap iterates in sorted key order)
        for (key, value) in &stats.extra {
            let formatted_value = match value {
                StatValue::Int(n) => n.to_string(),
                StatValue::Float(f) => format!("{f:.2}"),
                StatValue::String(s) => string_literal(s),
            };
            // Convert underscores to dashes for SMT-LIB style
            let smt_key = key.replace('_', "-");
            entries.push((smt_key, formatted_value));
        }

        // Sort alphabetically by key
        entries.sort_by(|a, b| a.0.cmp(&b.0));

        // Calculate max key length for column alignment
        let max_len = entries.iter().map(|(k, _)| k.len()).max().unwrap_or(0);

        // Format as SMT-LIB s-expression
        let lines: Vec<String> = entries
            .iter()
            .map(|(k, v)| {
                let padding = " ".repeat(max_len.saturating_sub(k.len()) + 1);
                format!(":{k}{padding}{v}")
            })
            .collect();

        format!("({})", lines.join("\n "))
    }

    /// Get an option value for get-option command
    pub(super) fn get_option_value(&self, keyword: &str) -> String {
        let key = keyword.trim_start_matches(':');
        match self.ctx.get_option(key) {
            Some(OptionValue::Bool(b)) => format!("(:{key} {b})"),
            Some(OptionValue::String(s)) => format!("(:{} {})", key, string_literal(s)),
            Some(OptionValue::Numeral(n)) => format!("(:{key} {n})"),
            #[allow(unreachable_patterns)]
            Some(_) => format!("(:{key} unsupported)"),
            None => format!("(error \"unknown option: {keyword}\")"),
        }
    }

    /// Get current assertions for get-assertions command
    pub(super) fn assertions(&self) -> String {
        if self.ctx.assertions.is_empty() {
            return "()".to_string();
        }

        let formatted: Vec<String> = self
            .ctx
            .assertions
            .iter()
            .map(|&term_id| self.format_term(term_id))
            .collect();

        format!("({})", formatted.join("\n "))
    }

    /// Simplify a term and return its SMT-LIB representation
    ///
    /// The term is already simplified during elaboration (by the TermStore),
    /// so this just formats the already-simplified term.
    pub(super) fn simplify(&self, term_id: TermId) -> String {
        self.format_term(term_id)
    }

    /// Format a term for SMT-LIB output (reconstructs the expression)
    pub(crate) fn format_term(&self, term_id: TermId) -> String {
        let term = self.ctx.terms.get(term_id);
        match term {
            TermData::Var(name, _) => quote_symbol(name),
            TermData::Const(Constant::Bool(true)) => "true".to_string(),
            TermData::Const(Constant::Bool(false)) => "false".to_string(),
            TermData::Const(Constant::Int(n)) => format_bigint(n),
            TermData::Const(Constant::Rational(r)) => format_rational(&r.0),
            TermData::Const(Constant::String(s)) => string_literal(s),
            TermData::Const(Constant::BitVec { value, width }) => {
                let hex_width = (*width as usize).div_ceil(4);
                format!("#x{:0>width$}", value.to_str_radix(16), width = hex_width)
            }
            TermData::Not(inner) => format!("(not {})", self.format_term(*inner)),
            TermData::Ite(cond, then_br, else_br) => format!(
                "(ite {} {} {})",
                self.format_term(*cond),
                self.format_term(*then_br),
                self.format_term(*else_br)
            ),
            TermData::App(sym, args) => {
                let name = format_symbol(sym);
                if args.is_empty() {
                    name
                } else {
                    let args_str: Vec<String> = args.iter().map(|&a| self.format_term(a)).collect();
                    format!("({} {})", name, args_str.join(" "))
                }
            }
            TermData::Let(bindings, body) => {
                // Let bindings should normally be expanded, but format just in case
                let bindings_str: Vec<String> = bindings
                    .iter()
                    .map(|(name, term)| {
                        format!("({} {})", quote_symbol(name), self.format_term(*term))
                    })
                    .collect();
                format!(
                    "(let ({}) {})",
                    bindings_str.join(" "),
                    self.format_term(*body)
                )
            }
            TermData::Forall(vars, body, _triggers) => {
                let vars_str: Vec<String> = vars
                    .iter()
                    .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_sort(sort)))
                    .collect();
                format!(
                    "(forall ({}) {})",
                    vars_str.join(" "),
                    self.format_term(*body)
                )
            }
            TermData::Exists(vars, body, _triggers) => {
                let vars_str: Vec<String> = vars
                    .iter()
                    .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_sort(sort)))
                    .collect();
                format!(
                    "(exists ({}) {})",
                    vars_str.join(" "),
                    self.format_term(*body)
                )
            }
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in format_term(): {other:?}"),
        }
    }

    /// Check if produce-assignments option is enabled
    pub(super) fn produce_assignments_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-assignments"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Check if produce-unsat-cores option is enabled
    pub(super) fn produce_unsat_cores_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-unsat-cores"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Get assignment of named formulas (get-assignment command)
    ///
    /// Returns the truth values of all named Boolean formulas.
    pub(super) fn get_assignment(&self) -> String {
        // Check that produce-assignments is enabled
        if !self.produce_assignments_enabled() {
            return "(error \"assignment generation is not enabled, set :produce-assignments to true\")".to_string();
        }

        // Check if we have a model
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                // SAT with no model (trivially satisfiable, no named terms to evaluate)
                return "()".to_string();
            }
            (Some(SolveResult::Unknown), _) => {
                // Unknown - still allowed, return assignment if available
                if let Some(m) = &self.last_model {
                    m
                } else {
                    return "()".to_string();
                }
            }
            _ => {
                return "(error \"assignment is not available\")".to_string();
            }
        };

        // Collect assignments for named terms
        let mut assignments = Vec::new();
        for (name, term_id) in self.ctx.named_terms_iter() {
            let value = self.evaluate_term(model, term_id);
            if let EvalValue::Bool(b) = value {
                assignments.push(format!("({} {})", quote_symbol(name), b));
            }
        }

        if assignments.is_empty() {
            "()".to_string()
        } else {
            format!("({})", assignments.join("\n "))
        }
    }

    /// Get unsatisfiable core (get-unsat-core command)
    ///
    /// Returns names of assertions that form an unsatisfiable core.
    /// When check-sat was redirected through assumption-based solving
    /// (produce-unsat-cores enabled), uses the SAT solver's failed-assumption
    /// core for a minimal result. Otherwise falls back to all named assertions.
    pub(crate) fn unsat_core(&self) -> String {
        // Check that produce-unsat-cores is enabled
        if !self.produce_unsat_cores_enabled() {
            return "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")".to_string();
        }

        // Check that last result was unsat
        match self.last_result {
            Some(SolveResult::Unsat) => {
                // Use proof-based core when available (from assumption-based solving)
                if let (Some(core_terms), Some(term_to_name)) =
                    (&self.last_assumption_core, &self.last_core_term_to_name)
                {
                    let names: Vec<String> = core_terms
                        .iter()
                        .filter_map(|tid| term_to_name.get(tid))
                        .map(|name| quote_symbol(name))
                        .collect();

                    return if names.is_empty() {
                        "()".to_string()
                    } else {
                        format!("({})", names.join(" "))
                    };
                }

                // Fallback: return all named assertions
                let names: Vec<String> = self
                    .ctx
                    .named_terms_iter()
                    .map(|(name, _)| quote_symbol(name))
                    .collect();

                if names.is_empty() {
                    "()".to_string()
                } else {
                    format!("({})", names.join(" "))
                }
            }
            _ => "(error \"unsat core is not available, last result was not unsat\")".to_string(),
        }
    }

    /// Get unsatisfiable assumptions (get-unsat-assumptions command)
    ///
    /// Returns the subset of assumptions from check-sat-assuming that contributed
    /// to unsatisfiability. Per SMT-LIB 2.6, this returns a subset of the literals
    /// from the most recent check-sat-assuming call that was unsatisfiable.
    pub(super) fn unsat_assumptions(&self) -> String {
        // Check that last result was unsat and we have assumptions
        match (&self.last_result, &self.last_assumptions) {
            (Some(SolveResult::Unsat), Some(assumptions)) => {
                if assumptions.is_empty() {
                    return "()".to_string();
                }

                // Use the minimal core if available (from SAT assumption-based solving)
                // Otherwise fall back to all assumptions
                let core_assumptions: &[TermId] = match &self.last_assumption_core {
                    Some(core) => core.as_slice(),
                    None => assumptions.as_slice(),
                };

                if core_assumptions.is_empty() {
                    return "()".to_string();
                }

                let literals: Vec<String> = core_assumptions
                    .iter()
                    .map(|&term_id| self.format_term(term_id))
                    .collect();

                format!("({})", literals.join(" "))
            }
            (Some(SolveResult::Unsat), None) => {
                // Unsat but no assumptions (regular check-sat, not check-sat-assuming)
                "(error \"no check-sat-assuming has been performed\")".to_string()
            }
            (Some(SolveResult::Sat), _) => {
                "(error \"unsat assumptions not available, last result was sat\")".to_string()
            }
            (Some(SolveResult::Unknown), _) => {
                "(error \"unsat assumptions not available, last result was unknown\")".to_string()
            }
            (None, _) => {
                "(error \"unsat assumptions not available, no check-sat has been performed\")"
                    .to_string()
            }
        }
    }
}
