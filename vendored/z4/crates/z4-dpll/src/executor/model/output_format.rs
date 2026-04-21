// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model output formatting helpers: function tables, array values, eval-value formatting.
//!
//! Extracted from `output.rs` for code health. The main `get-model`/`get-value`/
//! `get-objectives` methods remain in `output.rs`; this module has the formatting
//! and placeholder-resolution methods they call.

use z4_core::term::TermData;
use z4_core::{quote_symbol, string_literal, Sort, TermId};

use crate::executor_format::{
    format_bitvec, format_default_value, format_model_atom, format_sort, format_value,
};

use super::Executor;
use super::{EvalValue, Model};

/// Red zone size for `stacker::maybe_grow` in array model formatting (#4602).
const ARRAY_FMT_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for array model formatting recursion.
const ARRAY_FMT_STACK_SIZE: usize = 2 * 1024 * 1024;

impl Executor {
    /// Format a function table as an SMT-LIB define-fun.
    ///
    /// Resolves `@?N` placeholder values (from EUF model extraction) to concrete
    /// theory values using the full model (#5452).
    pub(super) fn format_function_table(
        &self,
        name: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
        model: &Model,
    ) -> String {
        // Generate parameter names: x0, x1, ...
        let params: Vec<String> = arg_sorts
            .iter()
            .enumerate()
            .map(|(i, s)| format!("(x{} {})", i, format_sort(s)))
            .collect();

        let params_str = params.join(" ");
        let result_sort_str = format_sort(result_sort);

        // Resolve @?N placeholders in table entries (#5452).
        let resolved_table: Vec<(Vec<String>, String)> = table
            .iter()
            .map(|(args, result)| {
                let resolved_args: Vec<String> = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        let sort = arg_sorts.get(i).cloned().unwrap_or(Sort::Bool);
                        self.resolve_table_value(arg, &sort, model)
                    })
                    .collect();
                let resolved_result = self.resolve_table_value(result, result_sort, model);
                (resolved_args, resolved_result)
            })
            .collect();

        // Build nested ite expression from resolved table.
        let body = if resolved_table.is_empty() {
            // Empty table - return default value.
            format_value(result_sort, None, &self.ctx.terms)
        } else {
            self.format_function_body(arg_sorts, result_sort, &resolved_table)
        };

        format!(
            "  (define-fun {} ({}) {}\n    {})",
            quote_symbol(name),
            params_str,
            result_sort_str,
            body
        )
    }

    /// Resolve a raw function table value, replacing `@?N` placeholders with
    /// concrete values from theory models (#5452).
    ///
    /// EUF model extraction generates `@?N` for Int/Real/BV-sorted terms that
    /// are not in `term_values` (which only covers Uninterpreted sorts). This
    /// method parses the term ID and evaluates it against the full model.
    fn resolve_table_value(&self, raw: &str, sort: &Sort, model: &Model) -> String {
        if let Some(id_str) = raw.strip_prefix("@?") {
            if let Ok(id) = id_str.parse::<u32>() {
                let term_id = TermId(id);
                let eval = self.evaluate_term(model, term_id);
                if !matches!(eval, EvalValue::Unknown) {
                    return self.format_eval_value(&eval, term_id);
                }
                // If evaluate_term returns Unknown, use sort-appropriate default.
                return format_value(sort, None, &self.ctx.terms);
            }
        }
        raw.to_string()
    }

    /// Build nested ite expression for function table.
    fn format_function_body(
        &self,
        _arg_sorts: &[Sort],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
    ) -> String {
        if table.is_empty() {
            return format_value(result_sort, None, &self.ctx.terms);
        }

        // Use last entry as the default (else branch).
        let (_, default_result) = table.last().expect("non-empty checked above");

        if table.len() == 1 {
            // Single entry - just return the result.
            return default_result.clone();
        }

        // Build nested ite from all entries except last (which becomes the else).
        let mut result = default_result.clone();

        for (args, value) in table.iter().rev().skip(1) {
            // Build condition: (and (= x0 arg0) (= x1 arg1) ...).
            let conditions: Vec<String> = args
                .iter()
                .enumerate()
                .map(|(i, arg)| format!("(= x{i} {arg})"))
                .collect();

            let condition = if conditions.len() == 1 {
                conditions[0].clone()
            } else {
                format!("(and {})", conditions.join(" "))
            };

            result = format!("(ite {condition} {value} {result})");
        }

        result
    }

    /// Format an array value from `ArrayInterpretation` for model output.
    pub(super) fn format_array_value(
        &self,
        sort: &Sort,
        interp: &z4_arrays::ArrayInterpretation,
    ) -> String {
        let sort_str = format_sort(sort);

        // Start with a const-array if we have a default, otherwise use a placeholder.
        let base = if let Some(ref default) = interp.default {
            format!("((as const {sort_str}) {default})")
        } else {
            // Use a default value based on element sort.
            let default_val = match sort {
                Sort::Array(arr) => format_default_value(&arr.element_sort),
                _ => "0".to_string(),
            };
            format!("((as const {sort_str}) {default_val})")
        };

        // Apply stores on top.
        let mut result = base;
        for (index, value) in &interp.stores {
            result = format!("(store {result} {index} {value})");
        }

        result
    }

    /// Format a default array value when no model info is available.
    pub(super) fn format_default_array(&self, sort: &Sort) -> String {
        let sort_str = format_sort(sort);
        let default_val = match sort {
            Sort::Array(arr) => format_default_value(&arr.element_sort),
            _ => "0".to_string(),
        };
        format!("((as const {sort_str}) {default_val})")
    }

    /// Format an array term's value for get-value output.
    ///
    /// This prefers using `ArrayModel` when available (QF_AX / QF_AUFL*), and otherwise
    /// falls back to rebuilding a value for common array constructors (`store`, `const-array`).
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested store chains (#4602).
    pub(super) fn format_array_term_value(&self, model: &Model, term_id: TermId) -> Option<String> {
        stacker::maybe_grow(ARRAY_FMT_STACK_RED_ZONE, ARRAY_FMT_STACK_SIZE, || {
            let sort = self.ctx.terms.sort(term_id);
            if !matches!(sort, Sort::Array(_)) {
                return None;
            }

            match self.ctx.terms.get(term_id) {
                TermData::Var(_, _) => {
                    let array_model = model.array_model.as_ref()?;
                    let interp = array_model.array_values.get(&term_id)?;
                    Some(self.format_array_value(sort, interp))
                }
                TermData::Let(_, body) => self.format_array_term_value(model, *body),
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => self.format_array_term_value(model, *then_br),
                    EvalValue::Bool(false) => self.format_array_term_value(model, *else_br),
                    _ => None,
                },
                TermData::App(sym, args) => match sym.name() {
                    "store" if args.len() == 3 => {
                        let base_sort = self.ctx.terms.sort(args[0]);
                        let base = self
                            .format_array_term_value(model, args[0])
                            .unwrap_or_else(|| self.format_default_array(base_sort));

                        let index_val = self.evaluate_term(model, args[1]);
                        let index_str = self.format_eval_value(&index_val, args[1]);

                        let value_val = self.evaluate_term(model, args[2]);
                        let value_str = self.format_eval_value(&value_val, args[2]);

                        Some(format!("(store {base} {index_str} {value_str})"))
                    }
                    "const-array" if args.len() == 1 => {
                        let default_val = self.evaluate_term(model, args[0]);
                        let default_str = self.format_eval_value(&default_val, args[0]);
                        Some(format!(
                            "((as const {}) {})",
                            format_sort(sort),
                            default_str
                        ))
                    }
                    _ => None,
                },
                _ => None,
            }
        })
    }

    /// Format an evaluated value for SMT-LIB output.
    pub(super) fn format_eval_value(&self, value: &EvalValue, term_id: TermId) -> String {
        match value {
            EvalValue::Bool(true) => "true".to_string(),
            EvalValue::Bool(false) => "false".to_string(),
            EvalValue::Element(elem) => {
                let sort = self.ctx.terms.sort(term_id);
                format_model_atom(sort, elem)
            }
            EvalValue::Rational(r) => {
                if r.is_integer() {
                    r.numer().to_string()
                } else {
                    format!("(/ {} {})", r.numer(), r.denom())
                }
            }
            EvalValue::BitVec { value, width } => {
                // Use format_bitvec for SMT-LIB compliant output (#1793).
                format_bitvec(value, *width)
            }
            EvalValue::Fp(fp_val) => fp_val.to_smtlib(),
            EvalValue::String(s) => string_literal(s),
            EvalValue::Seq(elems) => {
                if elems.is_empty() {
                    let sort = self.ctx.terms.sort(term_id);
                    format!("(as seq.empty {sort})")
                } else {
                    // Build seq.++ of seq.unit elements
                    let units: Vec<String> = elems
                        .iter()
                        .map(|e| {
                            let inner = self.format_eval_value(e, term_id);
                            format!("(seq.unit {inner})")
                        })
                        .collect();
                    if units.len() == 1 {
                        // SAFETY: len() == 1 guarantees next() returns Some
                        units.into_iter().next().expect("invariant: single element")
                    } else {
                        let joined = units.join(" ");
                        format!("(seq.++ {joined})")
                    }
                }
            }
            EvalValue::Unknown => {
                // Fall back to default for the sort.
                let sort = self.ctx.terms.sort(term_id);
                format_value(sort, None, &self.ctx.terms)
            }
        }
    }

    /// Resolve `@?N` placeholder values in a function table using the full model (#5452).
    ///
    /// The EUF model builds function tables before LIA/LRA/BV theory values are
    /// merged into `term_values`. Int/Real/BV-returning functions get `@?{term_id}`
    /// placeholders for their result values (and sometimes arguments). This method
    /// resolves those placeholders using `evaluate_term`, which consults all theory
    /// models including `func_app_const_terms`, `lia_model`, `lra_model`, and `bv_model`.
    pub(super) fn resolve_function_table(
        &self,
        model: &Model,
        table: &[(Vec<String>, String)],
    ) -> Vec<(Vec<String>, String)> {
        table
            .iter()
            .map(|(args, result)| {
                let resolved_args: Vec<String> = args
                    .iter()
                    .map(|a| self.resolve_placeholder(model, a))
                    .collect();
                let resolved_result = self.resolve_placeholder(model, result);
                (resolved_args, resolved_result)
            })
            .collect()
    }

    /// Resolve a single `@?N` placeholder string to a concrete value.
    ///
    /// If the string matches `@?N` where N is a valid term ID, evaluate that term
    /// using the full model and return the formatted value. Otherwise return the
    /// original string unchanged.
    fn resolve_placeholder(&self, model: &Model, value: &str) -> String {
        // Check if this is an @?N placeholder
        let term_id = match value.strip_prefix("@?") {
            Some(id_str) => match id_str.parse::<u32>() {
                Ok(id) if (id as usize) < self.ctx.terms.len() => TermId(id),
                _ => return value.to_string(),
            },
            None => return value.to_string(),
        };

        // Evaluate the term using the full model (which has all theory values)
        let eval = self.evaluate_term(model, term_id);
        match self.eval_value_to_model_atom(&eval) {
            Some(resolved) => resolved,
            None => value.to_string(), // Keep placeholder if evaluation fails
        }
    }
}
