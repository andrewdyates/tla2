// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model output entry points: `get-model`, `get-value`, `get-objectives`.
//!
//! Formatting helpers (function tables, array values, eval-value rendering)
//! live in sibling `output_format.rs`.

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::{quote_symbol, string_literal, Sort, TermId};

use crate::executor_format::{
    format_bigint, format_bitvec, format_model_atom, format_rational, format_sort, format_value,
};
use crate::executor_types::SolveResult;

use super::Executor;
use super::{debug_model, EvalValue, Model};

impl Executor {
    /// Generate objective output for get-objectives command.
    pub(crate) fn get_objectives(&self) -> String {
        if self.ctx.objectives().is_empty() {
            return "(error \"no objectives\")".to_string();
        }

        // Use the last model if available; for trivially SAT cases, fall back to defaults.
        let dummy_model;
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                dummy_model = Model {
                    sat_model: Vec::new(),
                    term_to_var: HashMap::new(),
                    euf_model: None,
                    array_model: None,
                    lra_model: None,
                    lia_model: None,
                    bv_model: None,
                    fp_model: None,
                    string_model: None,
                    seq_model: None,
                };
                &dummy_model
            }
            _ => {
                return "(error \"objectives are not available\")".to_string();
            }
        };

        let mut out = String::from("(objectives\n");
        for obj in self.ctx.objectives() {
            let term_str = self.format_term(obj.term);
            let value = self.evaluate_term(model, obj.term);
            let value_str = self.format_eval_value(&value, obj.term);
            out.push_str(&format!(" ({term_str} {value_str})\n"));
        }
        out.push_str(")\n");
        out
    }

    /// Generate model output for get-model command.
    pub(crate) fn model(&self) -> String {
        if !self.produce_models_enabled() {
            return "(error \"model generation is not enabled\")".to_string();
        }

        // Check if we have a model.
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                // SAT but no assertions (trivially satisfiable).
                return "(model\n)".to_string();
            }
            _ => {
                return "(error \"model is not available\")".to_string();
            }
        };

        // Collect model values for user-declared symbols.
        let mut definitions = Vec::new();

        for (name, info) in self.ctx.symbol_iter() {
            // Skip DT-internal symbols (constructors, testers, selectors) (#5412).
            if self.is_dt_internal_symbol(name) {
                continue;
            }

            // Handle functions with arguments (generate function tables).
            if !info.arg_sorts.is_empty() {
                // Check if we have EUF model with function tables.
                if let Some(ref euf_model) = model.euf_model {
                    if let Some(table) = euf_model.function_tables.get(name) {
                        // Resolve @?N placeholders in function table values (#5452).
                        // The EUF model builds tables before theory values are merged,
                        // so Int/Real/BV-returning functions have @?N placeholders
                        // instead of concrete values. Resolve them now using the
                        // full model which has all theory values available.
                        let resolved = self.resolve_function_table(model, table);
                        let def = self.format_function_table(
                            name,
                            &info.arg_sorts,
                            &info.sort,
                            &resolved,
                            model,
                        );
                        definitions.push(def);
                    }
                }
                continue;
            }

            // For constants (no arguments), need term_id.
            if let Some(term_id) = info.term {
                // For constants (no arguments), look up value.
                let sort_str = format_sort(&info.sort);

                // Handle array-sorted symbols specially.
                if let Sort::Array(_) = &info.sort {
                    if let Some(ref array_model) = model.array_model {
                        if let Some(interp) = array_model.array_values.get(&term_id) {
                            let array_value = self.format_array_value(&info.sort, interp);
                            definitions.push(format!(
                                "  (define-fun {} () {}\n    {})",
                                quote_symbol(name),
                                sort_str,
                                array_value
                            ));
                            continue;
                        }
                    }
                    // Fallback: return a default const-array.
                    let array_value = self.format_default_array(&info.sort);
                    definitions.push(format!(
                        "  (define-fun {} () {}\n    {})",
                        quote_symbol(name),
                        sort_str,
                        array_value
                    ));
                    continue;
                }

                let quoted_name = quote_symbol(name);

                // For DT-sorted variables, resolve to constructor expression (#5412).
                if let Sort::Uninterpreted(sort_name) = &info.sort {
                    if let Some(ctor_expr) = self.resolve_dt_value(sort_name, term_id, model) {
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {ctor_expr})"
                        ));
                        continue;
                    }
                }

                // Try EUF model first for uninterpreted sorts.
                if let Some(ref euf_model) = model.euf_model {
                    if let Some(elem) = euf_model.term_values.get(&term_id) {
                        let elem = format_model_atom(&info.sort, elem);
                        definitions
                            .push(format!("  (define-fun {quoted_name} () {sort_str} {elem})"));
                        continue;
                    }
                }

                // Try LRA model for Real sort.
                if matches!(info.sort, Sort::Real) {
                    if let Some(ref lra_model) = model.lra_model {
                        if let Some(val) = lra_model.values.get(&term_id) {
                            // Use the actual value without minimization.
                            let value_str = format_rational(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try LIA model for Int sort.
                if matches!(info.sort, Sort::Int) {
                    let debug = debug_model();
                    if debug {
                        safe_eprintln!(
                            "[MODEL] Looking up Int symbol '{}' term_id={}, lia_model={}",
                            name,
                            term_id.0,
                            model.lia_model.is_some()
                        );
                        if let Some(ref lm) = model.lia_model {
                            safe_eprintln!(
                                "[MODEL]   LIA model keys: {:?}",
                                lm.values.keys().map(|k| k.0).collect::<Vec<_>>()
                            );
                        }
                    }
                    if let Some(ref lia_model) = model.lia_model {
                        if let Some(val) = lia_model.values.get(&term_id) {
                            if debug {
                                safe_eprintln!(
                                    "[MODEL]   Found value {} for term_id={}",
                                    val,
                                    term_id.0
                                );
                            }
                            // Only apply minimization if counterexample minimization is enabled
                            // and bounds are available. Otherwise use the actual value.
                            let value_str = format_bigint(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        } else if debug {
                            safe_eprintln!(
                                "[MODEL]   NOT found in LIA model for term_id={}",
                                term_id.0
                            );
                        }
                    }
                    // Also check LRA model for Int (when using pure LRA solver for arithmetic).
                    if let Some(ref lra_model) = model.lra_model {
                        if let Some(val) = lra_model.values.get(&term_id) {
                            // Convert rational to integer if it's a whole number.
                            if val.is_integer() {
                                // Use the actual value without minimization.
                                let value_str = format_bigint(val.numer());
                                definitions.push(format!(
                                    "  (define-fun {quoted_name} () {sort_str} {value_str})"
                                ));
                                continue;
                            }
                        }
                    }
                }

                // Try BV model for BitVec sort.
                if let Sort::BitVec(bv) = &info.sort {
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(val) = bv_model.values.get(&term_id) {
                            let hex_str = format_bitvec(val, bv.width);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {hex_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try String model for String sort.
                if matches!(info.sort, Sort::String) {
                    if let Some(ref string_model) = model.string_model {
                        if let Some(val) = string_model.values.get(&term_id) {
                            let value_str = string_literal(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try FP model for FloatingPoint sort.
                if matches!(info.sort, Sort::FloatingPoint(..)) {
                    if let Some(ref fp_model) = model.fp_model {
                        if let Some(val) = fp_model.values.get(&term_id) {
                            let value_str = val.to_smtlib();
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try Seq model for Seq sort.
                if matches!(info.sort, Sort::Seq(..)) {
                    if let Some(ref seq_model) = model.seq_model {
                        if let Some(elems) = seq_model.values.get(&term_id) {
                            // Format as nested binary seq.++ of seq.unit applications.
                            // Empty sequence: (as seq.empty <sort>)
                            // Single element: (seq.unit <elem>)
                            // Multiple: left-associative binary (seq.++ ...) for SMT-LIB 2.6
                            let value_str = if elems.is_empty() {
                                format!("(as seq.empty {sort_str})")
                            } else if elems.len() == 1 {
                                format!("(seq.unit {})", elems[0])
                            } else {
                                // Build left-associative binary seq.++ tree:
                                // [e1,e2,e3] => (seq.++ (seq.++ (seq.unit e1) (seq.unit e2)) (seq.unit e3))
                                let mut acc = format!("(seq.unit {})", elems[0]);
                                for e in &elems[1..] {
                                    acc = format!("(seq.++ {acc} (seq.unit {e}))");
                                }
                                acc
                            };
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Check BV bool_overrides for Bool variables recovered from
                // preprocessor substitutions (#5512, #5524).
                if info.sort == Sort::Bool {
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(&b) = bv_model.bool_overrides.get(&term_id) {
                            let value_str = if b { "true" } else { "false" };
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Fall back to SAT model for Bool.
                let value = self.term_value(&model.sat_model, &model.term_to_var, term_id);
                let value_str = format_value(&info.sort, value, &self.ctx.terms);
                definitions.push(format!(
                    "  (define-fun {quoted_name} () {sort_str} {value_str})"
                ));
            }
        }

        if definitions.is_empty() {
            "(model\n)".to_string()
        } else {
            format!("(model\n{}\n)", definitions.join("\n"))
        }
    }

    /// Generate output for get-value command.
    pub(crate) fn values(&self, term_ids: &[TermId]) -> String {
        if !self.produce_models_enabled() {
            return "(error \"model generation is not enabled\")".to_string();
        }

        // Check if we have a model.
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                // SAT but no assertions - all terms have undefined values.
                let pairs: Vec<String> = term_ids
                    .iter()
                    .map(|&term_id| {
                        let term_str = self.format_term(term_id);
                        let sort = self.ctx.terms.sort(term_id);
                        let value_str = format_value(sort, None, &self.ctx.terms);
                        format!("({term_str} {value_str})")
                    })
                    .collect();
                return format!("({})", pairs.join(" "));
            }
            _ => {
                return "(error \"model is not available\")".to_string();
            }
        };

        // Generate values for each term using recursive evaluation.
        let pairs: Vec<String> = term_ids
            .iter()
            .map(|&term_id| {
                let term_str = self.format_term(term_id);
                let sort = self.ctx.terms.sort(term_id);
                let value_str = if matches!(sort, Sort::Array(_)) {
                    self.format_array_term_value(model, term_id)
                        .unwrap_or_else(|| self.format_default_array(sort))
                } else if let Sort::Uninterpreted(sort_name) = sort {
                    // DT-sorted terms: resolve to constructor expression (#5412).
                    self.resolve_dt_value(sort_name, term_id, model)
                        .unwrap_or_else(|| {
                            let eval_value = self.evaluate_term(model, term_id);
                            self.format_eval_value(&eval_value, term_id)
                        })
                } else {
                    let eval_value = self.evaluate_term(model, term_id);
                    // For selector apps returning Unknown, scan assertions (#5432).
                    let eval_value = if matches!(eval_value, EvalValue::Unknown) {
                        self.extract_value_from_asserted_equalities(model, term_id)
                            .unwrap_or(eval_value)
                    } else {
                        eval_value
                    };
                    // For Real/Int-sorted terms still Unknown after equality scan,
                    // try bound extraction from inequality assertions (#5506).
                    let eval_value = if matches!(eval_value, EvalValue::Unknown) {
                        match sort {
                            Sort::Real => self
                                .extract_real_from_assertion_bounds(term_id)
                                .map(EvalValue::Rational)
                                .unwrap_or(eval_value),
                            Sort::Int => self
                                .extract_int_from_assertion_bounds(term_id)
                                .map(|v| EvalValue::Rational(num_rational::BigRational::from(v)))
                                .unwrap_or(eval_value),
                            _ => eval_value,
                        }
                    } else {
                        eval_value
                    };
                    self.format_eval_value(&eval_value, term_id)
                };
                format!("({term_str} {value_str})")
            })
            .collect();

        format!("({})", pairs.join(" "))
    }
}
