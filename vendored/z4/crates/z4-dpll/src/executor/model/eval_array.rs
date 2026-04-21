// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (code-health split).
//! All methods are `impl Executor` — they share the same method namespace.

#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::term::TermData;
use z4_core::TermId;

use super::{EvalValue, Model, NormalizedArray, EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE};

use super::Executor;

impl Executor {
    /// Evaluate select(array, index) using array axioms (ROW1/ROW2).
    ///
    /// Recursively peels off `store` layers:
    /// - `select(store(a, i, v), j)` = if `i == j` then `v` else `select(a, j)`
    /// - For base arrays (variables), looks up in the array model.
    pub(in crate::executor) fn evaluate_select(
        &self,
        model: &Model,
        array: TermId,
        index: TermId,
    ) -> EvalValue {
        let index_val = self.evaluate_term(model, index);

        // Walk through store layers with visited-set cycle guard.
        // In a well-formed term DAG, this chain is structurally finite.
        let mut current_array = array;
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(current_array) {
                break; // cycle detected in malformed term
            }
            let term = self.ctx.terms.get(current_array);
            match term {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let store_index = args[1];
                    let store_value = args[2];
                    let store_index_val = self.evaluate_term(model, store_index);

                    // ROW1: same index -> return stored value
                    match (&index_val, &store_index_val) {
                        (EvalValue::Rational(i), EvalValue::Rational(j)) if i == j => {
                            return self.evaluate_term(model, store_value);
                        }
                        (EvalValue::Element(i), EvalValue::Element(j)) if i == j => {
                            return self.evaluate_term(model, store_value);
                        }
                        (
                            EvalValue::BitVec { value: i, .. },
                            EvalValue::BitVec { value: j, .. },
                        ) if i == j => {
                            return self.evaluate_term(model, store_value);
                        }
                        (EvalValue::Bool(i), EvalValue::Bool(j)) if i == j => {
                            return self.evaluate_term(model, store_value);
                        }
                        // ROW2: different index -> recurse into base array
                        (EvalValue::Unknown, _) | (_, EvalValue::Unknown) => {
                            return EvalValue::Unknown;
                        }
                        _ => {
                            // Different indices: peel this store and continue
                            current_array = args[0];
                            continue;
                        }
                    }
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    // const-array: all indices map to the same value
                    return self.evaluate_term(model, args[0]);
                }
                _ => break,
            }
        }

        // Base array: look up in array model
        self.lookup_array_model(model, current_array, &index_val)
    }

    /// Look up a base array variable in the array model.
    ///
    /// Store entries are matched with typed comparisons so mixed AUFLIA/AUFLRA
    /// models can validate concrete `select` assertions. Array defaults are
    /// only trusted in pure EUF/AX paths.
    fn lookup_array_model(&self, model: &Model, array: TermId, index_val: &EvalValue) -> EvalValue {
        let Some(ref array_model) = model.array_model else {
            return EvalValue::Unknown;
        };
        let Some(interp) = array_model.array_values.get(&array) else {
            return EvalValue::Unknown;
        };

        let has_arith_model = model.lia_model.is_some() || model.lra_model.is_some();
        let mut has_unparseable_index = false;
        for (stored_idx, stored_val) in &interp.stores {
            let parsed_idx = self.parse_model_value_string(stored_idx, &interp.index_sort);
            if matches!(parsed_idx, EvalValue::Unknown) {
                has_unparseable_index = true;
                continue;
            }
            if Self::eval_values_equal(index_val, &parsed_idx) {
                return self.parse_model_value_string(stored_val, &interp.element_sort);
            }
        }

        if has_unparseable_index {
            return EvalValue::Unknown;
        }

        // Under active arithmetic models, avoid trusting array defaults when no
        // concrete index match was found. Defaults are safe in pure EUF/AX paths.
        if !has_arith_model {
            if let Some(ref default) = interp.default {
                return self.parse_model_value_string(default, &interp.element_sort);
            }
        }

        EvalValue::Unknown
    }

    /// Compare `EvalValue`s conservatively for array index matching.
    ///
    /// `Unknown` is never equal to anything, including `Unknown`.
    pub(super) fn eval_values_equal(a: &EvalValue, b: &EvalValue) -> bool {
        !matches!(a, EvalValue::Unknown) && !matches!(b, EvalValue::Unknown) && a == b
    }

    /// both sides are reduced to (default, sorted-stores) and compared.
    /// Falls back to string comparison, then to SAT model when the evaluator
    /// cannot determine equality.
    pub(in crate::executor) fn evaluate_array_equality(
        &self,
        model: &Model,
        eq_term: TermId,
        args: &[TermId],
    ) -> EvalValue {
        // Try semantic comparison via normalized array models.
        if let Some(result) = self.compare_array_models_normalized(model, args[0], args[1]) {
            return EvalValue::Bool(result);
        }

        // Fall back to string representation comparison.
        let lhs = self.format_array_term_value(model, args[0]);
        let rhs = self.format_array_term_value(model, args[1]);
        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            if lhs == rhs {
                return EvalValue::Bool(true);
            }
            // Strings differ but this is unreliable for arrays (different syntax,
            // same semantics). Don't return false — fall through to SAT.
        }

        // No semantic evidence either way; fall back to SAT model.
        if let Some(b) = self.term_value(&model.sat_model, &model.term_to_var, eq_term) {
            EvalValue::Bool(b)
        } else {
            EvalValue::Unknown
        }
    }

    /// Normalize an array term to (default_value, sorted store map) for semantic comparison.
    ///
    /// Returns None if the array cannot be fully normalized.
    fn normalize_array_to_stores(&self, model: &Model, term_id: TermId) -> Option<NormalizedArray> {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Var(_, _) => {
                    let array_model = model.array_model.as_ref()?;
                    let interp = array_model.array_values.get(&term_id)?;
                    let mut stores: Vec<(String, String)> = interp.stores.clone();
                    stores.sort_by(|a, b| a.0.cmp(&b.0));
                    Some((interp.default.clone(), stores))
                }
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let mut base = self.normalize_array_to_stores(model, args[0])?;
                    let index_val = self.evaluate_term(model, args[1]);
                    let index_str = self.format_eval_value(&index_val, args[1]);
                    let value_val = self.evaluate_term(model, args[2]);
                    let value_str = self.format_eval_value(&value_val, args[2]);

                    // Overwrite existing entry at this index if present.
                    if let Some(existing) = base.1.iter_mut().find(|(k, _)| *k == index_str) {
                        existing.1 = value_str;
                    } else {
                        base.1.push((index_str, value_str));
                        base.1.sort_by(|a, b| a.0.cmp(&b.0));
                    }
                    Some(base)
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    let default_val = self.evaluate_term(model, args[0]);
                    let default_str = self.format_eval_value(&default_val, args[0]);
                    Some((Some(default_str), Vec::new()))
                }
                TermData::Let(_, body) => self.normalize_array_to_stores(model, *body),
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => self.normalize_array_to_stores(model, *then_br),
                    EvalValue::Bool(false) => self.normalize_array_to_stores(model, *else_br),
                    _ => None,
                },
                _ => None,
            }
        })
    }

    /// Compare two array terms by normalizing both to (default, sorted-stores)
    /// and checking structural equality.
    ///
    /// Returns Some(true) if provably equal, Some(false) if provably different,
    /// None if comparison cannot be determined.
    fn compare_array_models_normalized(&self, model: &Model, a: TermId, b: TermId) -> Option<bool> {
        let norm_a = self.normalize_array_to_stores(model, a)?;
        let norm_b = self.normalize_array_to_stores(model, b)?;
        Some(norm_a == norm_b)
    }
}
