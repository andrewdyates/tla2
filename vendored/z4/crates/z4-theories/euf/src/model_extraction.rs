// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF model extraction.

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use std::collections::BTreeMap;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, TermData, TermId};
use z4_core::Sort;

use crate::solver::EufSolver;
use crate::types::EufModel;

impl EufSolver<'_> {
    fn model_table_arg_value(&self, model: &EufModel, arg: TermId) -> String {
        if matches!(self.terms.sort(arg), Sort::Bool) {
            if let Some(value) = self.assigns.get(&arg).copied() {
                return if value {
                    "true".to_string()
                } else {
                    "false".to_string()
                };
            }
            if let Some(raw) = model.term_values.get(&arg) {
                if raw == "true" || raw == "false" {
                    return raw.clone();
                }
            }
            return format!("@?{}", arg.0);
        }
        if let Some(value) = model.term_values.get(&arg) {
            return value.clone();
        }
        format!("@?{}", arg.0)
    }

    /// Extract a model after solving (call after check() returns Sat)
    ///
    /// Returns an `EufModel` containing:
    /// - Element representatives for uninterpreted sorts
    /// - Term-to-element mappings
    /// - Function table interpretations for uninterpreted functions
    pub fn extract_model(&mut self) -> EufModel {
        // Ensure congruence closure is up-to-date
        self.rebuild_closure();

        let mut model = EufModel::default();
        let model_terms = self.scoped_model_terms();

        // Collect equivalence class representatives per sort
        // Maps (sort_name, representative_id) -> element_name
        let mut rep_to_elem: HashMap<(String, u32), String> = HashMap::new();
        // Counter for generating element names per sort
        let mut sort_counters: HashMap<String, usize> = HashMap::new();

        // First pass: assign element names to representatives
        for &term_id in &model_terms {
            let sort = self.terms.sort(term_id);

            // Only process uninterpreted sorts
            let sort_name = match sort {
                Sort::Uninterpreted(name) => name.clone(),
                _ => continue,
            };

            let rep = self.uf.find(term_id.0);
            let key = (sort_name.clone(), rep);

            if !rep_to_elem.contains_key(&key) {
                let counter = sort_counters.entry(sort_name.clone()).or_insert(0);
                let elem_name = format!("@{sort_name}!{counter}");
                *counter += 1;

                rep_to_elem.insert(key.clone(), elem_name.clone());

                // Add to sort_elements
                model
                    .sort_elements
                    .entry(sort_name)
                    .or_default()
                    .push(elem_name);
            }
        }

        // Second pass: map each term to its element name
        for &term_id in &model_terms {
            let sort = self.terms.sort(term_id);

            let sort_name = match sort {
                Sort::Uninterpreted(name) => name.clone(),
                _ => continue,
            };

            let rep = self.uf.find(term_id.0);
            let key = (sort_name, rep);

            if let Some(elem_name) = rep_to_elem.get(&key) {
                model.term_values.insert(term_id, elem_name.clone());
            }
        }

        // Assign distinct integer values to Int-sorted equivalence classes (#3172).
        // When EUF manages Int-sorted terms without a LIA/LRA solver, the model
        // validator defaults all unassigned ints to 0, violating disequalities.
        // Prefer actual constant values from terms in each class so that
        // validate_model sees consistent values for (= c 5) style assertions.
        {
            use num_bigint::BigInt;

            // First pass: find constant values per equivalence class
            let mut rep_const_val: HashMap<u32, BigInt> = HashMap::new();
            for &term_id in &model_terms {
                if !matches!(self.terms.sort(term_id), Sort::Int) {
                    continue;
                }
                if let TermData::Const(Constant::Int(n)) = self.terms.get(term_id) {
                    let rep = self.uf.find(term_id.0);
                    rep_const_val.entry(rep).or_insert_with(|| n.clone());
                }
            }

            // Second pass: assign values - use constant if available, else counter
            let mut int_rep_to_val: HashMap<u32, BigInt> = HashMap::new();
            // Start counter from a value unlikely to collide with constants
            let mut used_values: HashSet<BigInt> = rep_const_val.values().cloned().collect();
            let mut int_counter: i64 = 0;

            for &term_id in &model_terms {
                if !matches!(self.terms.sort(term_id), Sort::Int) {
                    continue;
                }

                let rep = self.uf.find(term_id.0);
                let val = int_rep_to_val
                    .entry(rep)
                    .or_insert_with(|| {
                        if let Some(const_val) = rep_const_val.get(&rep) {
                            const_val.clone()
                        } else {
                            // Find a value not used by any constant
                            loop {
                                let v = BigInt::from(int_counter);
                                int_counter += 1;
                                if !used_values.contains(&v) {
                                    used_values.insert(v.clone());
                                    return v;
                                }
                            }
                        }
                    })
                    .clone();
                model.int_values.insert(term_id, val);
            }
        }

        // Third pass: build function tables for uninterpreted functions
        // Use BTreeMap for deterministic ordering
        let mut fn_entries: BTreeMap<String, Vec<(Vec<String>, String, TermId)>> = BTreeMap::new();
        // Separate tracking for predicates (Bool-returning functions)
        let mut pred_entries: BTreeMap<String, Vec<(Vec<String>, String, TermId)>> =
            BTreeMap::new();

        for &term_id in &model_terms {
            // Get function applications
            let (sym, args) = match self.terms.get(term_id) {
                TermData::App(sym, args) if !Self::is_builtin_symbol(sym) => {
                    (sym.clone(), args.clone())
                }
                _ => continue,
            };

            // Skip nullary functions (constants) - handled in second pass
            if args.is_empty() {
                continue;
            }

            let result_sort = self.terms.sort(term_id);

            // Get element names for arguments
            let arg_values: Vec<String> = args
                .iter()
                .map(|&arg| self.model_table_arg_value(&model, arg))
                .collect();

            // Handle predicates (Bool-sorted functions) using assigns
            if matches!(result_sort, Sort::Bool) {
                // Get value from assigns (SAT model propagated to theory)
                let result_value = match self.assigns.get(&term_id) {
                    Some(true) => "true".to_string(),
                    Some(false) | None => "false".to_string(), // Default unassigned to false
                };

                pred_entries.entry(sym.to_string()).or_default().push((
                    arg_values,
                    result_value,
                    term_id,
                ));
                continue;
            }

            // Get element name for result (non-Bool functions)
            let result_value = model
                .term_values
                .get(&term_id)
                .cloned()
                .unwrap_or_else(|| format!("@?{}", term_id.0));

            fn_entries.entry(sym.to_string()).or_default().push((
                arg_values,
                result_value,
                term_id,
            ));
        }

        // Deduplicate function table entries by representative
        for (fn_name, entries) in fn_entries {
            let mut seen: HashMap<Vec<String>, String> = HashMap::new();
            let mut table = Vec::new();

            for (args, result, _term_id) in entries {
                // Use first occurrence for each argument combination
                if !seen.contains_key(&args) {
                    seen.insert(args.clone(), result.clone());
                    table.push((args, result));
                }
            }

            if !table.is_empty() {
                model.function_tables.insert(fn_name, table);
            }
        }

        // Deduplicate predicate table entries
        for (pred_name, entries) in pred_entries {
            let mut seen: HashMap<Vec<String>, String> = HashMap::new();
            let mut table = Vec::new();

            for (args, result, _term_id) in entries {
                // Use first occurrence for each argument combination
                if !seen.contains_key(&args) {
                    seen.insert(args.clone(), result.clone());
                    table.push((args, result));
                }
            }

            if !table.is_empty() {
                model.function_tables.insert(pred_name, table);
            }
        }

        // Populate func_app_const_terms from tracked values (#385)
        // This enables get-value to return actual values for UF applications returning Int/Real/BV
        model.func_app_const_terms.clone_from(&self.func_app_values);

        model
    }

    /// Extract SMT-LIB values for Int-sorted terms based on the current EUF equivalence classes.
    ///
    /// This is used for model printing in contexts that rely on EUF equalities but do not run
    /// the dedicated arithmetic theories (e.g., `QF_AX` with `Int` indices/elements).
    ///
    /// The returned map assigns a *distinct* integer to each equivalence class, preferring a
    /// concrete integer constant if one is present in the class.
    pub fn extract_int_term_values(&mut self) -> HashMap<TermId, String> {
        self.rebuild_closure();
        let model_terms = self.scoped_model_terms();

        // Group Int-sorted terms by their equivalence-class representative.
        let mut rep_to_terms: BTreeMap<u32, Vec<TermId>> = BTreeMap::new();
        for &term_id in &model_terms {
            if self.terms.sort(term_id) != &Sort::Int {
                continue;
            }
            let rep = self.uf.find(term_id.0);
            rep_to_terms.entry(rep).or_default().push(term_id);
        }

        // Prefer a concrete Int constant if present; otherwise assign fresh integers.
        let mut used_values: HashSet<String> = HashSet::new();
        let mut rep_to_value: BTreeMap<u32, String> = BTreeMap::new();

        let format_int_value = |n_str: &str| -> String {
            if let Some(rest) = n_str.strip_prefix('-') {
                format!("(- {rest})")
            } else {
                n_str.to_string()
            }
        };

        for (&rep, terms) in &rep_to_terms {
            let const_value = terms.iter().find_map(|&t| match self.terms.get(t) {
                TermData::Const(Constant::Int(n)) => Some(format_int_value(&n.to_string())),
                _ => None,
            });
            if let Some(v) = const_value {
                used_values.insert(v.clone());
                rep_to_value.insert(rep, v);
            }
        }

        let mut next_fresh: u64 = 0;
        for &rep in rep_to_terms.keys() {
            if rep_to_value.contains_key(&rep) {
                continue;
            }
            loop {
                let cand = next_fresh.to_string();
                next_fresh += 1;
                if used_values.insert(cand.clone()) {
                    rep_to_value.insert(rep, cand);
                    break;
                }
            }
        }

        // Expand class values back to term_id -> value.
        let mut term_values: HashMap<TermId, String> = HashMap::new();
        for (rep, terms) in rep_to_terms {
            let value = rep_to_value
                .get(&rep)
                .cloned()
                .unwrap_or_else(|| "0".to_string());
            for term in terms {
                term_values.insert(term, value.clone());
            }
        }

        term_values
    }
}
