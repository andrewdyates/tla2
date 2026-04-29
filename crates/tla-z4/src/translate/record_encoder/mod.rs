// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Record and tuple encoding as SMT product types for TLA+ operations.
//!
//! Encodes TLA+ records as named-field product types where each field
//! becomes an individual SMT variable. Tuples are records with positional
//! field names ("1", "2", etc.).
//!
//! # Encoding
//!
//! | TLA+ Operation               | SMT Encoding                                         |
//! |------------------------------|------------------------------------------------------|
//! | `[f1 |-> e1, ..., fn |-> en]`| `r__f1 = e1 /\ ... /\ r__fn = en`                   |
//! | `r.field`                    | read `r__field` SMT variable                         |
//! | `[r EXCEPT !.field = e]`     | fresh record, all fields equal except updated field  |
//! | `<<e1, ..., en>>`            | `t__1 = e1 /\ ... /\ t__n = en`                     |
//! | `t[i]`                       | read `t__i` SMT variable (constant index)            |
//! | `S1 \X S2`                   | enumerate all pairs from bounded sets                |
//! | `[f1: S1, ..., fn: Sn]`     | enumerate all field combinations from bounded sets   |
//! | `r1 = r2`                    | `r1__f1 = r2__f1 /\ ... /\ r1__fn = r2__fn`         |
//! | `DOMAIN r`                   | `{"f1", ..., "fn"}` as interned string set            |
//! | `DOMAIN <<e1,...,en>>`       | `{1, ..., n}` integer set                             |
//!
//! Records are expanded into per-field SMT variables at declaration time via
//! [`Z4Translator::declare_record_var`]. The encoder operates on these
//! pre-declared variables to build constraints.
//!
//! # Usage
//!
//! ```no_run
//! use tla_z4::translate::record_encoder::RecordEncoder;
//! use tla_z4::{Z4Translator, TlaSort};
//!
//! let mut trans = Z4Translator::new();
//! let enc = RecordEncoder::new();
//!
//! // Declare a record variable with fields a: Int, b: Bool
//! trans.declare_record_var("r", vec![
//!     ("a".to_string(), TlaSort::Int),
//!     ("b".to_string(), TlaSort::Bool),
//! ]).unwrap();
//!
//! // Get field term for r.a
//! let field_term = enc.translate_field_access(&trans, "r", "a").unwrap();
//! ```
//!
//! Part of #3749

use std::collections::HashMap;

use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::{TlaSort, Z4Translator};

/// Encoder for TLA+ records and tuples as SMT product types.
///
/// Provides methods to build and manipulate record/tuple constraints
/// within a [`Z4Translator`] context.
///
/// Records are represented as individual SMT variables per field:
/// a record variable `r` with fields `a: Int, b: Bool` becomes
/// SMT variables `r__a: Int` and `r__b: Bool`.
#[derive(Debug, Clone, Default)]
pub struct RecordEncoder;

impl RecordEncoder {
    /// Create a new record encoder.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Translate record field access `r.field`.
    ///
    /// Returns the z4 term for the field's SMT variable.
    /// The record must have been previously declared via
    /// [`Z4Translator::declare_record_var`].
    pub fn translate_field_access(
        &self,
        trans: &Z4Translator,
        record_name: &str,
        field_name: &str,
    ) -> Z4Result<Term> {
        trans.get_record_field(record_name, field_name)
    }

    /// Get the sort of a record field.
    ///
    /// Returns `None` if the record or field is not found.
    pub fn field_sort(
        &self,
        trans: &Z4Translator,
        record_name: &str,
        field_name: &str,
    ) -> Z4Result<TlaSort> {
        let info = trans.get_record_var(record_name)?;
        info.field_sorts
            .iter()
            .find(|(name, _)| name == field_name)
            .map(|(_, sort)| sort.clone())
            .ok_or_else(|| Z4Error::UnknownVariable(format!("{record_name}.{field_name}")))
    }

    /// Encode record construction `[f1 |-> e1, ..., fn |-> en]`.
    ///
    /// Asserts that each field of the target record variable equals
    /// the corresponding expression term. Returns the conjunction
    /// of all field equalities.
    ///
    /// The `field_terms` map provides pre-translated z4 terms for each
    /// field value expression.
    pub fn encode_record_construction(
        &self,
        trans: &mut Z4Translator,
        record_name: &str,
        field_terms: &HashMap<String, Term>,
    ) -> Z4Result<Term> {
        let info = trans.get_record_var(record_name)?.clone();

        if field_terms.len() != info.field_sorts.len() {
            return Err(Z4Error::UnsupportedOp(format!(
                "record construction arity mismatch: expected {} fields, got {}",
                info.field_sorts.len(),
                field_terms.len()
            )));
        }

        let mut conjuncts = Vec::with_capacity(info.field_sorts.len());
        for (field_name, _sort) in &info.field_sorts {
            let var_term =
                info.field_terms.get(field_name).copied().ok_or_else(|| {
                    Z4Error::UnknownVariable(format!("{record_name}.{field_name}"))
                })?;
            let val_term = field_terms.get(field_name).copied().ok_or_else(|| {
                Z4Error::UnsupportedOp(format!(
                    "missing field '{field_name}' in record construction"
                ))
            })?;
            let eq = trans.solver_mut().try_eq(var_term, val_term)?;
            conjuncts.push(eq);
        }

        build_conjunction(trans, &conjuncts)
    }

    /// Encode record EXCEPT `[r EXCEPT !.field = e]`.
    ///
    /// Creates constraints for a fresh record variable where:
    /// - The specified field equals `new_value`
    /// - All other fields equal the corresponding fields of the source record
    ///
    /// Returns the conjunction of all field constraints.
    pub fn encode_record_except(
        &self,
        trans: &mut Z4Translator,
        source_name: &str,
        target_name: &str,
        field_name: &str,
        new_value: Term,
    ) -> Z4Result<Term> {
        let source_info = trans.get_record_var(source_name)?.clone();
        let target_info = trans.get_record_var(target_name)?.clone();

        // Verify the field exists
        if !source_info.field_terms.contains_key(field_name) {
            return Err(Z4Error::UnknownVariable(format!(
                "{source_name}.{field_name}"
            )));
        }

        let mut conjuncts = Vec::with_capacity(source_info.field_sorts.len());
        for (fname, _sort) in &source_info.field_sorts {
            let target_term = target_info
                .field_terms
                .get(fname)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("{target_name}.{fname}")))?;

            if fname == field_name {
                // Updated field: target.field = new_value
                let eq = trans.solver_mut().try_eq(target_term, new_value)?;
                conjuncts.push(eq);
            } else {
                // Unchanged field: target.field = source.field
                let source_term =
                    source_info.field_terms.get(fname).copied().ok_or_else(|| {
                        Z4Error::UnknownVariable(format!("{source_name}.{fname}"))
                    })?;
                let eq = trans.solver_mut().try_eq(target_term, source_term)?;
                conjuncts.push(eq);
            }
        }

        build_conjunction(trans, &conjuncts)
    }

    /// Encode tuple construction `<<e1, ..., en>>`.
    ///
    /// Asserts that each element of the target tuple variable equals
    /// the corresponding expression term. Returns the conjunction
    /// of all element equalities.
    ///
    /// The `element_terms` slice provides pre-translated z4 terms for each
    /// element (0-indexed in the slice, mapped to 1-indexed tuple positions).
    pub fn encode_tuple_construction(
        &self,
        trans: &mut Z4Translator,
        tuple_name: &str,
        element_terms: &[Term],
    ) -> Z4Result<Term> {
        let info = trans.get_tuple_var(tuple_name)?.clone();

        if element_terms.len() != info.element_sorts.len() {
            return Err(Z4Error::UnsupportedOp(format!(
                "tuple construction arity mismatch: expected {} elements, got {}",
                info.element_sorts.len(),
                element_terms.len()
            )));
        }

        let mut conjuncts = Vec::with_capacity(info.element_sorts.len());
        for (i, &val_term) in element_terms.iter().enumerate() {
            let idx = i + 1; // 1-based indexing
            let var_term = info
                .element_terms
                .get(&idx)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("{tuple_name}[{idx}]")))?;
            let eq = trans.solver_mut().try_eq(var_term, val_term)?;
            conjuncts.push(eq);
        }

        build_conjunction(trans, &conjuncts)
    }

    /// Encode tuple indexing `t[i]` for a constant index.
    ///
    /// Returns the z4 term for the element at position `index` (1-based).
    pub fn translate_tuple_index(
        &self,
        trans: &Z4Translator,
        tuple_name: &str,
        index: usize,
    ) -> Z4Result<Term> {
        trans.get_tuple_element(tuple_name, index)
    }

    /// Encode record equality `r1 = r2` as field-wise conjunction.
    ///
    /// Two records are equal iff all their corresponding fields are equal.
    /// Returns the conjunction: `r1.f1 = r2.f1 /\ ... /\ r1.fn = r2.fn`.
    pub fn encode_record_equality(
        &self,
        trans: &mut Z4Translator,
        left_name: &str,
        right_name: &str,
    ) -> Z4Result<Term> {
        let left_info = trans.get_record_var(left_name)?.clone();
        let right_info = trans.get_record_var(right_name)?.clone();

        // Verify field sets match
        if left_info.field_sorts != right_info.field_sorts {
            return Ok(trans.solver_mut().bool_const(false));
        }

        let mut conjuncts = Vec::with_capacity(left_info.field_sorts.len());
        for (field_name, _sort) in &left_info.field_sorts {
            let left_term = left_info
                .field_terms
                .get(field_name)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("{left_name}.{field_name}")))?;
            let right_term = right_info
                .field_terms
                .get(field_name)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("{right_name}.{field_name}")))?;
            let eq = trans.solver_mut().try_eq(left_term, right_term)?;
            conjuncts.push(eq);
        }

        build_conjunction(trans, &conjuncts)
    }

    /// Encode Cartesian product `S1 \X S2` for bounded integer sets.
    ///
    /// For bounded sets represented as slices of integer constants,
    /// generates all pairs `<<s1, s2>>` where `s1 \in S1, s2 \in S2`.
    ///
    /// Returns a vector of (term1, term2) pairs representing the product elements.
    pub fn enumerate_cartesian_product(&self, set1: &[i64], set2: &[i64]) -> Vec<(i64, i64)> {
        let mut pairs = Vec::with_capacity(set1.len() * set2.len());
        for &a in set1 {
            for &b in set2 {
                pairs.push((a, b));
            }
        }
        pairs
    }

    /// Encode membership in a Cartesian product `<<x, y>> \in S1 \X S2`.
    ///
    /// Generates: `(x \in S1) /\ (y \in S2)` where membership in bounded
    /// sets is expanded to disjunctions.
    pub fn encode_cartesian_membership(
        &self,
        trans: &mut Z4Translator,
        x_term: Term,
        y_term: Term,
        set1_elements: &[Term],
        set2_elements: &[Term],
    ) -> Z4Result<Term> {
        let x_in_s1 = encode_finite_membership(trans, x_term, set1_elements)?;
        let y_in_s2 = encode_finite_membership(trans, y_term, set2_elements)?;
        Ok(trans.solver_mut().try_and(x_in_s1, y_in_s2)?)
    }

    /// Encode a record set `[f1: S1, ..., fn: Sn]`.
    ///
    /// Constrains each field of the target record variable to be a member
    /// of its corresponding bounded set. Returns the conjunction of all
    /// field membership constraints.
    ///
    /// The `field_sets` map provides the bounded set elements for each field,
    /// where each element is a pre-translated z4 term.
    pub fn encode_record_set_membership(
        &self,
        trans: &mut Z4Translator,
        record_name: &str,
        field_sets: &HashMap<String, Vec<Term>>,
    ) -> Z4Result<Term> {
        let info = trans.get_record_var(record_name)?.clone();

        let mut conjuncts = Vec::with_capacity(info.field_sorts.len());
        for (field_name, _sort) in &info.field_sorts {
            let var_term =
                info.field_terms.get(field_name).copied().ok_or_else(|| {
                    Z4Error::UnknownVariable(format!("{record_name}.{field_name}"))
                })?;
            let elements = field_sets.get(field_name).ok_or_else(|| {
                Z4Error::UnsupportedOp(format!(
                    "missing set for field '{field_name}' in record set"
                ))
            })?;
            let membership = encode_finite_membership(trans, var_term, elements)?;
            conjuncts.push(membership);
        }

        build_conjunction(trans, &conjuncts)
    }

    /// Declare a fresh record variable with the same field structure as an
    /// existing record. Returns the name of the fresh variable.
    pub fn declare_fresh_record(
        &self,
        trans: &mut Z4Translator,
        prefix: &str,
        source_name: &str,
    ) -> Z4Result<String> {
        let source_info = trans.get_record_var(source_name)?.clone();
        let fresh_name = trans.fresh_name(prefix);
        trans.declare_record_var(&fresh_name, source_info.field_sorts)?;
        Ok(fresh_name)
    }

    /// Encode `DOMAIN r` for a record variable.
    ///
    /// Returns interned integer IDs for each field name, suitable for building
    /// membership tests like `x \in DOMAIN r`. For a record with fields
    /// `{"a", "b"}`, returns terms for `[intern("a"), intern("b")]`.
    ///
    /// Part of #3787.
    pub fn encode_record_domain_ids(
        &self,
        trans: &mut Z4Translator,
        record_name: &str,
    ) -> Z4Result<Vec<Term>> {
        let info = trans.get_record_var(record_name)?.clone();
        let mut id_terms = Vec::with_capacity(info.field_sorts.len());
        for (field_name, _sort) in &info.field_sorts {
            let id = trans.intern_string(field_name);
            let term = trans.solver_mut().int_const(id);
            id_terms.push(term);
        }
        Ok(id_terms)
    }

    /// Encode `DOMAIN t` for a tuple variable.
    ///
    /// Returns integer terms `[1, 2, ..., n]` for a tuple of arity n.
    /// TLA+ tuples have integer domains corresponding to 1-based indices.
    ///
    /// Part of #3787.
    pub fn encode_tuple_domain_ids(
        &self,
        trans: &mut Z4Translator,
        tuple_name: &str,
    ) -> Z4Result<Vec<Term>> {
        let info = trans.get_tuple_var(tuple_name)?.clone();
        let mut id_terms = Vec::with_capacity(info.element_sorts.len());
        for i in 1..=info.element_sorts.len() {
            let term = trans.solver_mut().int_const(i as i64);
            id_terms.push(term);
        }
        Ok(id_terms)
    }

    /// Encode record variable equality with a literal record value.
    ///
    /// `r = [f1 |-> v1, ..., fn |-> vn]` becomes
    /// `r__f1 = v1 /\ ... /\ r__fn = vn`.
    ///
    /// The `literal_field_terms` map provides pre-translated z4 terms for
    /// each field value in the literal. Different field counts or missing
    /// fields produce `FALSE` (TLA+ semantics: records with different domains
    /// are not equal).
    ///
    /// Part of #3787.
    pub fn encode_record_var_eq_literal(
        &self,
        trans: &mut Z4Translator,
        record_name: &str,
        literal_field_terms: &HashMap<String, Term>,
    ) -> Z4Result<Term> {
        let info = trans.get_record_var(record_name)?.clone();

        // Different number of fields => not equal
        if literal_field_terms.len() != info.field_sorts.len() {
            return Ok(trans.solver_mut().bool_const(false));
        }

        let mut conjuncts = Vec::with_capacity(info.field_sorts.len());
        for (field_name, _sort) in &info.field_sorts {
            let var_term =
                info.field_terms.get(field_name).copied().ok_or_else(|| {
                    Z4Error::UnknownVariable(format!("{record_name}.{field_name}"))
                })?;
            // If the literal doesn't have this field, records have different shapes
            let val_term = match literal_field_terms.get(field_name) {
                Some(&t) => t,
                None => return Ok(trans.solver_mut().bool_const(false)),
            };
            let eq = trans.solver_mut().try_eq(var_term, val_term)?;
            conjuncts.push(eq);
        }

        build_conjunction(trans, &conjuncts)
    }

    /// Encode tuple variable equality with a literal tuple value.
    ///
    /// `t = <<v1, ..., vn>>` becomes `t__1 = v1 /\ ... /\ t__n = vn`.
    /// Different arities produce `FALSE` (TLA+ semantics).
    ///
    /// Part of #3787.
    pub fn encode_tuple_var_eq_literal(
        &self,
        trans: &mut Z4Translator,
        tuple_name: &str,
        literal_element_terms: &[Term],
    ) -> Z4Result<Term> {
        let info = trans.get_tuple_var(tuple_name)?.clone();

        // Different arity => not equal (TLA+ semantics)
        if literal_element_terms.len() != info.element_sorts.len() {
            return Ok(trans.solver_mut().bool_const(false));
        }

        let mut conjuncts = Vec::with_capacity(info.element_sorts.len());
        for (i, &val_term) in literal_element_terms.iter().enumerate() {
            let idx = i + 1; // 1-based
            let var_term = info
                .element_terms
                .get(&idx)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("{tuple_name}[{idx}]")))?;
            let eq = trans.solver_mut().try_eq(var_term, val_term)?;
            conjuncts.push(eq);
        }

        build_conjunction(trans, &conjuncts)
    }
}

/// Build a conjunction from a slice of boolean terms.
///
/// Returns `true` for an empty slice (vacuous conjunction).
fn build_conjunction(trans: &mut Z4Translator, conjuncts: &[Term]) -> Z4Result<Term> {
    if conjuncts.is_empty() {
        return Ok(trans.solver_mut().bool_const(true));
    }
    let mut result = conjuncts[0];
    for &c in &conjuncts[1..] {
        result = trans.solver_mut().try_and(result, c)?;
    }
    Ok(result)
}

/// Encode finite set membership `x \in {e1, ..., en}` as a disjunction.
///
/// Returns `(x = e1) \/ (x = e2) \/ ... \/ (x = en)`.
/// For an empty set, returns `false`.
fn encode_finite_membership(
    trans: &mut Z4Translator,
    element: Term,
    set_elements: &[Term],
) -> Z4Result<Term> {
    if set_elements.is_empty() {
        return Ok(trans.solver_mut().bool_const(false));
    }
    let mut disjuncts = Vec::with_capacity(set_elements.len());
    for &set_elem in set_elements {
        let eq = trans.solver_mut().try_eq(element, set_elem)?;
        disjuncts.push(eq);
    }
    let mut result = disjuncts[0];
    for &d in &disjuncts[1..] {
        result = trans.solver_mut().try_or(result, d)?;
    }
    Ok(result)
}

#[cfg(test)]
mod tests;
