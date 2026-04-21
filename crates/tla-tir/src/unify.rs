// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hindley-Milner style type unification for TLA2 (Snowcat parity).
//!
//! Provides constraint-based type inference via:
//! - `TypeUnifier`: core unification with occurs check
//! - `TypeScheme`: polymorphic type abstraction (forall quantification)
//! - `TypeError`: structured type error reporting
//!
//! Part of #3750: Apalache Gap 2 — Full Type Checker.

use std::collections::{HashMap, HashSet};

use tla_core::NameId;

use crate::types::TirType;

/// A type error discovered during unification.
#[derive(Debug, Clone)]
pub struct TypeError {
    pub message: String,
    pub location: Option<String>,
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(loc) = &self.location {
            write!(f, "{}: {}", loc, self.message)
        } else {
            write!(f, "{}", self.message)
        }
    }
}

/// A polymorphic type scheme: `forall a1, a2, ... . body`.
///
/// Type variables in `forall` are bound; all others are free.
/// Instantiation replaces each bound variable with a fresh type variable.
#[derive(Debug, Clone)]
pub struct TypeScheme {
    /// Bound type variable ids.
    pub forall: Vec<u32>,
    /// The type body (may reference variables in `forall`).
    pub body: TirType,
}

/// Core type unification engine.
///
/// Maintains a substitution map from type variable ids to types, supports
/// unification with occurs check, generalization, and instantiation.
pub struct TypeUnifier {
    /// Substitution: type variable id -> resolved type.
    subst: HashMap<u32, TirType>,
    /// Next fresh type variable id.
    next_var: u32,
    /// Accumulated type errors (non-fatal — we continue after errors).
    errors: Vec<TypeError>,
}

impl TypeUnifier {
    /// Create a new unifier with no substitutions.
    pub fn new() -> Self {
        Self {
            subst: HashMap::new(),
            next_var: 0,
            errors: Vec::new(),
        }
    }

    /// Allocate a fresh type variable.
    pub fn fresh_var(&mut self) -> TirType {
        let id = self.next_var;
        self.next_var += 1;
        TirType::Var(id)
    }

    /// Core unification: make `a` and `b` equal under the current substitution.
    ///
    /// Returns `Ok(())` on success, `Err(TypeError)` on failure. On failure,
    /// the error is also recorded internally for batch retrieval.
    pub fn unify(
        &mut self,
        a: &TirType,
        b: &TirType,
        location: Option<&str>,
    ) -> Result<(), TypeError> {
        let a = self.resolve(a);
        let b = self.resolve(b);

        // Equal types unify trivially.
        if a == b {
            return Ok(());
        }

        match (&a, &b) {
            // Var binds to anything (with occurs check).
            (TirType::Var(id), _) => self.bind(*id, &b, location),
            (_, TirType::Var(id)) => self.bind(*id, &a, location),

            // Dyn is compatible with anything (backward compatibility with gradual typing).
            (TirType::Dyn, _) | (_, TirType::Dyn) => Ok(()),

            // Structural recursion for compound types.
            (TirType::Set(a_inner), TirType::Set(b_inner)) => {
                self.unify(a_inner, b_inner, location)
            }
            (TirType::Seq(a_inner), TirType::Seq(b_inner)) => {
                self.unify(a_inner, b_inner, location)
            }
            (TirType::Func(a_dom, a_rng), TirType::Func(b_dom, b_rng)) => {
                self.unify(a_dom, b_dom, location)?;
                self.unify(a_rng, b_rng, location)
            }
            (TirType::Tuple(a_elems), TirType::Tuple(b_elems))
                if a_elems.len() == b_elems.len() =>
            {
                for (ae, be) in a_elems.iter().zip(b_elems.iter()) {
                    self.unify(ae, be, location)?;
                }
                Ok(())
            }
            (TirType::Record(a_fields), TirType::Record(b_fields))
                if a_fields.len() == b_fields.len() =>
            {
                self.unify_record_fields(a_fields, b_fields, location)
            }

            // Row type unification: OpenRecord with closed Record.
            (TirType::OpenRecord(fields_a, row_a), TirType::Record(fields_b)) => {
                self.unify_open_with_closed(fields_a, *row_a, fields_b, location)
            }
            (TirType::Record(fields_a), TirType::OpenRecord(fields_b, row_b)) => {
                self.unify_open_with_closed(fields_b, *row_b, fields_a, location)
            }

            // Row type unification: two OpenRecords.
            (TirType::OpenRecord(fields_a, row_a), TirType::OpenRecord(fields_b, row_b)) => {
                self.unify_open_records(fields_a, *row_a, fields_b, *row_b, location)
            }

            // Variant unification: same tags, unify payloads.
            (TirType::Variant(a_cases), TirType::Variant(b_cases))
                if a_cases.len() == b_cases.len() =>
            {
                self.unify_variants(a_cases, b_cases, location)
            }

            // Incompatible types.
            _ => {
                let err = TypeError {
                    message: format!("cannot unify {:?} with {:?}", a, b),
                    location: location.map(String::from),
                };
                self.errors.push(err.clone());
                Err(err)
            }
        }
    }

    /// Apply the current substitution to a type, resolving all bound variables.
    ///
    /// Chases substitution chains: if Var(0) -> Var(1) -> Int, resolve returns Int.
    pub fn resolve(&self, ty: &TirType) -> TirType {
        match ty {
            TirType::Var(id) => {
                if let Some(resolved) = self.subst.get(id) {
                    self.resolve(resolved)
                } else {
                    ty.clone()
                }
            }
            TirType::Set(inner) => TirType::Set(Box::new(self.resolve(inner))),
            TirType::Seq(inner) => TirType::Seq(Box::new(self.resolve(inner))),
            TirType::Func(d, r) => {
                TirType::Func(Box::new(self.resolve(d)), Box::new(self.resolve(r)))
            }
            TirType::Tuple(elems) => {
                TirType::Tuple(elems.iter().map(|e| self.resolve(e)).collect())
            }
            TirType::Record(fields) => TirType::Record(
                fields
                    .iter()
                    .map(|(id, ty)| (*id, self.resolve(ty)))
                    .collect(),
            ),
            TirType::OpenRecord(fields, row) => {
                let resolved_fields: Vec<(NameId, TirType)> = fields
                    .iter()
                    .map(|(id, ty)| (*id, self.resolve(ty)))
                    .collect();
                // If the row variable is bound, merge its fields.
                if let Some(row_ty) = self.subst.get(row) {
                    let row_resolved = self.resolve(row_ty);
                    match row_resolved {
                        TirType::Record(extra_fields) => {
                            let mut all_fields = resolved_fields;
                            all_fields.extend(extra_fields);
                            TirType::Record(all_fields)
                        }
                        TirType::OpenRecord(extra_fields, new_row) => {
                            let mut all_fields = resolved_fields;
                            all_fields.extend(extra_fields);
                            TirType::OpenRecord(all_fields, new_row)
                        }
                        _ => TirType::OpenRecord(resolved_fields, *row),
                    }
                } else {
                    TirType::OpenRecord(resolved_fields, *row)
                }
            }
            TirType::Variant(cases) => TirType::Variant(
                cases
                    .iter()
                    .map(|(tag, ty)| (tag.clone(), self.resolve(ty)))
                    .collect(),
            ),
            // Primitives and Dyn pass through.
            TirType::Bool | TirType::Int | TirType::Str | TirType::Dyn => ty.clone(),
        }
    }

    /// Generalize a type: quantify over free type variables not in the environment.
    ///
    /// This creates a `TypeScheme` where variables that appear in the type but
    /// NOT in `env_free_vars` become universally quantified.
    pub fn generalize(&self, ty: &TirType, env_free_vars: &HashSet<u32>) -> TypeScheme {
        let resolved = self.resolve(ty);
        let ty_vars = resolved.free_vars();
        let forall: Vec<u32> = ty_vars.difference(env_free_vars).copied().collect();
        TypeScheme {
            forall,
            body: resolved,
        }
    }

    /// Instantiate a type scheme: replace each bound variable with a fresh one.
    pub fn instantiate(&mut self, scheme: &TypeScheme) -> TirType {
        if scheme.forall.is_empty() {
            return scheme.body.clone();
        }
        let mapping: HashMap<u32, TirType> = scheme
            .forall
            .iter()
            .map(|&v| (v, self.fresh_var()))
            .collect();
        self.substitute_vars(&scheme.body, &mapping)
    }

    /// Get all accumulated errors.
    pub fn errors(&self) -> &[TypeError] {
        &self.errors
    }

    /// Record an error without failing unification (for error recovery).
    pub fn record_error(&mut self, err: TypeError) {
        self.errors.push(err);
    }

    /// Check if the unifier has any errors.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    // --- Internal helpers ---

    /// Bind a type variable to a type, with occurs check.
    fn bind(&mut self, var_id: u32, ty: &TirType, location: Option<&str>) -> Result<(), TypeError> {
        // Don't bind a variable to itself.
        if *ty == TirType::Var(var_id) {
            return Ok(());
        }
        // Occurs check: prevent infinite types.
        if self.occurs_in(var_id, ty) {
            let err = TypeError {
                message: format!("infinite type: t{} occurs in {:?}", var_id, ty),
                location: location.map(String::from),
            };
            self.errors.push(err.clone());
            return Err(err);
        }
        self.subst.insert(var_id, ty.clone());
        Ok(())
    }

    /// Occurs check: does `var_id` appear free in `ty`?
    fn occurs_in(&self, var_id: u32, ty: &TirType) -> bool {
        let resolved = self.resolve(ty);
        match &resolved {
            TirType::Var(id) => *id == var_id,
            TirType::Set(inner) | TirType::Seq(inner) => self.occurs_in(var_id, inner),
            TirType::Func(d, r) => self.occurs_in(var_id, d) || self.occurs_in(var_id, r),
            TirType::Tuple(elems) => elems.iter().any(|e| self.occurs_in(var_id, e)),
            TirType::Record(fields) => fields.iter().any(|(_, t)| self.occurs_in(var_id, t)),
            TirType::OpenRecord(fields, row) => {
                *row == var_id || fields.iter().any(|(_, t)| self.occurs_in(var_id, t))
            }
            TirType::Variant(cases) => cases.iter().any(|(_, t)| self.occurs_in(var_id, t)),
            TirType::Bool | TirType::Int | TirType::Str | TirType::Dyn => false,
        }
    }

    /// Unify record fields by name (order-independent).
    fn unify_record_fields(
        &mut self,
        a_fields: &[(NameId, TirType)],
        b_fields: &[(NameId, TirType)],
        location: Option<&str>,
    ) -> Result<(), TypeError> {
        for (a_id, a_ty) in a_fields {
            if let Some((_, b_ty)) = b_fields.iter().find(|(bid, _)| *bid == *a_id) {
                self.unify(a_ty, b_ty, location)?;
            } else {
                let err = TypeError {
                    message: format!(
                        "record field mismatch: field {:?} not found in other record",
                        a_id
                    ),
                    location: location.map(String::from),
                };
                self.errors.push(err.clone());
                return Err(err);
            }
        }
        Ok(())
    }

    /// Unify an open record (with row variable) against a closed record.
    ///
    /// All known fields of the open record must exist in the closed record and
    /// their types must unify. The row variable is bound to the remaining fields.
    fn unify_open_with_closed(
        &mut self,
        open_fields: &[(NameId, TirType)],
        row_var: u32,
        closed_fields: &[(NameId, TirType)],
        location: Option<&str>,
    ) -> Result<(), TypeError> {
        // Unify shared fields.
        for (id, open_ty) in open_fields {
            if let Some((_, closed_ty)) = closed_fields.iter().find(|(cid, _)| *cid == *id) {
                self.unify(open_ty, closed_ty, location)?;
            } else {
                let err = TypeError {
                    message: format!("open record field {:?} not found in closed record", id),
                    location: location.map(String::from),
                };
                self.errors.push(err.clone());
                return Err(err);
            }
        }
        // Bind the row variable to the remaining fields.
        let open_ids: HashSet<NameId> = open_fields.iter().map(|(id, _)| *id).collect();
        let remaining: Vec<(NameId, TirType)> = closed_fields
            .iter()
            .filter(|(id, _)| !open_ids.contains(id))
            .cloned()
            .collect();
        self.bind(row_var, &TirType::Record(remaining), location)
    }

    /// Unify two open records.
    ///
    /// Shared fields are unified. Each side's unique fields are collected,
    /// and fresh row variables are created for the remainders.
    fn unify_open_records(
        &mut self,
        a_fields: &[(NameId, TirType)],
        a_row: u32,
        b_fields: &[(NameId, TirType)],
        b_row: u32,
        location: Option<&str>,
    ) -> Result<(), TypeError> {
        let a_ids: HashSet<NameId> = a_fields.iter().map(|(id, _)| *id).collect();
        let b_ids: HashSet<NameId> = b_fields.iter().map(|(id, _)| *id).collect();

        // Unify shared fields.
        for (id, a_ty) in a_fields {
            if let Some((_, b_ty)) = b_fields.iter().find(|(bid, _)| *bid == *id) {
                self.unify(a_ty, b_ty, location)?;
            }
        }

        // Fields only in b: a's row must include them.
        let b_only: Vec<(NameId, TirType)> = b_fields
            .iter()
            .filter(|(id, _)| !a_ids.contains(id))
            .cloned()
            .collect();

        // Fields only in a: b's row must include them.
        let a_only: Vec<(NameId, TirType)> = a_fields
            .iter()
            .filter(|(id, _)| !b_ids.contains(id))
            .cloned()
            .collect();

        // Create a fresh row variable for the shared remainder.
        let fresh_row = self.fresh_var();
        let fresh_row_id = match fresh_row {
            TirType::Var(id) => id,
            _ => unreachable!(),
        };

        // a_row = b_only ++ fresh_row
        if b_only.is_empty() {
            self.bind(a_row, &fresh_row, location)?;
        } else {
            self.bind(a_row, &TirType::OpenRecord(b_only, fresh_row_id), location)?;
        }

        // b_row = a_only ++ fresh_row
        if a_only.is_empty() {
            self.bind(b_row, &fresh_row, location)?;
        } else {
            self.bind(b_row, &TirType::OpenRecord(a_only, fresh_row_id), location)?;
        }

        Ok(())
    }

    /// Unify variant types: same tags, unify payloads.
    fn unify_variants(
        &mut self,
        a_cases: &[(String, TirType)],
        b_cases: &[(String, TirType)],
        location: Option<&str>,
    ) -> Result<(), TypeError> {
        for (a_tag, a_ty) in a_cases {
            if let Some((_, b_ty)) = b_cases.iter().find(|(bt, _)| bt == a_tag) {
                self.unify(a_ty, b_ty, location)?;
            } else {
                let err = TypeError {
                    message: format!("variant tag `{}` not found in other variant type", a_tag),
                    location: location.map(String::from),
                };
                self.errors.push(err.clone());
                return Err(err);
            }
        }
        Ok(())
    }

    /// Replace type variables according to a mapping (used by `instantiate`).
    fn substitute_vars(&self, ty: &TirType, mapping: &HashMap<u32, TirType>) -> TirType {
        match ty {
            TirType::Var(id) => {
                if let Some(replacement) = mapping.get(id) {
                    replacement.clone()
                } else {
                    ty.clone()
                }
            }
            TirType::Set(inner) => TirType::Set(Box::new(self.substitute_vars(inner, mapping))),
            TirType::Seq(inner) => TirType::Seq(Box::new(self.substitute_vars(inner, mapping))),
            TirType::Func(d, r) => TirType::Func(
                Box::new(self.substitute_vars(d, mapping)),
                Box::new(self.substitute_vars(r, mapping)),
            ),
            TirType::Tuple(elems) => TirType::Tuple(
                elems
                    .iter()
                    .map(|e| self.substitute_vars(e, mapping))
                    .collect(),
            ),
            TirType::Record(fields) => TirType::Record(
                fields
                    .iter()
                    .map(|(id, ty)| (*id, self.substitute_vars(ty, mapping)))
                    .collect(),
            ),
            TirType::OpenRecord(fields, row) => {
                let new_fields: Vec<(NameId, TirType)> = fields
                    .iter()
                    .map(|(id, ty)| (*id, self.substitute_vars(ty, mapping)))
                    .collect();
                // If the row variable itself is in the mapping, replace it.
                if let Some(TirType::Var(new_row)) = mapping.get(row) {
                    TirType::OpenRecord(new_fields, *new_row)
                } else {
                    TirType::OpenRecord(new_fields, *row)
                }
            }
            TirType::Variant(cases) => TirType::Variant(
                cases
                    .iter()
                    .map(|(tag, ty)| (tag.clone(), self.substitute_vars(ty, mapping)))
                    .collect(),
            ),
            TirType::Bool | TirType::Int | TirType::Str | TirType::Dyn => ty.clone(),
        }
    }
}

impl Default for TypeUnifier {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::intern_name;

    #[test]
    fn test_unify_same_types() {
        let mut u = TypeUnifier::new();
        assert!(u.unify(&TirType::Int, &TirType::Int, None).is_ok());
        assert!(u.unify(&TirType::Bool, &TirType::Bool, None).is_ok());
        assert!(u.unify(&TirType::Str, &TirType::Str, None).is_ok());
        assert!(u.unify(&TirType::Dyn, &TirType::Dyn, None).is_ok());
    }

    #[test]
    fn test_unify_var_with_concrete() {
        let mut u = TypeUnifier::new();
        let v = u.fresh_var();
        assert!(u.unify(&v, &TirType::Int, None).is_ok());
        assert_eq!(u.resolve(&v), TirType::Int);
    }

    #[test]
    fn test_unify_var_both_sides() {
        let mut u = TypeUnifier::new();
        let v1 = u.fresh_var();
        let v2 = u.fresh_var();
        assert!(u.unify(&v1, &v2, None).is_ok());
        // After unifying two vars, binding one should resolve the other.
        assert!(u.unify(&v2, &TirType::Bool, None).is_ok());
        assert_eq!(u.resolve(&v1), TirType::Bool);
        assert_eq!(u.resolve(&v2), TirType::Bool);
    }

    #[test]
    fn test_unify_occurs_check_fails() {
        let mut u = TypeUnifier::new();
        let v = u.fresh_var();
        // t0 = Set(t0) should fail (infinite type).
        let set_v = TirType::Set(Box::new(v.clone()));
        assert!(u.unify(&v, &set_v, None).is_err());
        assert!(u.has_errors());
    }

    #[test]
    fn test_unify_set_recursive() {
        let mut u = TypeUnifier::new();
        let v = u.fresh_var();
        let set_v = TirType::Set(Box::new(v.clone()));
        let set_int = TirType::Set(Box::new(TirType::Int));
        assert!(u.unify(&set_v, &set_int, None).is_ok());
        assert_eq!(u.resolve(&v), TirType::Int);
        assert_eq!(u.resolve(&set_v), TirType::Set(Box::new(TirType::Int)));
    }

    #[test]
    fn test_unify_func_types() {
        let mut u = TypeUnifier::new();
        let v1 = u.fresh_var();
        let v2 = u.fresh_var();
        let f1 = TirType::Func(Box::new(v1.clone()), Box::new(v2.clone()));
        let f2 = TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool));
        assert!(u.unify(&f1, &f2, None).is_ok());
        assert_eq!(u.resolve(&v1), TirType::Int);
        assert_eq!(u.resolve(&v2), TirType::Bool);
    }

    #[test]
    fn test_unify_record_types() {
        let mut u = TypeUnifier::new();
        let id_x = intern_name("x");
        let id_y = intern_name("y");
        let v = u.fresh_var();
        let r1 = TirType::Record(vec![(id_x, TirType::Int), (id_y, v.clone())]);
        let r2 = TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Bool)]);
        assert!(u.unify(&r1, &r2, None).is_ok());
        assert_eq!(u.resolve(&v), TirType::Bool);
    }

    #[test]
    fn test_unify_record_field_mismatch() {
        let mut u = TypeUnifier::new();
        let id_x = intern_name("x");
        let id_y = intern_name("y");
        let id_z = intern_name("z");
        let r1 = TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Bool)]);
        let r2 = TirType::Record(vec![(id_x, TirType::Int), (id_z, TirType::Bool)]);
        assert!(u.unify(&r1, &r2, None).is_err());
    }

    #[test]
    fn test_unify_open_record_with_closed() {
        let mut u = TypeUnifier::new();
        let id_x = intern_name("x");
        let id_y = intern_name("y");
        let row = match u.fresh_var() {
            TirType::Var(id) => id,
            _ => unreachable!(),
        };
        // { x: Int, ...row } unified with { x: Int, y: Bool }
        let open = TirType::OpenRecord(vec![(id_x, TirType::Int)], row);
        let closed = TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Bool)]);
        assert!(u.unify(&open, &closed, None).is_ok());

        // The row variable should be bound to { y: Bool }.
        let resolved = u.resolve(&TirType::Var(row));
        assert_eq!(resolved, TirType::Record(vec![(id_y, TirType::Bool)]));

        // The full open record should resolve to the closed record.
        let full = u.resolve(&open);
        assert_eq!(
            full,
            TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Bool)])
        );
    }

    #[test]
    fn test_unify_variant_types() {
        let mut u = TypeUnifier::new();
        let v = u.fresh_var();
        let var1 = TirType::Variant(vec![
            ("Some".to_string(), v.clone()),
            ("None".to_string(), TirType::Bool),
        ]);
        let var2 = TirType::Variant(vec![
            ("Some".to_string(), TirType::Int),
            ("None".to_string(), TirType::Bool),
        ]);
        assert!(u.unify(&var1, &var2, None).is_ok());
        assert_eq!(u.resolve(&v), TirType::Int);
    }

    #[test]
    fn test_unify_variant_tag_mismatch() {
        let mut u = TypeUnifier::new();
        let var1 = TirType::Variant(vec![("A".to_string(), TirType::Int)]);
        let var2 = TirType::Variant(vec![("B".to_string(), TirType::Int)]);
        assert!(u.unify(&var1, &var2, None).is_err());
    }

    #[test]
    fn test_generalize_and_instantiate() {
        let mut u = TypeUnifier::new();
        let v = u.fresh_var(); // t0

        // Type: Set(t0) -> t0  (the "pick element from set" signature)
        let ty = TirType::Func(
            Box::new(TirType::Set(Box::new(v.clone()))),
            Box::new(v.clone()),
        );

        // Generalize with empty environment: t0 should be quantified.
        let scheme = u.generalize(&ty, &HashSet::new());
        assert_eq!(scheme.forall.len(), 1);
        assert!(scheme.forall.contains(&0));

        // Instantiate: should produce a fresh variable, not t0.
        let inst = u.instantiate(&scheme);
        match &inst {
            TirType::Func(dom, rng) => {
                // Both should reference the same NEW variable (t1).
                match (dom.as_ref(), rng.as_ref()) {
                    (TirType::Set(inner), rng_ty) => {
                        assert_eq!(inner.as_ref(), rng_ty);
                        assert!(matches!(rng_ty, TirType::Var(id) if *id != 0));
                    }
                    _ => panic!("expected Set(...) -> Var(...)"),
                }
            }
            _ => panic!("expected Func type after instantiation"),
        }
    }

    #[test]
    fn test_resolve_chain() {
        let mut u = TypeUnifier::new();
        let v0 = u.fresh_var(); // t0
        let v1 = u.fresh_var(); // t1
        let v2 = u.fresh_var(); // t2

        // t0 -> t1 -> t2 -> Int
        assert!(u.unify(&v0, &v1, None).is_ok());
        assert!(u.unify(&v1, &v2, None).is_ok());
        assert!(u.unify(&v2, &TirType::Int, None).is_ok());

        assert_eq!(u.resolve(&v0), TirType::Int);
        assert_eq!(u.resolve(&v1), TirType::Int);
        assert_eq!(u.resolve(&v2), TirType::Int);
    }

    #[test]
    fn test_unify_dyn_is_wildcard() {
        let mut u = TypeUnifier::new();
        // Dyn unifies with anything without binding.
        assert!(u.unify(&TirType::Dyn, &TirType::Int, None).is_ok());
        assert!(u.unify(&TirType::Bool, &TirType::Dyn, None).is_ok());
        assert!(u.unify(&TirType::Dyn, &TirType::Dyn, None).is_ok());
    }

    #[test]
    fn test_unify_incompatible_types() {
        let mut u = TypeUnifier::new();
        assert!(u.unify(&TirType::Int, &TirType::Bool, None).is_err());
        assert!(u
            .unify(
                &TirType::Set(Box::new(TirType::Int)),
                &TirType::Seq(Box::new(TirType::Int)),
                None
            )
            .is_err());
    }

    #[test]
    fn test_unify_tuple_length_mismatch() {
        let mut u = TypeUnifier::new();
        let t1 = TirType::Tuple(vec![TirType::Int]);
        let t2 = TirType::Tuple(vec![TirType::Int, TirType::Bool]);
        assert!(u.unify(&t1, &t2, None).is_err());
    }

    #[test]
    fn test_unify_tuple_elementwise() {
        let mut u = TypeUnifier::new();
        let v = u.fresh_var();
        let t1 = TirType::Tuple(vec![TirType::Int, v.clone()]);
        let t2 = TirType::Tuple(vec![TirType::Int, TirType::Str]);
        assert!(u.unify(&t1, &t2, None).is_ok());
        assert_eq!(u.resolve(&v), TirType::Str);
    }

    #[test]
    fn test_generalize_respects_env() {
        let mut u = TypeUnifier::new();
        let v0 = u.fresh_var(); // t0
        let v1 = u.fresh_var(); // t1

        // Type: t0 -> t1
        let ty = TirType::Func(Box::new(v0.clone()), Box::new(v1.clone()));

        // Generalize with t0 in the environment: only t1 should be quantified.
        let mut env = HashSet::new();
        env.insert(0); // t0 is in scope
        let scheme = u.generalize(&ty, &env);
        assert_eq!(scheme.forall.len(), 1);
        assert!(scheme.forall.contains(&1));
        assert!(!scheme.forall.contains(&0));
    }
}
