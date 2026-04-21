// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_core::NameId;

/// Gradual TIR type lattice.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TirType {
    Bool,
    Int,
    Str,
    Set(Box<TirType>),
    Seq(Box<TirType>),
    Func(Box<TirType>, Box<TirType>),
    Tuple(Vec<TirType>),
    Record(Vec<(NameId, TirType)>),
    /// Type variable for unification (Snowcat parity).
    Var(u32),
    /// Open record with known fields and a row variable for extension.
    /// The `u32` is the row variable id — unification can bind it to remaining fields.
    OpenRecord(Vec<(NameId, TirType)>, u32),
    /// Tagged union / sum type (Snowcat `Variant` parity).
    /// Each entry is `(tag_name, payload_type)`.
    Variant(Vec<(String, TirType)>),
    Dyn,
}

impl TirType {
    /// Compute the join (least upper bound) of two types in the gradual lattice.
    ///
    /// `Dyn` acts as both top and bottom: it is compatible with everything.
    /// `Var` acts like `Dyn` in join — it is a wildcard until resolved by unification.
    /// When both sides are concrete but different, the result is `Dyn`.
    #[must_use]
    pub fn join(&self, other: &TirType) -> TirType {
        if *self == TirType::Dyn || matches!(self, TirType::Var(_)) {
            return other.clone();
        }
        if *other == TirType::Dyn || matches!(other, TirType::Var(_)) {
            return self.clone();
        }
        if self == other {
            return self.clone();
        }
        match (self, other) {
            (TirType::Set(a), TirType::Set(b)) => TirType::Set(Box::new(a.join(b))),
            (TirType::Seq(a), TirType::Seq(b)) => TirType::Seq(Box::new(a.join(b))),
            (TirType::Func(ad, ar), TirType::Func(bd, br)) => {
                TirType::Func(Box::new(ad.join(bd)), Box::new(ar.join(br)))
            }
            (TirType::Tuple(a), TirType::Tuple(b)) if a.len() == b.len() => {
                TirType::Tuple(a.iter().zip(b.iter()).map(|(x, y)| x.join(y)).collect())
            }
            (TirType::Record(a), TirType::Record(b)) if a.len() == b.len() => {
                // Join record types field-by-field when they have the same fields.
                let joined: Option<Vec<(NameId, TirType)>> = a
                    .iter()
                    .map(|(id, ty_a)| {
                        b.iter()
                            .find(|(bid, _)| *bid == *id)
                            .map(|(_, ty_b)| (*id, ty_a.join(ty_b)))
                    })
                    .collect();
                joined.map_or(TirType::Dyn, TirType::Record)
            }
            // OpenRecord joins: promote to closed Record if fields match
            (TirType::OpenRecord(a, _), TirType::Record(b))
            | (TirType::Record(b), TirType::OpenRecord(a, _)) => {
                // Join known fields; extra fields from the closed side stay
                let joined: Option<Vec<(NameId, TirType)>> = b
                    .iter()
                    .map(|(id, ty_b)| {
                        let ty_a = a
                            .iter()
                            .find(|(aid, _)| *aid == *id)
                            .map(|(_, t)| t.join(ty_b))
                            .unwrap_or_else(|| ty_b.clone());
                        Some((*id, ty_a))
                    })
                    .collect();
                joined.map_or(TirType::Dyn, TirType::Record)
            }
            (TirType::OpenRecord(a, _), TirType::OpenRecord(b, row)) => {
                // Merge fields from both sides, join shared fields
                let mut merged: Vec<(NameId, TirType)> = Vec::new();
                for (id, ty_a) in a {
                    let ty = b
                        .iter()
                        .find(|(bid, _)| *bid == *id)
                        .map(|(_, ty_b)| ty_a.join(ty_b))
                        .unwrap_or_else(|| ty_a.clone());
                    merged.push((*id, ty));
                }
                for (id, ty_b) in b {
                    if !a.iter().any(|(aid, _)| *aid == *id) {
                        merged.push((*id, ty_b.clone()));
                    }
                }
                TirType::OpenRecord(merged, *row)
            }
            // Variant joins: merge tags, join shared payload types
            (TirType::Variant(a), TirType::Variant(b)) => {
                let mut merged: Vec<(String, TirType)> = Vec::new();
                for (tag, ty_a) in a {
                    let ty = b
                        .iter()
                        .find(|(bt, _)| *bt == *tag)
                        .map(|(_, ty_b)| ty_a.join(ty_b))
                        .unwrap_or_else(|| ty_a.clone());
                    merged.push((tag.clone(), ty));
                }
                for (tag, ty_b) in b {
                    if !a.iter().any(|(at, _)| *at == *tag) {
                        merged.push((tag.clone(), ty_b.clone()));
                    }
                }
                TirType::Variant(merged)
            }
            _ => TirType::Dyn,
        }
    }

    /// Extract the element type from a set type.
    ///
    /// Returns `None` if this is not a `Set(...)`.
    #[must_use]
    pub fn set_element(&self) -> Option<&TirType> {
        match self {
            TirType::Set(inner) => Some(inner),
            _ => None,
        }
    }

    /// Extract the element type from a sequence type.
    ///
    /// Returns `None` if this is not a `Seq(...)`.
    #[must_use]
    pub fn seq_element(&self) -> Option<&TirType> {
        match self {
            TirType::Seq(inner) => Some(inner),
            _ => None,
        }
    }

    /// Extract domain and range from a function type.
    ///
    /// Returns `None` if this is not a `Func(...)`.
    #[must_use]
    pub fn func_parts(&self) -> Option<(&TirType, &TirType)> {
        match self {
            TirType::Func(d, r) => Some((d, r)),
            _ => None,
        }
    }

    /// Returns `true` if this type is fully resolved (contains no `Dyn` or `Var`).
    #[must_use]
    pub fn is_concrete(&self) -> bool {
        match self {
            TirType::Dyn | TirType::Var(_) => false,
            TirType::Bool | TirType::Int | TirType::Str => true,
            TirType::Set(inner) | TirType::Seq(inner) => inner.is_concrete(),
            TirType::Func(d, r) => d.is_concrete() && r.is_concrete(),
            TirType::Tuple(elems) => elems.iter().all(|e| e.is_concrete()),
            TirType::Record(fields) => fields.iter().all(|(_, t)| t.is_concrete()),
            TirType::OpenRecord(_, _) => false, // row variable means not fully resolved
            TirType::Variant(cases) => cases.iter().all(|(_, t)| t.is_concrete()),
        }
    }

    /// Collect all free type variable ids in this type.
    #[must_use]
    pub fn free_vars(&self) -> std::collections::HashSet<u32> {
        let mut vars = std::collections::HashSet::new();
        self.collect_free_vars(&mut vars);
        vars
    }

    fn collect_free_vars(&self, vars: &mut std::collections::HashSet<u32>) {
        match self {
            TirType::Var(id) => {
                vars.insert(*id);
            }
            TirType::Set(inner) | TirType::Seq(inner) => inner.collect_free_vars(vars),
            TirType::Func(d, r) => {
                d.collect_free_vars(vars);
                r.collect_free_vars(vars);
            }
            TirType::Tuple(elems) => {
                for e in elems {
                    e.collect_free_vars(vars);
                }
            }
            TirType::Record(fields) => {
                for (_, t) in fields {
                    t.collect_free_vars(vars);
                }
            }
            TirType::OpenRecord(fields, row) => {
                for (_, t) in fields {
                    t.collect_free_vars(vars);
                }
                vars.insert(*row);
            }
            TirType::Variant(cases) => {
                for (_, t) in cases {
                    t.collect_free_vars(vars);
                }
            }
            TirType::Bool | TirType::Int | TirType::Str | TirType::Dyn => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::intern_name;

    #[test]
    fn test_join_dyn_absorbs() {
        assert_eq!(TirType::Dyn.join(&TirType::Int), TirType::Int);
        assert_eq!(TirType::Int.join(&TirType::Dyn), TirType::Int);
        assert_eq!(TirType::Dyn.join(&TirType::Dyn), TirType::Dyn);
    }

    #[test]
    fn test_join_same_type() {
        assert_eq!(TirType::Bool.join(&TirType::Bool), TirType::Bool);
        assert_eq!(TirType::Int.join(&TirType::Int), TirType::Int);
    }

    #[test]
    fn test_join_different_base_is_dyn() {
        assert_eq!(TirType::Bool.join(&TirType::Int), TirType::Dyn);
        assert_eq!(TirType::Str.join(&TirType::Bool), TirType::Dyn);
    }

    #[test]
    fn test_join_set_recursive() {
        let set_int = TirType::Set(Box::new(TirType::Int));
        let set_dyn = TirType::Set(Box::new(TirType::Dyn));
        assert_eq!(set_int.join(&set_dyn), TirType::Set(Box::new(TirType::Int)));
        assert_eq!(set_dyn.join(&set_int), TirType::Set(Box::new(TirType::Int)));
    }

    #[test]
    fn test_join_set_incompatible_element() {
        let set_int = TirType::Set(Box::new(TirType::Int));
        let set_bool = TirType::Set(Box::new(TirType::Bool));
        assert_eq!(
            set_int.join(&set_bool),
            TirType::Set(Box::new(TirType::Dyn))
        );
    }

    #[test]
    fn test_join_func() {
        let f1 = TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool));
        let f2 = TirType::Func(Box::new(TirType::Int), Box::new(TirType::Dyn));
        assert_eq!(
            f1.join(&f2),
            TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool))
        );
    }

    #[test]
    fn test_join_tuple() {
        let t1 = TirType::Tuple(vec![TirType::Int, TirType::Dyn]);
        let t2 = TirType::Tuple(vec![TirType::Dyn, TirType::Bool]);
        assert_eq!(
            t1.join(&t2),
            TirType::Tuple(vec![TirType::Int, TirType::Bool])
        );
    }

    #[test]
    fn test_join_tuple_length_mismatch() {
        let t1 = TirType::Tuple(vec![TirType::Int]);
        let t2 = TirType::Tuple(vec![TirType::Int, TirType::Bool]);
        assert_eq!(t1.join(&t2), TirType::Dyn);
    }

    #[test]
    fn test_join_record() {
        let id_x = intern_name("x");
        let id_y = intern_name("y");
        let r1 = TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Dyn)]);
        let r2 = TirType::Record(vec![(id_x, TirType::Dyn), (id_y, TirType::Bool)]);
        assert_eq!(
            r1.join(&r2),
            TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Bool)])
        );
    }

    #[test]
    fn test_set_element() {
        assert_eq!(
            TirType::Set(Box::new(TirType::Int)).set_element(),
            Some(&TirType::Int)
        );
        assert_eq!(TirType::Int.set_element(), None);
    }

    #[test]
    fn test_seq_element() {
        assert_eq!(
            TirType::Seq(Box::new(TirType::Str)).seq_element(),
            Some(&TirType::Str)
        );
        assert_eq!(TirType::Bool.seq_element(), None);
    }

    #[test]
    fn test_func_parts() {
        let f = TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool));
        assert_eq!(f.func_parts(), Some((&TirType::Int, &TirType::Bool)));
        assert_eq!(TirType::Dyn.func_parts(), None);
    }

    #[test]
    fn test_is_concrete() {
        assert!(TirType::Int.is_concrete());
        assert!(TirType::Bool.is_concrete());
        assert!(!TirType::Dyn.is_concrete());
        assert!(TirType::Set(Box::new(TirType::Int)).is_concrete());
        assert!(!TirType::Set(Box::new(TirType::Dyn)).is_concrete());
        assert!(TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool)).is_concrete());
        assert!(!TirType::Func(Box::new(TirType::Dyn), Box::new(TirType::Bool)).is_concrete());
        assert!(TirType::Tuple(vec![TirType::Int, TirType::Bool]).is_concrete());
        assert!(!TirType::Tuple(vec![TirType::Int, TirType::Dyn]).is_concrete());
    }
}
