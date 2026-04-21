// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term creation (builder) methods for [`TermStore`].
//!
//! Extracted from `mod.rs` — contains `intern`, all `mk_*` constructors,
//! and `is_quantifier`.

use std::mem::size_of;
use std::sync::atomic::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

use crate::sort::Sort;

use super::{Constant, Symbol, TermData, TermEntry, TermId, TermStore, GLOBAL_TERM_BYTES};

impl TermStore {
    /// Internal: find or create a term
    pub(super) fn intern(&mut self, term: TermData, sort: Sort) -> TermId {
        let hash = Self::compute_hash(&term);

        // Check if we already have this term
        if let Some(ids) = self.hash_cons.get(&hash) {
            for &id in ids {
                if self.terms[id.index()].term == term {
                    debug_assert!(
                        self.terms[id.index()].sort == sort,
                        "BUG #6734: intern sort mismatch — existing {:?} vs requested {:?} for {:?}",
                        self.terms[id.index()].sort,
                        sort,
                        self.terms[id.index()].term
                    );
                    return id;
                }
            }
        }

        // Track approximate memory usage across all TermStore instances (#2769).
        // size_of::<TermEntry>() captures the inline struct size. Heap allocations
        // within TermData (Vec<TermId> children, String constants) are not counted,
        // so actual usage is higher than reported.
        let entry_size = size_of::<TermEntry>();
        GLOBAL_TERM_BYTES.fetch_add(entry_size, Ordering::Relaxed);
        self.instance_term_bytes += entry_size;

        // Create new term
        let id = TermId(self.terms.len() as u32);
        self.terms.push(TermEntry { term, sort });
        self.hash_cons.entry(hash).or_default().push(id);
        id
    }

    /// Create a boolean constant
    pub fn mk_bool(&mut self, value: bool) -> TermId {
        self.intern(TermData::Const(Constant::Bool(value)), Sort::Bool)
    }

    /// Create an integer constant
    pub fn mk_int(&mut self, value: BigInt) -> TermId {
        self.intern(TermData::Const(Constant::Int(value)), Sort::Int)
    }

    /// Create a rational constant
    pub fn mk_rational(&mut self, value: BigRational) -> TermId {
        self.intern(
            TermData::Const(Constant::Rational(value.into())),
            Sort::Real,
        )
    }

    /// Create a bitvector constant
    ///
    /// The value is normalized to the canonical unsigned representation
    /// (0 to 2^width - 1) so that `mk_bitvec(-128, 8)` and `mk_bitvec(128, 8)`
    /// produce the same interned constant (both represent 0x80).
    pub fn mk_bitvec(&mut self, value: BigInt, width: u32) -> TermId {
        // Normalize to unsigned representation: value mod 2^width
        // This ensures -128 and 128 both become 128 for 8-bit bitvectors.
        let modulus = BigInt::one() << width;
        let normalized = ((value % &modulus) + &modulus) % &modulus;
        self.intern(
            TermData::Const(Constant::BitVec {
                value: normalized,
                width,
            }),
            Sort::bitvec(width),
        )
    }

    /// Create a string constant
    pub fn mk_string(&mut self, value: String) -> TermId {
        self.intern(TermData::Const(Constant::String(value)), Sort::String)
    }

    /// Create or get a variable by name
    pub fn mk_var(&mut self, name: impl Into<String>, sort: Sort) -> TermId {
        let name = name.into();

        // Check if we already have this variable
        if let Some(&(id, _)) = self.names.get(&name) {
            return id;
        }

        let var_id = self.var_counter;
        self.var_counter += 1;

        let id = self.intern(TermData::Var(name.clone(), var_id), sort.clone());
        self.names.insert(name, (id, sort));
        id
    }

    /// Create a fresh variable while preserving the visible symbol name.
    ///
    /// SMT-LIB allows a symbol name to be declared again after the declaring
    /// scope has been popped. Those redeclarations must get a fresh internal
    /// identity even though the user-facing name is unchanged; otherwise
    /// incremental solvers can accidentally alias stale scoped state to the
    /// new declaration.
    pub fn mk_fresh_named_var(&mut self, name: impl Into<String>, sort: Sort) -> TermId {
        let name = name.into();
        let var_id = self.var_counter;
        self.var_counter += 1;

        let id = self.intern(TermData::Var(name.clone(), var_id), sort.clone());
        self.names.insert(name, (id, sort));
        id
    }

    /// Create a fresh variable (guaranteed unique)
    pub fn mk_fresh_var(&mut self, prefix: &str, sort: Sort) -> TermId {
        loop {
            let var_id = self.var_counter;
            self.var_counter += 1;

            let name = format!("{prefix}_{var_id}");
            if self.names.contains_key(name.as_str()) {
                continue;
            }

            return self.intern(TermData::Var(name, var_id), sort);
        }
    }

    /// Create an internal symbol name guaranteed not to collide with user symbols.
    ///
    /// Uses format: `__z4_<purpose>!<id>` where id is monotonically increasing.
    /// The `!` separator follows Z3's fresh symbol convention.
    ///
    /// # Arguments
    /// * `purpose` - Descriptive tag (e.g., "dt_depth", "mbc")
    ///
    /// # Returns
    /// A unique symbol name that will never collide with user declarations
    /// (since user symbols starting with `__z4_` are rejected by the frontend).
    #[must_use]
    pub fn mk_internal_symbol(&mut self, purpose: &str) -> String {
        let id = self.var_counter;
        self.var_counter += 1;
        format!("__z4_{purpose}!{id}")
    }

    /// Create a function application
    pub fn mk_app(&mut self, func: Symbol, args: Vec<TermId>, sort: Sort) -> TermId {
        self.intern(TermData::App(func, args), sort)
    }

    /// Create a universal quantifier: forall ((x1 S1) ...) body
    pub fn mk_forall(&mut self, vars: Vec<(String, Sort)>, body: TermId) -> TermId {
        self.mk_forall_with_triggers(vars, body, Vec::new())
    }

    /// Create a universal quantifier with explicit user triggers.
    pub fn mk_forall_with_triggers(
        &mut self,
        vars: Vec<(String, Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
    ) -> TermId {
        debug_assert!(
            self.sort(body) == &Sort::Bool,
            "BUG: mk_forall body must be Bool, got {:?}",
            self.sort(body)
        );
        self.intern(TermData::Forall(vars, body, triggers), Sort::Bool)
    }

    /// Create an existential quantifier: exists ((x1 S1) ...) body
    pub fn mk_exists(&mut self, vars: Vec<(String, Sort)>, body: TermId) -> TermId {
        self.mk_exists_with_triggers(vars, body, Vec::new())
    }

    /// Create an existential quantifier with explicit user triggers.
    pub fn mk_exists_with_triggers(
        &mut self,
        vars: Vec<(String, Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
    ) -> TermId {
        debug_assert!(
            self.sort(body) == &Sort::Bool,
            "BUG: mk_exists body must be Bool, got {:?}",
            self.sort(body)
        );
        self.intern(TermData::Exists(vars, body, triggers), Sort::Bool)
    }

    /// Create a let binding: (let ((x1 t1) ...) body)
    ///
    /// The sort of a let expression is the sort of its body.
    pub fn mk_let(&mut self, bindings: Vec<(String, TermId)>, body: TermId) -> TermId {
        let body_sort = self.sort(body).clone();
        self.intern(TermData::Let(bindings, body), body_sort)
    }

    /// Check if a term is a quantifier
    pub fn is_quantifier(&self, term: TermId) -> bool {
        matches!(
            self.get(term),
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _)
        )
    }
}
