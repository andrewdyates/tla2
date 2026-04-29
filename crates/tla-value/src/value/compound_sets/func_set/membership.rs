// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Membership and cardinality logic for FuncSetValue ([S -> T]).

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use super::super::super::*;
use super::{debug_funcset, FuncSetValue};

impl FuncSetValue {
    /// Check if a value is contained in this function set
    /// f \in [S -> T] iff f is a function with DOMAIN f = S and range(f) \subseteq T
    /// Returns None if codomain membership is indeterminate (e.g. SetPred codomain).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        let debug = debug_funcset();
        match v {
            Value::Func(f) => {
                // Check domain equality
                let domain_set = match self.domain.to_sorted_set() {
                    Some(s) => s,
                    None => {
                        if debug {
                            eprintln!(
                                "[FuncSetValue::contains] domain.to_sorted_set() = None, domain={:?}",
                                self.domain
                            );
                        }
                        return Some(false);
                    }
                };
                if !f.domain_eq_sorted_set(&domain_set) {
                    if debug {
                        let actual_domain =
                            SortedSet::from_sorted_vec(f.domain_iter().cloned().collect());
                        eprintln!(
                            "[FuncSetValue::contains] domain mismatch: f.domain={:?}, expected={:?}",
                            actual_domain,
                            domain_set
                        );
                    }
                    return Some(false);
                }
                // Check range subset
                for val in f.mapping_values() {
                    let contained = self.codomain.set_contains(val);
                    if debug {
                        eprintln!("[FuncSetValue::contains] checking val={:?} in codomain={:?}, result={:?}", val, self.codomain, contained);
                    }
                    if !contained? {
                        if debug {
                            eprintln!(
                                "[FuncSetValue::contains] range check failed for val={val:?}"
                            );
                        }
                        return Some(false);
                    }
                }
                Some(true)
            }
            // IntFunc is a function with integer interval domain
            Value::IntFunc(f) => {
                // O(1) domain check: function set domain must equal min..max
                if !self.domain.is_integer_interval(f.min, f.max) {
                    return Some(false);
                }
                // Check range subset: all values must be in codomain
                for val in f.values.iter() {
                    if !self.codomain.set_contains(val)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            // Tuples/Seqs are functions with domain 1..n
            Value::Tuple(elems) => {
                // O(1) domain check: domain must be 1..n
                if !self.domain.is_sequence_domain(elems.len()) {
                    return Some(false);
                }
                // Check range subset: all elements must be in codomain
                for elem in elems.iter() {
                    if !self.codomain.set_contains(elem)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            Value::Seq(seq) => {
                // O(1) domain check: domain must be 1..n
                if !self.domain.is_sequence_domain(seq.len()) {
                    return Some(false);
                }
                // Check range subset: all elements must be in codomain
                for elem in seq.iter() {
                    if !self.codomain.set_contains(elem)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            _ => Some(false),
        }
    }

    /// Get the cardinality of the function set: |T|^|S|
    pub(crate) fn len(&self) -> Option<BigInt> {
        let domain_len = self.domain.set_len()?;
        let codomain_len = self.codomain.set_len()?;
        // |T|^|S| - be careful about very large sets but use BigInt for safety
        // TLC handles this so we should too - just return the BigInt result
        if let (Some(d), Some(c)) = (domain_len.to_u32(), codomain_len.to_u64()) {
            // Limit to reasonable exponent to prevent long computation
            // 2^30 is about 1 billion, which is a reasonable upper bound
            if d <= 30 {
                Some(BigInt::from(c).pow(d))
            } else {
                None // Exponent too large
            }
        } else {
            None
        }
    }

    /// Check if the function set is empty
    #[allow(dead_code)] // LazySet-pattern consistency; called via Value dispatch
    pub(crate) fn is_empty(&self) -> bool {
        // [S -> T] is empty iff S is non-empty and T is empty
        let domain_empty = self.domain.set_len().map_or(true, |n| n.is_zero());
        let codomain_empty = self.codomain.set_len().map_or(true, |n| n.is_zero());
        !domain_empty && codomain_empty
    }
}
