// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use super::FuncValue;
use std::cmp::Ordering;
use std::sync::Arc;

impl FuncValue {
    /// Check if two FuncValues share the same domain and values buffers
    /// and neither has an overlay.
    /// Part of #3371: With overlays, matching Arcs alone doesn't guarantee equality.
    #[inline]
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.domain, &other.domain)
            && Arc::ptr_eq(&self.values, &other.values)
            && self.overrides.is_none()
            && other.overrides.is_none()
    }

    /// Compose two permutations: (self ∘ other)(x) = self(other(x))
    ///
    /// For symmetry reduction, we need to compose permutations to compute
    /// the group closure. If permutations operate on disjoint domains
    /// (e.g., Permutations(A) ∪ Permutations(B)), the composition combines
    /// both mappings.
    ///
    /// Returns a new permutation that is the composition of self and other.
    pub fn compose_perm(&self, other: &FuncValue) -> FuncValue {
        if self.domain_is_empty() {
            return other.clone();
        }
        if other.domain_is_empty() {
            return self.clone();
        }

        let mut entries = Vec::with_capacity(self.domain_len() + other.domain_len());
        let mut self_idx = 0;
        let mut other_idx = 0;

        let compose_other_entry = |key: &Value, value: &Value| {
            let final_value = self.apply(value).cloned().unwrap_or_else(|| value.clone());
            (key.clone(), final_value)
        };

        while self_idx < self.domain.len() && other_idx < other.domain.len() {
            let self_key = &self.domain[self_idx];
            let self_value = self.get_value_at(self_idx);
            let other_key = &other.domain[other_idx];
            let other_value = other.get_value_at(other_idx);
            match self_key.cmp(other_key) {
                Ordering::Less => {
                    entries.push((self_key.clone(), self_value.clone()));
                    self_idx += 1;
                }
                Ordering::Equal => {
                    entries.push(compose_other_entry(other_key, other_value));
                    self_idx += 1;
                    other_idx += 1;
                }
                Ordering::Greater => {
                    entries.push(compose_other_entry(other_key, other_value));
                    other_idx += 1;
                }
            }
        }

        for idx in other_idx..other.domain.len() {
            entries.push(compose_other_entry(
                &other.domain[idx],
                other.get_value_at(idx),
            ));
        }
        for idx in self_idx..self.domain.len() {
            entries.push((self.domain[idx].clone(), self.get_value_at(idx).clone()));
        }

        FuncValue::from_sorted_entries(entries)
    }
}

impl Ord for FuncValue {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.ptr_eq(other) {
            return Ordering::Equal;
        }

        for ((self_key, self_value), (other_key, other_value)) in self.iter().zip(other.iter()) {
            let key_cmp = self_key.cmp(other_key);
            if key_cmp != Ordering::Equal {
                return key_cmp;
            }
            let value_cmp = self_value.cmp(other_value);
            if value_cmp != Ordering::Equal {
                return value_cmp;
            }
        }

        self.domain_len().cmp(&other.domain_len())
    }
}

impl PartialOrd for FuncValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for FuncValue {
    fn eq(&self, other: &Self) -> bool {
        self.ptr_eq(other)
            || (self.domain_len() == other.domain_len()
                && self.iter().zip(other.iter()).all(
                    |((self_key, self_value), (other_key, other_value))| {
                        self_key == other_key && self_value == other_value
                    },
                ))
    }
}

impl Eq for FuncValue {}
