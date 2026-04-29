// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FuncSetValue (function set [S -> T]) and FuncSetIterator.
//!
//! Split into per-concern modules as part of #3450.

mod iterator;
mod membership;
mod traits;

pub(crate) use iterator::FuncSetIterator;

use super::super::*;

debug_flag!(debug_funcset, "TLA2_DEBUG_FUNCSET");

/// A lazy function set value representing [S -> T] without allocating all |T|^|S| functions
///
/// This is a performance optimization for large function sets.
/// Membership check: f \in [S -> T] <==> f is a function with DOMAIN f = S and range(f) \subseteq T
#[derive(Clone, Debug)]
pub struct FuncSetValue {
    /// The domain set S
    pub(crate) domain: Box<Value>,
    /// The codomain set T
    pub(crate) codomain: Box<Value>,
}

impl FuncSetValue {
    /// Create a new function set [domain -> codomain]
    pub fn new(domain: Value, codomain: Value) -> Self {
        FuncSetValue {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    pub fn domain(&self) -> &Value {
        &self.domain
    }

    pub fn codomain(&self) -> &Value {
        &self.codomain
    }

    /// Materialize to a SortedSet via direct iteration.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        let iter = self.iter()?;
        Some(SortedSet::from_iter(iter))
    }

    /// Iterate over all functions in the function set
    pub(crate) fn iter(&self) -> Option<impl Iterator<Item = Value> + '_> {
        let domain_sorted = self.domain.to_sorted_set()?;
        let codomain_sorted = self.codomain.to_sorted_set()?;
        Some(FuncSetIterator::from_elems(
            domain_sorted.iter().cloned().collect(),
            codomain_sorted.iter().cloned().collect(),
        ))
    }
}
