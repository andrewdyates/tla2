// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Domain types for lazy function values.
//!
//! `ComponentDomain` describes the domain of a single component in a lazy function's
//! domain space. `LazyDomain` combines these into the overall domain descriptor.

use super::super::{SortedSet, Value};
use num_bigint::BigInt;
use num_traits::Zero;

/// Domain type for a single component of a lazy function's domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComponentDomain {
    Nat,
    Int,
    Real,
    String,
    Finite(SortedSet),
}

impl ComponentDomain {
    /// Check if a value is in this component domain
    pub fn contains(&self, v: &Value) -> bool {
        match self {
            ComponentDomain::Nat => match v {
                Value::SmallInt(n) => *n >= 0,
                Value::Int(n) => **n >= BigInt::zero(),
                _ => false,
            },
            ComponentDomain::Int => matches!(v, Value::SmallInt(_) | Value::Int(_)),
            ComponentDomain::Real => matches!(v, Value::SmallInt(_) | Value::Int(_)), // Int ⊆ Real
            ComponentDomain::String => matches!(v, Value::String(_)),
            ComponentDomain::Finite(s) => s.contains(v),
        }
    }

    /// Check if this domain is infinite
    pub fn is_infinite(&self) -> bool {
        matches!(
            self,
            ComponentDomain::Nat
                | ComponentDomain::Int
                | ComponentDomain::Real
                | ComponentDomain::String
        )
    }
}

/// Domain marker for lazy functions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LazyDomain {
    Nat,
    Int,
    Real,                          // Int ⊆ Real, TLC doesn't support actual reals
    String,                        // The set of all strings
    Product(Vec<ComponentDomain>), // Cartesian product of component domains
    /// General domain represented as an arbitrary set-like Value.
    /// Used for domains like SUBSET Int, [S -> T], etc.
    /// Membership is checked via Value::contains.
    General(Box<Value>),
}
