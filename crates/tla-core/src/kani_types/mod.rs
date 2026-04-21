// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Andrew Yates

//! Kani-compatible collection types.
//!
//! With feature `im`, this module re-exports the real `im` collection types.
//! Without `im`, it provides std-backed stubs that preserve the functional APIs
//! used by the checker/evaluator stack.

#[cfg(feature = "im")]
pub use im::{HashMap, OrdMap, OrdSet, Vector};

#[cfg(not(feature = "im"))]
mod hash_map;
#[cfg(not(feature = "im"))]
mod ord_map;
#[cfg(not(feature = "im"))]
mod ord_set;
#[cfg(not(feature = "im"))]
mod vector;

#[cfg(not(feature = "im"))]
pub use hash_map::HashMap;
#[cfg(not(feature = "im"))]
pub use ord_map::OrdMap;
#[cfg(not(feature = "im"))]
pub use ord_set::OrdSet;
#[cfg(not(feature = "im"))]
pub use vector::Vector;
