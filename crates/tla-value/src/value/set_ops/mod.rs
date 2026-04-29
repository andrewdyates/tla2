// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy set operation types: union, intersection, difference, sequence sets,
//! big union, and set filter (SetPred).
//!
//! Originally a single 1155-line file; decomposed into focused submodules:
//! - `set_binary_ops`: SetCupValue, SetCapValue, SetDiffValue
//! - `set_compound_ops`: SeqSetValue, UnionValue
//! - `set_pred`: SetPredValue, SetPredIdentity, SetPredIdentityVisitor

mod cached_bound_names;
mod set_binary_ops;
mod set_compound_ops;
mod set_pred;
mod span_normalize;

pub use set_binary_ops::{SetCapValue, SetCupValue, SetDiffValue};
pub use set_compound_ops::{SeqSetValue, UnionValue};
pub use set_pred::{SetPredCaptures, SetPredIdentity, SetPredIdentityVisitor, SetPredValue};
