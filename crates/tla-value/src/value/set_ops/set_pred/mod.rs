// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy set filter (`SetPredValue`): `{x \in S : P(x)}` predicate sets.
//!
//! Split into two focused submodules:
//! - `captures`: external capture bundle for construction
//! - `value`: runtime object, constructors, captured-env accessors
//! - `identity`: canonical identity types, ordering/hashing/fingerprinting
//!
//! Span normalization is in `span_normalize`. Extracted from `set_ops.rs`
//! as part of #2747, decomposed into submodules as part of #3358.

mod captures;
mod identity;
mod value;

pub use captures::SetPredCaptures;
pub use identity::{SetPredIdentity, SetPredIdentityVisitor};
pub use value::SetPredValue;
