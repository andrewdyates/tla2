// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compound set types: SubsetValue (powerset), FuncSetValue, RecordSetValue,
//! TupleSetValue, and KSubsetValue, with their iterators and trait impls.
//!
//! Extracted from `value/mod.rs` as part of #1398 decomposition.
//! Split into per-type modules as part of #1614.

mod func_set;
mod k_subset;
mod record_set;
mod subset;
mod tuple_set;

pub(crate) use func_set::FuncSetIterator;
pub use func_set::FuncSetValue;
#[cfg(test)]
pub(super) use k_subset::binomial;
pub(crate) use k_subset::KSubsetIterator;
pub use k_subset::KSubsetValue;
pub(crate) use record_set::RecordSetOwnedIterator;
pub use record_set::RecordSetValue;
pub(crate) use subset::SubsetIterator;
pub use subset::SubsetValue;
pub(crate) use tuple_set::TupleSetOwnedIterator;
pub use tuple_set::TupleSetValue;
