// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared trait for lazy/unenumerated set types.
//!
//! Eliminates duplicated `to_sorted_set`, `set_len`, and `set_iter`
//! implementations across 11 lazy set types. See designs/2026-02-07-value-set-trait.md.
//!
//! Split into child modules by family (#3438):
//! - `trait_api`: shared `LazySet` trait and default helpers
//! - `finite`: finite delegating families (IntervalValue, SubsetValue, etc.)
//! - `binary`: binary lazy-set wrappers (SetCupValue, SetCapValue, SetDiffValue)
//! - `compound`: compound special cases (UnionValue, SeqSetValue)

mod binary;
mod compound;
mod finite;
mod trait_api;

pub(crate) use trait_api::LazySet;
