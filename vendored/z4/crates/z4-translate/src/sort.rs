// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort translation trait.

use z4_dpll::api::Sort;

/// Trait for translating consumer sort types to z4 sorts.
pub trait SortTranslator {
    /// The consumer's sort type.
    type Sort;
    /// Error type for translation failures.
    type Error;
    /// Translate a consumer sort to a z4 sort.
    fn translate_sort(&self, sort: &Self::Sort) -> Result<Sort, Self::Error>;
}
