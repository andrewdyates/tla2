// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FlattenAnd preprocessing pass
//!
//! Flattens nested AND terms into individual assertions.
//! For example:
//!   `(and (and a b) (and c d))` becomes `[a, b, c, d]`
//!
//! This simplifies downstream processing and exposes individual
//! constraints for other passes (like variable substitution).
//!
//! # Reference
//! - `reference/bitwuzla/src/preprocess/pass/flatten_and.cpp`

use super::PreprocessingPass;
#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::term::TermData;
use z4_core::{TermId, TermStore};

/// Flattens nested AND terms into individual assertions.
pub(crate) struct FlattenAnd {
    /// Cache of terms we've already processed to avoid duplicates
    processed: HashSet<TermId>,
}

impl FlattenAnd {
    /// Create a new FlattenAnd pass.
    pub(crate) fn new() -> Self {
        Self {
            processed: HashSet::new(),
        }
    }
}

impl Default for FlattenAnd {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for FlattenAnd {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let mut modified = false;
        let mut new_assertions = Vec::new();
        let mut work_stack = Vec::new();

        for &assertion in assertions.iter() {
            work_stack.push(assertion);

            while let Some(term) = work_stack.pop() {
                // Skip if already processed to avoid duplicates
                if !self.processed.insert(term) {
                    continue;
                }

                match terms.get(term) {
                    // Flatten AND: push children onto work stack
                    TermData::App(sym, args) if sym.name() == "and" && args.len() >= 2 => {
                        modified = true;
                        // Push in reverse order so first child is processed first
                        for &arg in args.iter().rev() {
                            work_stack.push(arg);
                        }
                    }
                    // Not an AND: keep as individual assertion
                    _ => {
                        new_assertions.push(term);
                    }
                }
            }
        }

        if modified {
            *assertions = new_assertions;
        }

        modified
    }

    fn reset(&mut self) {
        self.processed.clear();
    }
}

#[cfg(test)]
#[path = "flatten_and_tests.rs"]
mod tests;
