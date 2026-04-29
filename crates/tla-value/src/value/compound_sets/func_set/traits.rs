// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ordering, equality, and hash trait impls for FuncSetValue.

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use super::FuncSetValue;

impl PartialEq for FuncSetValue {
    fn eq(&self, other: &Self) -> bool {
        self.domain == other.domain && self.codomain == other.codomain
    }
}

impl Eq for FuncSetValue {}

impl Hash for FuncSetValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.domain.hash(state);
        self.codomain.hash(state);
    }
}

impl Ord for FuncSetValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.domain.cmp(&other.domain) {
            Ordering::Equal => self.codomain.cmp(&other.codomain),
            ord => ord,
        }
    }
}

impl PartialOrd for FuncSetValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
