// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `SeqValue` trait and conversion implementations.

use super::super::Value;
use super::SeqValue;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::{Arc, OnceLock};
use tla_core::kani_types::Vector;

impl Clone for SeqValue {
    fn clone(&self) -> Self {
        let additive = self.additive_fp.load(AtomicOrdering::Relaxed);
        let flat_view = OnceLock::new();
        if let Some(flat) = self.flat_view.get() {
            let _ = flat_view.set(Arc::clone(flat));
        }
        SeqValue {
            elements: self.elements.clone(),
            additive_fp: AtomicU64::new(additive),
            flat_view,
        }
    }
}

impl Default for SeqValue {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Vec<Value>> for SeqValue {
    fn from(vec: Vec<Value>) -> Self {
        SeqValue::from_vec(vec)
    }
}

impl From<Vector<Value>> for SeqValue {
    fn from(elements: Vector<Value>) -> Self {
        SeqValue::from_imvec(elements)
    }
}

impl PartialEq for SeqValue {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        self.flat_slice() == other.flat_slice()
    }
}

impl Eq for SeqValue {}

impl PartialOrd for SeqValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SeqValue {
    fn cmp(&self, other: &Self) -> Ordering {
        for (a, b) in self.flat_slice().iter().zip(other.flat_slice().iter()) {
            match a.cmp(b) {
                Ordering::Equal => {}
                other => return other,
            }
        }
        self.len().cmp(&other.len())
    }
}

impl Hash for SeqValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for elem in self.flat_slice() {
            elem.hash(state);
        }
    }
}

impl fmt::Debug for SeqValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(feature = "im")]
impl<'a> IntoIterator for &'a SeqValue {
    type Item = &'a Value;
    type IntoIter = im::vector::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(not(feature = "im"))]
impl<'a> IntoIterator for &'a SeqValue {
    type Item = &'a Value;
    type IntoIter = std::slice::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromIterator<Value> for SeqValue {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        SeqValue::from_vec(iter.into_iter().collect())
    }
}

impl std::ops::Index<usize> for SeqValue {
    type Output = Value;

    fn index(&self, index: usize) -> &Self::Output {
        self.elements
            .get(index)
            .expect("SeqValue index out of bounds")
    }
}
