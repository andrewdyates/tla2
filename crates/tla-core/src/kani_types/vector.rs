// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Andrew Yates

use std::cmp::Ordering;
use std::fmt;

/// std-backed replacement for `im::Vector`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Vector<V>(Vec<V>);

impl<V: Clone> Vector<V> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push_back(&mut self, v: V) {
        self.0.push(v);
    }

    pub fn split_off(&mut self, at: usize) -> Self {
        assert!(at <= self.0.len());
        Self(self.0.split_off(at))
    }

    pub fn get(&self, index: usize) -> Option<&V> {
        self.0.get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut V> {
        self.0.get_mut(index)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, V> {
        self.0.iter()
    }

    pub fn update(&self, index: usize, v: V) -> Self {
        let mut new_vec = self.0.clone();
        new_vec[index] = v;
        Self(new_vec)
    }

    pub fn slice(&self, range: std::ops::Range<usize>) -> Self {
        let end = range.end.min(self.0.len());
        let start = range.start.min(end);
        Self(self.0[start..end].to_vec())
    }

    pub fn append(&self, other: &Self) -> Self {
        let mut new_vec = self.0.clone();
        new_vec.extend(other.0.iter().cloned());
        Self(new_vec)
    }

    pub fn pop_back(&mut self) -> Option<V> {
        self.0.pop()
    }

    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
    }

    pub fn back_mut(&mut self) -> Option<&mut V> {
        self.0.last_mut()
    }

    pub fn set(&mut self, index: usize, value: V) -> V {
        std::mem::replace(&mut self.0[index], value)
    }

    pub fn front(&self) -> Option<&V> {
        self.0.first()
    }

    pub fn back(&self) -> Option<&V> {
        self.0.last()
    }
}

impl<V: Clone> Default for Vector<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Clone + fmt::Debug> fmt::Debug for Vector<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl<V: Clone> FromIterator<V> for Vector<V> {
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<V: Clone> IntoIterator for Vector<V> {
    type Item = V;
    type IntoIter = std::vec::IntoIter<V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, V: Clone> IntoIterator for &'a Vector<V> {
    type Item = &'a V;
    type IntoIter = std::slice::Iter<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<V: Clone> std::ops::Index<usize> for Vector<V> {
    type Output = V;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<V: Clone + PartialOrd> PartialOrd for Vector<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<V: Clone + Ord> Ord for Vector<V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<V: Clone> From<Vec<V>> for Vector<V> {
    fn from(vec: Vec<V>) -> Self {
        Self(vec)
    }
}

impl<V: Clone> From<Vector<V>> for Vec<V> {
    fn from(vector: Vector<V>) -> Self {
        vector.0
    }
}
