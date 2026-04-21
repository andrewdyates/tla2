// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;
use std::iter::FromIterator;

/// std-backed replacement for `im::OrdSet`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct OrdSet<V>(BTreeSet<V>);

impl<V: Ord + Clone> OrdSet<V> {
    pub fn new() -> Self {
        Self(BTreeSet::new())
    }

    pub fn unit(a: V) -> Self {
        let mut set = BTreeSet::new();
        set.insert(a);
        Self(set)
    }

    pub fn insert(&mut self, v: V) -> Option<V> {
        if self.0.contains(&v) {
            let old = self.0.take(&v);
            self.0.insert(v);
            old
        } else {
            self.0.insert(v);
            None
        }
    }

    pub fn update(&self, v: V) -> Self {
        let mut new_set = self.0.clone();
        new_set.insert(v);
        Self(new_set)
    }

    pub fn remove<Q>(&mut self, v: &Q) -> Option<V>
    where
        V: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.0.take(v)
    }

    pub fn contains<Q>(&self, v: &Q) -> bool
    where
        V: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.0.contains(v)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &V> {
        self.0.iter()
    }

    pub fn without<Q>(&self, v: &Q) -> Self
    where
        V: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut new_set = self.0.clone();
        new_set.remove(v);
        Self(new_set)
    }

    pub fn union(mut self, other: Self) -> Self {
        for v in other.0 {
            self.0.insert(v);
        }
        self
    }

    pub fn intersection(self, other: Self) -> Self {
        Self(self.0.intersection(&other.0).cloned().collect())
    }

    pub fn difference(self, other: Self) -> Self {
        Self(self.0.difference(&other.0).cloned().collect())
    }

    pub fn relative_complement(self, other: Self) -> Self {
        self.difference(other)
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }
}

impl<V: Ord + Clone> Default for OrdSet<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Ord + Clone + fmt::Debug> fmt::Debug for OrdSet<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.0.iter()).finish()
    }
}

impl<V: Ord + Clone> FromIterator<V> for OrdSet<V> {
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<V: Ord + Clone> IntoIterator for OrdSet<V> {
    type Item = V;
    type IntoIter = std::collections::btree_set::IntoIter<V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, V: Ord + Clone> IntoIterator for &'a OrdSet<V> {
    type Item = &'a V;
    type IntoIter = std::collections::btree_set::Iter<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<V: Ord> PartialOrd for OrdSet<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<V: Ord> Ord for OrdSet<V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.iter().cmp(other.0.iter())
    }
}
