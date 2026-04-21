// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Andrew Yates

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::iter::FromIterator;

/// std-backed replacement for `im::OrdMap`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct OrdMap<K, V>(BTreeMap<K, V>);

impl<K: Ord + Clone, V: Clone> OrdMap<K, V> {
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    pub fn unit(key: K, value: V) -> Self {
        let mut map = BTreeMap::new();
        map.insert(key, value);
        Self(map)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.0.insert(k, v)
    }

    pub fn update(&self, k: K, v: V) -> Self {
        let mut new_map = self.0.clone();
        new_map.insert(k, v);
        Self(new_map)
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.0.get(k)
    }

    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.0.get_mut(k)
    }

    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.0.contains_key(k)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.0.iter()
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.0.keys()
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.0.values()
    }

    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.0.remove(k)
    }

    pub fn without<Q>(&self, k: &Q) -> Self
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut new_map = self.0.clone();
        new_map.remove(k);
        Self(new_map)
    }

    pub fn update_with<F>(&self, k: K, f: F) -> Self
    where
        F: FnOnce(Option<V>) -> Option<V>,
    {
        let mut new_map = self.0.clone();
        let old_val = new_map.remove(&k);
        if let Some(new_val) = f(old_val) {
            new_map.insert(k, new_val);
        }
        Self(new_map)
    }

    pub fn union(&self, other: &Self) -> Self {
        let mut new_map = self.0.clone();
        for (k, v) in &other.0 {
            new_map.insert(k.clone(), v.clone());
        }
        Self(new_map)
    }
}

impl<K: Ord + Clone, V: Clone> Default for OrdMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + Clone + fmt::Debug, V: Clone + fmt::Debug> fmt::Debug for OrdMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.0.iter()).finish()
    }
}

impl<K: Ord + Clone, V: Clone> FromIterator<(K, V)> for OrdMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<K: Ord + Clone, V: Clone> IntoIterator for OrdMap<K, V> {
    type Item = (K, V);
    type IntoIter = std::collections::btree_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K: Ord + Clone, V: Clone> IntoIterator for &'a OrdMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = std::collections::btree_map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<K: Ord, V: PartialOrd> PartialOrd for OrdMap<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.iter().partial_cmp(other.0.iter())
    }
}

impl<K: Ord, V: Ord> Ord for OrdMap<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.iter().cmp(other.0.iter())
    }
}
