// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLA+ runtime value types: sets, functions, and records.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A TLA+ set implemented as a sorted set for determinism.
///
/// This type mirrors TLA+ set semantics:
/// - Elements are unique
/// - Order doesn't matter for equality
/// - Iteration order is deterministic (sorted)
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TlaSet<T: Ord + Clone>(BTreeSet<T>);

impl<T: Ord + Clone> TlaSet<T> {
    /// Create an empty set
    pub fn new() -> Self {
        TlaSet(BTreeSet::new())
    }

    /// Check if element is in set
    pub fn contains(&self, elem: &T) -> bool {
        self.0.contains(elem)
    }

    /// Insert an element
    pub fn insert(&mut self, elem: T) {
        self.0.insert(elem);
    }

    /// Number of elements
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Iterate over elements in sorted order
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    /// Union of two sets
    pub fn union(&self, other: &TlaSet<T>) -> TlaSet<T> {
        TlaSet(self.0.union(&other.0).cloned().collect())
    }

    /// Intersection of two sets
    pub fn intersect(&self, other: &TlaSet<T>) -> TlaSet<T> {
        TlaSet(self.0.intersection(&other.0).cloned().collect())
    }

    /// Set difference
    pub fn difference(&self, other: &TlaSet<T>) -> TlaSet<T> {
        TlaSet(self.0.difference(&other.0).cloned().collect())
    }

    /// Check if this is a subset of other
    pub fn is_subset(&self, other: &TlaSet<T>) -> bool {
        self.0.is_subset(&other.0)
    }

    /// Convert all elements to Value and collect into a TlaSet<Value>.
    /// Useful when checking containment against a Value-typed state variable.
    pub fn to_value_set(&self) -> TlaSet<Value>
    where
        T: Into<Value>,
    {
        TlaSet(self.0.iter().map(|e| e.clone().into()).collect())
    }
}

impl<T: Ord + Clone> Default for TlaSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord + Clone + fmt::Debug> fmt::Debug for TlaSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for elem in &self.0 {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{elem:?}")?;
        }
        write!(f, "}}")
    }
}

impl<T: Ord + Clone> IntoIterator for TlaSet<T> {
    type Item = T;
    type IntoIter = std::collections::btree_set::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T: Ord + Clone> IntoIterator for &'a TlaSet<T> {
    type Item = &'a T;
    type IntoIter = std::collections::btree_set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<T: Ord + Clone> FromIterator<T> for TlaSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        TlaSet(iter.into_iter().collect())
    }
}

/// A TLA+ function implemented as a sorted map for determinism.
///
/// TLA+ functions are total mappings from a domain to values.
/// This is different from Rust functions - it's more like a HashMap.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TlaFunc<K: Ord + Clone, V: Ord + Clone>(BTreeMap<K, V>);

impl<K: Ord + Clone, V: Ord + Clone> TlaFunc<K, V> {
    /// Create an empty function
    pub fn new() -> Self {
        TlaFunc(BTreeMap::new())
    }

    /// Apply the function to an argument
    pub fn apply(&self, key: &K) -> Option<&V> {
        self.0.get(key)
    }

    /// Get the domain of the function
    pub fn domain(&self) -> TlaSet<K> {
        self.0.keys().cloned().collect()
    }

    /// Update the function at a single point (EXCEPT) - returns new function
    pub fn except(&self, key: K, value: V) -> Self {
        let mut new_map = self.0.clone();
        new_map.insert(key, value);
        TlaFunc(new_map)
    }

    /// Update the function at a single point in place (for EXCEPT code generation)
    pub fn update(&mut self, key: K, value: V) {
        self.0.insert(key, value);
    }

    /// Iterate over (key, value) pairs
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.0.iter()
    }
}

impl<K: Ord + Clone, V: Ord + Clone> Default for TlaFunc<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + Clone + fmt::Debug, V: Ord + Clone + fmt::Debug> fmt::Debug for TlaFunc<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for (k, v) in &self.0 {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{k:?} |-> {v:?}")?;
        }
        write!(f, "]")
    }
}

impl<K: Ord + Clone, V: Ord + Clone> FromIterator<(K, V)> for TlaFunc<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        TlaFunc(iter.into_iter().collect())
    }
}

/// A TLA+ record implemented as a sorted map from field names to values.
///
/// TLA+ records are like structs: [a |-> 1, b |-> 2]
/// Field access: r.a
/// Field update: [r EXCEPT !.a = 3]
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TlaRecord<V: Ord + Clone>(BTreeMap<String, V>);

impl<V: Ord + Clone> TlaRecord<V> {
    /// Create an empty record
    pub fn new() -> Self {
        TlaRecord(BTreeMap::new())
    }

    /// Create a record from field-value pairs
    pub fn from_fields(fields: impl IntoIterator<Item = (impl Into<String>, V)>) -> Self {
        TlaRecord(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    }

    /// Get a field value
    pub fn get(&self, field: &str) -> Option<&V> {
        self.0.get(field)
    }

    /// Set a field value (in place)
    pub fn set(&mut self, field: impl Into<String>, value: V) {
        self.0.insert(field.into(), value);
    }

    /// Get the set of field names
    pub fn fields(&self) -> TlaSet<String> {
        self.0.keys().cloned().collect()
    }

    /// Iterate over (field, value) pairs
    pub fn iter(&self) -> impl Iterator<Item = (&String, &V)> {
        self.0.iter()
    }
}

impl<V: Ord + Clone> Default for TlaRecord<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Ord + Clone + fmt::Debug> fmt::Debug for TlaRecord<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for (k, v) in &self.0 {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{k} |-> {v:?}")?;
        }
        write!(f, "]")
    }
}

impl<V: Ord + Clone> FromIterator<(String, V)> for TlaRecord<V> {
    fn from_iter<I: IntoIterator<Item = (String, V)>>(iter: I) -> Self {
        TlaRecord(iter.into_iter().collect())
    }
}

/// Compute k-subsets: all subsets of S with exactly k elements.
///
/// This is used for `kSubset(k, S)` in TLA+.
pub fn k_subsets<T: Ord + Clone>(set: &TlaSet<T>, k: i64) -> TlaSet<TlaSet<T>> {
    let elements: Vec<_> = set.iter().cloned().collect();
    let n = elements.len();
    let k = k as usize;
    let mut result = TlaSet::new();
    if k > n {
        return result;
    }
    // Generate all k-element subsets using bitmask
    if n <= 30 {
        for mask in 0..(1u64 << n) {
            if (mask.count_ones() as usize) == k {
                let mut subset = TlaSet::new();
                for (i, elem) in elements.iter().enumerate() {
                    if mask & (1 << i) != 0 {
                        subset.insert(elem.clone());
                    }
                }
                result.insert(subset);
            }
        }
    }
    result
}

/// Compute the set of all permutations of a set.
///
/// Used for `Permutations(S)` in TLA+. Returns the set of all bijections
/// from S to S, represented as `TlaFunc<T, T>`.
pub fn permutations<T: Ord + Clone>(set: &TlaSet<T>) -> TlaSet<TlaFunc<T, T>> {
    let elements: Vec<_> = set.iter().cloned().collect();
    let n = elements.len();
    let mut result = TlaSet::new();

    // Generate all permutations
    let mut indices: Vec<usize> = (0..n).collect();
    loop {
        let func: TlaFunc<T, T> = indices
            .iter()
            .enumerate()
            .map(|(i, &j)| (elements[i].clone(), elements[j].clone()))
            .collect();
        result.insert(func);

        // Next permutation (Heap's algorithm simplified)
        let mut i = n.wrapping_sub(1);
        if n <= 1 {
            break;
        }
        while i > 0 && indices[i - 1] >= indices[i] {
            i -= 1;
        }
        if i == 0 {
            break;
        }
        let mut j = n - 1;
        while indices[j] <= indices[i - 1] {
            j -= 1;
        }
        indices.swap(i - 1, j);
        indices[i..].reverse();
    }
    result
}

/// A dynamically-typed TLA+ value for use when codegen cannot infer a
/// concrete Rust type.
///
/// This enum covers all TLA+ value types and implements `Ord`, `Eq`, `Hash`,
/// and `Clone` so it can be used as an element type in `TlaSet<Value>`,
/// `TlaFunc<Value, Value>`, etc.
///
/// Generated code uses this type as a fallback; most well-typed specs will
/// use concrete types like `i64`, `String`, `TlaSet<i64>` directly.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Value {
    /// Boolean value
    Bool(bool),
    /// Integer value (TLA+ integers are unbounded, but we use i64)
    Int(i64),
    /// String value
    Str(String),
    /// Set of values
    Set(TlaSet<Value>),
    /// Sequence (ordered list) of values
    Seq(Vec<Value>),
    /// Function (map) from values to values
    Func(TlaFunc<Value, Value>),
    /// Record (string-keyed map)
    Record(TlaRecord<Value>),
    /// Tuple of values
    Tuple(Vec<Value>),
    /// Model value (symbolic constant)
    ModelValue(String),
}

impl Value {
    /// Check if this value is truthy (for boolean contexts).
    pub fn is_true(&self) -> bool {
        matches!(self, Value::Bool(true))
    }

    /// Check if this Value contains another (set membership).
    pub fn contains(&self, elem: &Value) -> bool {
        match self {
            Value::Set(s) => s.contains(elem),
            _ => false,
        }
    }

    /// Iterate over elements (works for sets and sequences).
    pub fn iter(&self) -> Box<dyn Iterator<Item = &Value> + '_> {
        match self {
            Value::Set(s) => Box::new(s.iter()),
            Value::Seq(v) => Box::new(v.iter()),
            _ => Box::new(std::iter::empty()),
        }
    }

    /// Number of elements (for sets, sequences, records, functions).
    pub fn len(&self) -> usize {
        match self {
            Value::Set(s) => s.len(),
            Value::Seq(v) => v.len(),
            Value::Record(r) => r.iter().count(),
            Value::Func(f) => f.iter().count(),
            _ => 0,
        }
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Apply as a function: self[key].
    pub fn apply(&self, key: &Value) -> Option<&Value> {
        match self {
            Value::Func(f) => f.apply(key),
            _ => None,
        }
    }

    /// Get a record field.
    pub fn get(&self, field: &str) -> Option<&Value> {
        match self {
            Value::Record(r) => r.get(field),
            _ => None,
        }
    }

    /// Set union.
    pub fn union(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Set(a), Value::Set(b)) => Value::Set(a.union(b)),
            _ => self.clone(),
        }
    }

    /// Set intersection.
    pub fn intersect(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Set(a), Value::Set(b)) => Value::Set(a.intersect(b)),
            _ => self.clone(),
        }
    }

    /// Set difference.
    pub fn difference(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Set(a), Value::Set(b)) => Value::Set(a.difference(b)),
            _ => self.clone(),
        }
    }

    /// Subset check.
    pub fn is_subset(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Set(a), Value::Set(b)) => a.is_subset(b),
            _ => false,
        }
    }

    /// Function EXCEPT: return new function with one key updated.
    pub fn except(&self, key: Value, value: Value) -> Value {
        match self {
            Value::Func(f) => Value::Func(f.except(key, value)),
            _ => self.clone(),
        }
    }

    /// In-place function update (for multi-spec EXCEPT).
    pub fn update(&mut self, key: Value, value: Value) {
        if let Value::Func(ref mut f) = self {
            f.update(key, value);
        }
    }

    /// Set a record field value in place.
    pub fn set(&mut self, field: impl Into<String>, value: Value) {
        if let Value::Record(ref mut r) = self {
            r.set(field, value);
        }
    }

    /// Get the domain of a function.
    pub fn domain(&self) -> TlaSet<Value> {
        match self {
            Value::Func(f) => f.domain(),
            _ => TlaSet::new(),
        }
    }

    /// Insert into a set.
    pub fn insert(&mut self, elem: Value) {
        if let Value::Set(ref mut s) = self {
            s.insert(elem);
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Int(n) => write!(f, "{n}"),
            Value::Str(s) => write!(f, "{s:?}"),
            Value::Set(s) => write!(f, "{s:?}"),
            Value::Seq(s) => write!(f, "{s:?}"),
            Value::Func(func) => write!(f, "{func:?}"),
            Value::Record(r) => write!(f, "{r:?}"),
            Value::Tuple(t) => write!(f, "{t:?}"),
            Value::ModelValue(m) => write!(f, "{m}"),
        }
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<i64> for Value {
    fn from(n: i64) -> Self {
        Value::Int(n)
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::Str(s)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::Str(s.to_string())
    }
}

/// Extract i64 from Value for generated code type coercion.
impl From<Value> for i64 {
    fn from(v: Value) -> Self {
        match v {
            Value::Int(n) => n,
            _ => 0, // fallback for generated code
        }
    }
}

/// Extract bool from Value for generated code type coercion.
impl From<Value> for bool {
    fn from(v: Value) -> Self {
        match v {
            Value::Bool(b) => b,
            _ => false,
        }
    }
}

/// Extract String from Value for generated code type coercion.
impl From<Value> for String {
    fn from(v: Value) -> Self {
        match v {
            Value::Str(s) => s,
            Value::ModelValue(s) => s,
            _ => String::new(),
        }
    }
}

/// Convert `TlaSet<T>` into `Value::Set` by converting each element to `Value`.
/// This covers generated code patterns like `TlaSet<TlaRecord<Value>>` or
/// `TlaSet<TlaFunc<i64, i64>>` that need to become `Value::Set`.
/// When T = Value, the conversion is effectively identity (Value::from(Value) = Value).
impl<T: Into<Value> + Ord + Clone> From<TlaSet<T>> for Value {
    fn from(s: TlaSet<T>) -> Self {
        Value::Set(s.iter().map(|v| v.clone().into()).collect())
    }
}

impl From<Vec<Value>> for Value {
    fn from(v: Vec<Value>) -> Self {
        Value::Seq(v)
    }
}

/// Convert `TlaFunc<K, V>` into `Value::Func` by converting keys and values.
/// When K = Value and V = Value, the conversion is effectively identity.
impl<K: Into<Value> + Ord + Clone, V: Into<Value> + Ord + Clone> From<TlaFunc<K, V>> for Value {
    fn from(f: TlaFunc<K, V>) -> Self {
        Value::Func(
            f.iter()
                .map(|(k, v)| (k.clone().into(), v.clone().into()))
                .collect(),
        )
    }
}

impl From<TlaRecord<Value>> for Value {
    fn from(r: TlaRecord<Value>) -> Self {
        Value::Record(r)
    }
}

impl From<(Value, Value)> for Value {
    fn from(t: (Value, Value)) -> Self {
        Value::Tuple(vec![t.0, t.1])
    }
}

/// Allow `for x in value` when value is a set or sequence.
/// Panics at runtime if the Value is not a Set or Seq.
impl IntoIterator for Value {
    type Item = Value;
    type IntoIter = std::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Value::Set(s) => s.into_iter().collect::<Vec<_>>().into_iter(),
            Value::Seq(v) => v.into_iter(),
            Value::Tuple(v) => v.into_iter(),
            other => panic!("cannot iterate over {other:?}"),
        }
    }
}

impl std::ops::Add for Value {
    type Output = Value;
    fn add(self, rhs: Value) -> Value {
        match (&self, &rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            _ => self,
        }
    }
}

impl std::ops::Sub for Value {
    type Output = Value;
    fn sub(self, rhs: Value) -> Value {
        match (&self, &rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a - b),
            _ => self,
        }
    }
}

impl std::ops::Mul for Value {
    type Output = Value;
    fn mul(self, rhs: Value) -> Value {
        match (&self, &rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a * b),
            _ => self,
        }
    }
}

impl std::ops::Div for Value {
    type Output = Value;
    fn div(self, rhs: Value) -> Value {
        match (&self, &rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            _ => self,
        }
    }
}

impl std::ops::Rem for Value {
    type Output = Value;
    fn rem(self, rhs: Value) -> Value {
        match (&self, &rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a % b),
            _ => self,
        }
    }
}

impl std::ops::Neg for Value {
    type Output = Value;
    fn neg(self) -> Value {
        match self {
            Value::Int(n) => Value::Int(-n),
            _ => self,
        }
    }
}

// Mixed-type arithmetic: Value op i64
impl std::ops::Add<i64> for Value {
    type Output = Value;
    fn add(self, rhs: i64) -> Value {
        self + Value::Int(rhs)
    }
}

impl std::ops::Sub<i64> for Value {
    type Output = Value;
    fn sub(self, rhs: i64) -> Value {
        self - Value::Int(rhs)
    }
}

impl std::ops::Mul<i64> for Value {
    type Output = Value;
    fn mul(self, rhs: i64) -> Value {
        self * Value::Int(rhs)
    }
}

impl std::ops::Div<i64> for Value {
    type Output = Value;
    fn div(self, rhs: i64) -> Value {
        self / Value::Int(rhs)
    }
}

impl std::ops::Rem<i64> for Value {
    type Output = Value;
    fn rem(self, rhs: i64) -> Value {
        self % Value::Int(rhs)
    }
}

// Mixed-type arithmetic: i64 op Value
impl std::ops::Add<Value> for i64 {
    type Output = Value;
    fn add(self, rhs: Value) -> Value {
        Value::Int(self) + rhs
    }
}

impl std::ops::Sub<Value> for i64 {
    type Output = Value;
    fn sub(self, rhs: Value) -> Value {
        Value::Int(self) - rhs
    }
}

impl std::ops::Mul<Value> for i64 {
    type Output = Value;
    fn mul(self, rhs: Value) -> Value {
        Value::Int(self) * rhs
    }
}

impl std::ops::Div<Value> for i64 {
    type Output = Value;
    fn div(self, rhs: Value) -> Value {
        Value::Int(self) / rhs
    }
}

impl std::ops::Rem<Value> for i64 {
    type Output = Value;
    fn rem(self, rhs: Value) -> Value {
        Value::Int(self) % rhs
    }
}

impl std::ops::Not for Value {
    type Output = bool;
    fn not(self) -> bool {
        !self.is_true()
    }
}

// Cross-type equality: Value vs i64, bool, String, &str
impl PartialEq<i64> for Value {
    fn eq(&self, other: &i64) -> bool {
        matches!(self, Value::Int(n) if n == other)
    }
}

impl PartialEq<Value> for i64 {
    fn eq(&self, other: &Value) -> bool {
        matches!(other, Value::Int(n) if n == self)
    }
}

impl PartialEq<bool> for Value {
    fn eq(&self, other: &bool) -> bool {
        matches!(self, Value::Bool(b) if b == other)
    }
}

impl PartialEq<Value> for bool {
    fn eq(&self, other: &Value) -> bool {
        matches!(other, Value::Bool(b) if b == self)
    }
}

impl PartialEq<str> for Value {
    fn eq(&self, other: &str) -> bool {
        matches!(self, Value::Str(s) if s == other)
    }
}

impl PartialEq<String> for Value {
    fn eq(&self, other: &String) -> bool {
        matches!(self, Value::Str(s) if s == other)
    }
}

impl PartialEq<Value> for String {
    fn eq(&self, other: &Value) -> bool {
        matches!(other, Value::Str(s) if s == self)
    }
}

// Cross-type equality: Value vs TlaSet, TlaFunc, Vec, TlaRecord
impl<T: Into<Value> + Ord + Clone> PartialEq<TlaSet<T>> for Value {
    fn eq(&self, other: &TlaSet<T>) -> bool {
        match self {
            Value::Set(s) => {
                let other_as_value: TlaSet<Value> = other.iter().map(|e| e.clone().into()).collect();
                s == &other_as_value
            }
            _ => false,
        }
    }
}

impl PartialEq<Vec<Value>> for Value {
    fn eq(&self, other: &Vec<Value>) -> bool {
        matches!(self, Value::Seq(s) if s == other)
    }
}

impl PartialEq<TlaFunc<Value, Value>> for Value {
    fn eq(&self, other: &TlaFunc<Value, Value>) -> bool {
        matches!(self, Value::Func(f) if f == other)
    }
}

impl PartialEq<TlaRecord<Value>> for Value {
    fn eq(&self, other: &TlaRecord<Value>) -> bool {
        matches!(self, Value::Record(r) if r == other)
    }
}

// Cross-type ordering: Value vs i64
impl PartialOrd<i64> for Value {
    fn partial_cmp(&self, other: &i64) -> Option<std::cmp::Ordering> {
        match self {
            Value::Int(n) => n.partial_cmp(other),
            _ => None,
        }
    }
}

impl PartialOrd<Value> for i64 {
    fn partial_cmp(&self, other: &Value) -> Option<std::cmp::Ordering> {
        match other {
            Value::Int(n) => self.partial_cmp(n),
            _ => None,
        }
    }
}

impl Value {
    /// Power operation for generated code.
    pub fn pow(&self, exp: u32) -> Value {
        match self {
            Value::Int(n) => Value::Int(n.pow(exp)),
            _ => self.clone(),
        }
    }

    /// first() for sequence semantics.
    pub fn first(&self) -> Option<&Value> {
        match self {
            Value::Seq(v) => v.first(),
            _ => None,
        }
    }

    /// Push to sequence (Append).
    pub fn push(&mut self, elem: Value) {
        if let Value::Seq(ref mut v) = self {
            v.push(elem);
        }
    }
}

/// Allow iteration via `for x in &value` (for set/sequence values).
impl<'a> IntoIterator for &'a Value {
    type Item = &'a Value;
    type IntoIter = Box<dyn Iterator<Item = &'a Value> + 'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Create a range set {a..b} inclusive
pub fn range_set(a: i64, b: i64) -> TlaSet<i64> {
    if a > b {
        TlaSet::new()
    } else {
        (a..=b).collect()
    }
}

/// The BOOLEAN set {FALSE, TRUE}
pub fn boolean_set() -> TlaSet<bool> {
    crate::tla_set![false, true]
}

/// Compute the powerset (SUBSET S)
pub fn powerset<T: Ord + Clone>(set: &TlaSet<T>) -> TlaSet<TlaSet<T>> {
    let elements: Vec<_> = set.iter().cloned().collect();
    let n = elements.len();

    assert!(
        n <= 20,
        "SUBSET of set with {n} elements would be too large"
    );

    let mut result = TlaSet::new();
    for mask in 0..(1u64 << n) {
        let mut subset = TlaSet::new();
        for (i, elem) in elements.iter().enumerate() {
            if mask & (1 << i) != 0 {
                subset.insert(elem.clone());
            }
        }
        result.insert(subset);
    }
    result
}

/// Compute the Cartesian product of two sets
pub fn cartesian_product<T: Ord + Clone, U: Ord + Clone>(
    a: &TlaSet<T>,
    b: &TlaSet<U>,
) -> TlaSet<(T, U)> {
    let mut result = TlaSet::new();
    for x in a {
        for y in b {
            result.insert((x.clone(), y.clone()));
        }
    }
    result
}

/// Check if a set is finite (always true for in-memory sets)
pub fn is_finite_set<T>(_set: T) -> bool {
    true
}

/// Pick a random element from a set (deterministic: picks first element)
pub fn random_element<T: Ord + Clone>(set: &TlaSet<T>) -> T {
    set.iter()
        .next()
        .cloned()
        .expect("RandomElement requires non-empty set")
}

/// Seq(S) — the set of all finite sequences over S.
///
/// In TLA+ this is an infinite set. For codegen, we generate sequences up to
/// a bounded length (default: elements^2, capped at 4) to avoid combinatorial
/// explosion. This is sufficient for type constraints and small-domain model
/// checking. Returns an empty set if the base set is empty.
pub fn seq_set<T: Ord + Clone>(base: &TlaSet<T>) -> TlaSet<Vec<T>> {
    let elements: Vec<_> = base.iter().cloned().collect();
    let n = elements.len();
    if n == 0 {
        // Only the empty sequence
        let mut result = TlaSet::new();
        result.insert(Vec::new());
        return result;
    }
    // Bound the max length to avoid explosion
    let max_len = std::cmp::min(n * n, 4);
    let mut result = TlaSet::new();
    // Empty sequence
    result.insert(Vec::new());
    // Generate sequences of length 1..=max_len
    fn generate_seqs<T: Ord + Clone>(
        elements: &[T],
        current: &mut Vec<T>,
        max_len: usize,
        result: &mut TlaSet<Vec<T>>,
    ) {
        if current.len() > max_len {
            return;
        }
        if !current.is_empty() {
            result.insert(current.clone());
        }
        if current.len() < max_len {
            for elem in elements {
                current.push(elem.clone());
                generate_seqs(elements, current, max_len, result);
                current.pop();
            }
        }
    }
    let mut current = Vec::new();
    generate_seqs(&elements, &mut current, max_len, &mut result);
    result
}

/// Function merge: f @@ g.
///
/// Returns a new function that maps each key in `DOMAIN(f) \union DOMAIN(g)`
/// to `f[k]` if `k \in DOMAIN(f)`, otherwise `g[k]`. In other words, `f`
/// takes priority over `g` for keys in both domains.
pub fn func_merge<K: Ord + Clone, V: Ord + Clone>(
    f: &TlaFunc<K, V>,
    g: &TlaFunc<K, V>,
) -> TlaFunc<K, V> {
    let mut result: BTreeMap<K, V> = BTreeMap::new();
    // Add all of g first (lower priority)
    for (k, v) in g.iter() {
        result.insert(k.clone(), v.clone());
    }
    // Overwrite with f (higher priority)
    for (k, v) in f.iter() {
        result.insert(k.clone(), v.clone());
    }
    TlaFunc(result)
}
