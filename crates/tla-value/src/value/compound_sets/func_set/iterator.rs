// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FuncSetIterator: lazy odometer iteration over [S -> T] function sets.

use std::sync::Arc;

use num_traits::ToPrimitive;

use super::super::super::*;

/// Iterator over function set elements
pub(crate) struct FuncSetIterator {
    domain_elems: Vec<Value>,
    codomain_elems: Vec<Value>,
    indices: Vec<usize>,
    done: bool,
}

impl FuncSetIterator {
    /// Create a FuncSetIterator from pre-ordered element vectors.
    ///
    /// Fix #2364: Used by `iter_set_tlc_normalized` to construct a lazy odometer
    /// iterator with domain/range elements in TLC-normalized order, avoiding
    /// the O(|T|^|S| * log) materialization+sort of all function values.
    pub fn from_elems(domain_elems: Vec<Value>, codomain_elems: Vec<Value>) -> Self {
        let n = domain_elems.len();
        let done = codomain_elems.is_empty() && !domain_elems.is_empty();
        FuncSetIterator {
            indices: vec![0; n],
            domain_elems,
            codomain_elems,
            done,
        }
    }

    /// Check if domain elements form a consecutive integer interval.
    /// Returns Some((min, max)) if so, None otherwise.
    fn is_int_interval_domain(&self) -> Option<(i64, i64)> {
        if self.domain_elems.is_empty() {
            return None;
        }

        // All elements must be integers
        let mut ints: Vec<i64> = Vec::with_capacity(self.domain_elems.len());
        for elem in &self.domain_elems {
            match elem {
                Value::SmallInt(n) => ints.push(*n),
                Value::Int(n) => {
                    if let Some(i) = n.to_i64() {
                        ints.push(i);
                    } else {
                        return None; // Out of i64 range
                    }
                }
                _ => return None, // Non-integer domain element
            }
        }

        // Must be sorted (domain_elems comes from OrdSet which is sorted)
        // Check if consecutive integers: min, min+1, min+2, ..., max
        let min = ints[0];
        let max = ints[ints.len() - 1];
        if checked_interval_len(min, max) != Some(ints.len()) {
            return None; // Not consecutive or overflow
        }

        // Verify all are consecutive (sorted + size check should be enough,
        // but let's be explicit)
        for (i, &n) in ints.iter().enumerate() {
            if n != min + i as i64 {
                return None;
            }
        }

        Some((min, max))
    }
}

impl Iterator for FuncSetIterator {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // Handle empty domain case: [{}->T] = {[]}
        if self.domain_elems.is_empty() {
            self.done = true;
            return Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                Vec::new(),
            ))));
        }

        // Check if domain is a consecutive integer sequence starting at some min
        // If so, use IntFunc for better EXCEPT performance
        // IMPORTANT: If domain is 1..n, create Seq instead (functions 1..n are sequences in TLA+)
        let func = if let Some((min, max)) = self.is_int_interval_domain() {
            // Build IntFunc/Seq with array of values
            let values: Vec<Value> = (0..self.domain_elems.len())
                .map(|i| self.codomain_elems[self.indices[i]].clone())
                .collect();
            // If domain is 1..n, this is semantically a sequence
            if min == 1 {
                Value::Seq(Arc::new(values.into()))
            } else {
                Value::IntFunc(Arc::new(IntIntervalFunc::new(min, max, values)))
            }
        } else {
            let entries =
                build_func_entries(&self.domain_elems, &self.codomain_elems, &self.indices);
            Value::Func(Arc::new(FuncValue::from_sorted_entries(entries)))
        };

        // Increment indices (like counting in base |T|).
        //
        // TLC-compatible enumeration order: treat earlier domain elements as more significant.
        // This means the *last* domain element changes fastest.
        let mut carry = true;
        for i in (0..self.indices.len()).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] >= self.codomain_elems.len() {
                    self.indices[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            self.done = true;
        }

        Some(func)
    }
}

fn build_func_entries(
    domain_elems: &[Value],
    codomain_elems: &[Value],
    indices: &[usize],
) -> Vec<(Value, Value)> {
    let mut entries = Vec::with_capacity(domain_elems.len());
    for (key, &value_idx) in domain_elems.iter().zip(indices.iter()) {
        entries.push((key.clone(), codomain_elems[value_idx].clone()));
    }
    entries
}
