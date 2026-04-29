// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Part of #3432: shared constrained-SUBSET matcher and runtime generator.

use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_value::{SortedSet, Value};

use super::subset_profile;

pub(crate) struct ConstrainedSubsetPattern<'a> {
    pub(crate) base_set_expr: &'a Spanned<Expr>,
    pub(crate) superset_expr: &'a Spanned<Expr>,
    pub(crate) subset_expr: &'a Spanned<Expr>,
    pub(crate) remaining_body: Option<Spanned<Expr>>,
}

pub(crate) fn match_constrained_subset_exists<'a>(
    var_name: &str,
    domain_expr: &'a Spanned<Expr>,
    body: &'a Spanned<Expr>,
) -> Option<ConstrainedSubsetPattern<'a>> {
    let base_set_expr = match &domain_expr.node {
        Expr::Powerset(inner) => inner.as_ref(),
        _ => return None,
    };

    let conjuncts = flatten_conjunction(body);
    if conjuncts.len() < 2 {
        return None;
    }

    let mut superset_idx = None;
    let mut subset_idx = None;

    for (idx, conjunct) in conjuncts.iter().enumerate() {
        let Expr::Subseteq(left, right) = &conjunct.node else {
            continue;
        };

        if is_bare_ident(&left.node, var_name) {
            if superset_idx.replace(idx).is_some() {
                return None;
            }
            continue;
        }
        if is_bare_ident(&right.node, var_name) {
            if subset_idx.replace(idx).is_some() {
                return None;
            }
        }
    }

    let superset_idx = superset_idx?;
    let subset_idx = subset_idx?;

    let superset_expr = match &conjuncts[superset_idx].node {
        Expr::Subseteq(_, right) => right.as_ref(),
        _ => unreachable!(),
    };
    let subset_expr = match &conjuncts[subset_idx].node {
        Expr::Subseteq(left, _) => left.as_ref(),
        _ => unreachable!(),
    };

    let remaining_body = reconstruct_remaining_body(body, &conjuncts, &[superset_idx, subset_idx]);

    Some(ConstrainedSubsetPattern {
        base_set_expr,
        superset_expr,
        subset_expr,
        remaining_body,
    })
}

/// Generate all subsets `r` of `base_elements` where `subset_bound ⊆ r ⊆ superset_bound`.
///
/// Returns `None` when membership checks are indeterminate, signaling the caller
/// to fall back to the generic SUBSET enumeration path.
pub(crate) fn generate_constrained_subsets(
    base_elements: &[Value],
    superset_bound: &Value,
    subset_bound: &Value,
) -> Option<Vec<Value>> {
    let x_elements: Vec<&Value> = match subset_bound {
        Value::Set(set) => set.iter().collect(),
        _ => {
            subset_profile::record_success(0, 0);
            return Some(Vec::new());
        }
    };

    for x_elem in &x_elements {
        match superset_bound.set_contains(x_elem) {
            Some(true) => {}
            Some(false) => {
                subset_profile::record_success(0, 0);
                return Some(Vec::new());
            }
            None => {
                subset_profile::record_fallback();
                return None;
            }
        }
        if !base_elements.contains(x_elem) {
            subset_profile::record_success(0, 0);
            return Some(Vec::new());
        }
    }

    let mut free_elements: Vec<&Value> = Vec::new();
    for base_elem in base_elements {
        match superset_bound.set_contains(base_elem) {
            Some(true) => {
                if x_elements.iter().all(|x| *x != base_elem) {
                    free_elements.push(base_elem);
                }
            }
            Some(false) => {}
            None => {
                subset_profile::record_fallback();
                return None;
            }
        }
    }

    let num_free = free_elements.len();
    if num_free > 20 {
        subset_profile::record_fallback();
        return None;
    }
    debug_assert!(
        num_free <= 31,
        "count_ones via u32 truncation requires num_free <= 31"
    );

    // Part of #3364: Pre-sort free_elements so we can merge-insert instead of
    // sorting each generated subset. Combined with k-subset combinatorial
    // iteration this reduces from O(n * 2^n) bitmask scanning to O(2^n) direct
    // enumeration, and from O(k log k) per-subset sort to O(k) merge.
    free_elements.sort_by(|a, b| a.cmp(b));
    let x_sorted: Vec<Value> = x_elements.iter().map(|v| (*v).clone()).collect();

    let count = 1usize << num_free;
    let mut result = Vec::with_capacity(count);

    for k in 0..=num_free {
        if k == 0 {
            // No free elements selected — just the mandatory subset bound.
            result.push(Value::from_sorted_set(SortedSet::from_sorted_vec(
                x_sorted.clone(),
            )));
            continue;
        }
        // Enumerate all k-subsets of free_elements using index iteration.
        let mut indices: Vec<usize> = (0..k).collect();
        loop {
            let selected_free: Vec<Value> =
                indices.iter().map(|&i| free_elements[i].clone()).collect();
            let merged = merge_sorted(&x_sorted, &selected_free);
            result.push(Value::from_sorted_set(SortedSet::from_sorted_vec(merged)));
            if !advance_k_subset_indices(&mut indices, num_free) {
                break;
            }
        }
    }

    subset_profile::record_success(free_elements.len(), result.len());
    Some(result)
}

/// Merge two sorted `Value` slices into a single sorted `Vec<Value>`.
/// Both inputs must be sorted by `Value::cmp`. O(a.len() + b.len()).
fn merge_sorted(a: &[Value], b: &[Value]) -> Vec<Value> {
    let mut result = Vec::with_capacity(a.len() + b.len());
    let mut ai = 0;
    let mut bi = 0;
    while ai < a.len() && bi < b.len() {
        if a[ai] <= b[bi] {
            result.push(a[ai].clone());
            ai += 1;
        } else {
            result.push(b[bi].clone());
            bi += 1;
        }
    }
    while ai < a.len() {
        result.push(a[ai].clone());
        ai += 1;
    }
    while bi < b.len() {
        result.push(b[bi].clone());
        bi += 1;
    }
    result
}

/// Advance a k-subset index array to the next combination in lexicographic order.
/// Returns `false` when all combinations have been exhausted.
/// `indices` must be a sorted array of `k` distinct indices in `0..n`.
fn advance_k_subset_indices(indices: &mut [usize], n: usize) -> bool {
    let k = indices.len();
    let mut i = k;
    while i > 0 {
        i -= 1;
        if indices[i] < n - k + i {
            indices[i] += 1;
            for j in (i + 1)..k {
                indices[j] = indices[j - 1] + 1;
            }
            return true;
        }
    }
    false
}

fn reconstruct_remaining_body(
    original_body: &Spanned<Expr>,
    conjuncts: &[&Spanned<Expr>],
    removed_indices: &[usize],
) -> Option<Spanned<Expr>> {
    let mut remaining = conjuncts
        .iter()
        .enumerate()
        .filter(|(idx, _)| !removed_indices.contains(idx))
        .map(|(_, conjunct)| (*conjunct).clone());

    let first = remaining.next()?;
    Some(remaining.fold(first, |acc, next| {
        Spanned::new(Expr::And(Box::new(acc), Box::new(next)), original_body.span)
    }))
}

fn flatten_conjunction<'a>(expr: &'a Spanned<Expr>) -> Vec<&'a Spanned<Expr>> {
    let mut result = Vec::new();
    flatten_conjunction_inner(expr, &mut result);
    result
}

fn flatten_conjunction_inner<'a>(expr: &'a Spanned<Expr>, out: &mut Vec<&'a Spanned<Expr>>) {
    match &expr.node {
        Expr::And(left, right) => {
            flatten_conjunction_inner(left, out);
            flatten_conjunction_inner(right, out);
        }
        _ => out.push(expr),
    }
}

fn is_bare_ident(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Ident(ident, _) if ident.as_str() == name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_subset_bound() {
        let base = vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)];
        let superset = Value::set(base.clone());
        let subset = Value::empty_set();

        let results = generate_constrained_subsets(&base, &superset, &subset).unwrap();
        assert_eq!(results.len(), 8);
        let sizes: Vec<usize> = results
            .iter()
            .map(|value| match value {
                Value::Set(set) => set.len(),
                _ => panic!("expected set"),
            })
            .collect();
        assert_eq!(sizes, vec![0, 1, 1, 1, 2, 2, 2, 3]);
    }

    #[test]
    fn test_tight_constraints() {
        let base = vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)];
        let superset = Value::set(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let subset = Value::set(vec![Value::SmallInt(1)]);

        let results = generate_constrained_subsets(&base, &superset, &subset).unwrap();
        assert_eq!(results.len(), 2);
        assert!(results.contains(&Value::set(vec![Value::SmallInt(1)])));
        assert!(results.contains(&Value::set(vec![Value::SmallInt(1), Value::SmallInt(2)])));
    }

    #[test]
    fn test_unsatisfiable_x_not_in_t() {
        let base = vec![Value::SmallInt(1), Value::SmallInt(2)];
        let superset = Value::set(vec![Value::SmallInt(1)]);
        let subset = Value::set(vec![Value::SmallInt(2)]);

        let results = generate_constrained_subsets(&base, &superset, &subset).unwrap();
        assert!(results.is_empty());
    }

    #[test]
    fn test_all_free() {
        let base = vec![Value::SmallInt(1), Value::SmallInt(2)];
        let superset = Value::set(base.clone());
        let subset = Value::empty_set();

        let results = generate_constrained_subsets(&base, &superset, &subset).unwrap();
        assert_eq!(results.len(), 4);
        let sizes: Vec<usize> = results
            .iter()
            .map(|value| match value {
                Value::Set(set) => set.len(),
                _ => panic!("expected set"),
            })
            .collect();
        assert_eq!(sizes, vec![0, 1, 1, 2]);
    }
}
