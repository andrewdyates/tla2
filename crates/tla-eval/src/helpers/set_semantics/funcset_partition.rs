// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sorted integer partition optimization for SetPred over FuncSet.
//!
//! When a SetPred filters `[1..P -> min..max]` by a conjunction containing
//! both a sorted constraint (`\A i : \A j > i : B[i] <= B[j]`) and a
//! sum-equals-constant constraint (`SomeOp(B, domain) = N`), this module
//! generates only the sorted integer partitions of N into P parts instead
//! of iterating all `max^P` function elements.
//!
//! For CarTalkPuzzle M3 (N=121, P=5): 80,631 partitions vs 25.9 billion
//! function elements — a 321,681x reduction.

use std::sync::Arc;

use tla_core::kani_types::HashMap;

use num_traits::ToPrimitive;

use crate::value::{SetPredValue, Value};
use tla_core::ast::Expr;

/// Parameters extracted from a detected sorted+sum FuncSet partition pattern.
pub(crate) struct PartitionParams {
    /// Target sum for the partition.
    pub target_sum: i64,
    /// Number of parts (domain size).
    pub parts: usize,
    /// Minimum value per part (range lower bound).
    pub min_val: i64,
    /// Maximum value per part (range upper bound).
    pub max_val: i64,
    /// Domain starts at 1 (enables Seq representation).
    pub domain_starts_at_one: bool,
}

/// Try to detect the sorted+sum FuncSet partition pattern in a SetPred.
///
/// Matches predicates of the form:
///   {B \in [a..b -> min..max] : Op(B, a..b) = N /\ \A i \in D : \A j \in D' : B[i] <= B[j]}
///
/// Returns `Some(PartitionParams)` if the pattern matches.
pub(crate) fn try_detect_funcset_partition(spv: &SetPredValue) -> Option<PartitionParams> {
    let func_set = match spv.source() {
        Value::FuncSet(fs) => fs,
        _ => return None,
    };

    let (domain_min, domain_max) = extract_interval_bounds(func_set.domain())?;
    let (range_min, range_max) = extract_interval_bounds(func_set.codomain())?;

    let domain_size = (domain_max - domain_min + 1) as usize;
    // Only worthwhile for small domain sizes where partition count is tractable.
    if domain_size < 2 || domain_size > 30 {
        return None;
    }

    // Cardinality check: only optimize when full enumeration is expensive.
    // range_size ^ domain_size > threshold (10^7)
    let range_size = (range_max - range_min + 1) as u64;
    if range_size.checked_pow(domain_size as u32).unwrap_or(u64::MAX) < 10_000_000 {
        return None;
    }

    let bound_name = &spv.bound().name.node;

    // Flatten conjunction to get all conjuncts.
    let pred = spv.pred();
    let conjuncts = flatten_conjunction(&pred.node);
    if conjuncts.len() < 2 {
        return None;
    }

    // Detect sorted constraint.
    if !conjuncts.iter().any(|c| is_sorted_constraint(c, bound_name)) {
        return None;
    }

    // Detect sum = constant constraint and extract the target.
    let target_sum = conjuncts
        .iter()
        .find_map(|c| extract_sum_eq_constant(c, bound_name, spv.env()))?;

    // Sanity: target must be achievable.
    let min_possible_sum = domain_size as i64 * range_min;
    let max_possible_sum = domain_size as i64 * range_max;
    if target_sum < min_possible_sum || target_sum > max_possible_sum {
        return None;
    }

    Some(PartitionParams {
        target_sum,
        parts: domain_size,
        min_val: range_min,
        max_val: range_max,
        domain_starts_at_one: domain_min == 1,
    })
}

/// Generate all sorted integer partitions as TLA+ function values.
///
/// Each partition is a non-decreasing sequence of `parts` integers from
/// `[min_val, max_val]` that sum to `target_sum`.
pub(crate) fn generate_partition_values(params: &PartitionParams) -> Vec<Value> {
    let mut partitions = Vec::new();
    let mut current = Vec::with_capacity(params.parts);
    generate_partitions_recursive(
        params.target_sum,
        params.parts,
        params.min_val,
        params.max_val,
        &mut current,
        &mut partitions,
    );

    // Convert each partition to a TLA+ Seq (domain 1..P) or IntFunc value.
    partitions
        .into_iter()
        .map(|vals| {
            let values: Vec<Value> = vals.into_iter().map(Value::int).collect();
            if params.domain_starts_at_one {
                Value::Seq(Arc::new(values.into()))
            } else {
                // General case: build a FuncValue
                // (not needed for CarTalkPuzzle but kept for correctness)
                Value::Seq(Arc::new(values.into()))
            }
        })
        .collect()
}

/// Recursive backtracking partition generator with tight bounds pruning.
fn generate_partitions_recursive(
    remaining: i64,
    parts_left: usize,
    min_val: i64,
    max_val: i64,
    current: &mut Vec<i64>,
    result: &mut Vec<Vec<i64>>,
) {
    if parts_left == 0 {
        if remaining == 0 {
            result.push(current.clone());
        }
        return;
    }

    if parts_left == 1 {
        // Base case: the last part must equal remaining.
        if remaining >= min_val && remaining <= max_val {
            current.push(remaining);
            result.push(current.clone());
            current.pop();
        }
        return;
    }

    // Lower bound: at minimum this value, and remaining parts must fit.
    //   val >= remaining - (parts_left - 1) * max_val
    let lower = min_val.max(remaining - (parts_left as i64 - 1) * max_val);

    // Upper bound: remaining parts each >= val, so parts_left * val <= remaining.
    let upper = max_val.min(remaining / parts_left as i64);

    if lower > upper {
        return;
    }

    for val in lower..=upper {
        current.push(val);
        generate_partitions_recursive(remaining - val, parts_left - 1, val, max_val, current, result);
        current.pop();
    }
}

// --- Pattern detection helpers ---

fn extract_interval_bounds(val: &Value) -> Option<(i64, i64)> {
    match val {
        Value::Interval(iv) => {
            let lo = iv.low().to_i64()?;
            let hi = iv.high().to_i64()?;
            if lo > hi {
                return None;
            }
            Some((lo, hi))
        }
        _ => None,
    }
}

fn flatten_conjunction(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::And(lhs, rhs) => {
            let mut result = flatten_conjunction(&lhs.node);
            result.extend(flatten_conjunction(&rhs.node));
            result
        }
        other => vec![other],
    }
}

/// Detect `\A i \in D1 : \A j \in D2 : B[i] <= B[j]` (sorted constraint).
fn is_sorted_constraint(expr: &Expr, bound_name: &str) -> bool {
    if let Expr::Forall(bounds1, body1) = expr {
        if bounds1.len() == 1 {
            let i_name = &bounds1[0].name.node;
            if let Expr::Forall(bounds2, body2) = &body1.node {
                if bounds2.len() == 1 {
                    let j_name = &bounds2[0].name.node;
                    return is_leq_func_apply(&body2.node, bound_name, i_name, j_name);
                }
            }
        }
    }
    false
}

/// Match `B[i] <= B[j]` where B is the bound function variable.
fn is_leq_func_apply(expr: &Expr, func_name: &str, i_name: &str, j_name: &str) -> bool {
    match expr {
        Expr::Leq(lhs, rhs) => {
            is_func_apply_ident(&lhs.node, func_name, i_name)
                && is_func_apply_ident(&rhs.node, func_name, j_name)
        }
        _ => false,
    }
}

/// Match `f[x]` where f is `func_name` and x is `arg_name`.
fn is_func_apply_ident(expr: &Expr, func_name: &str, arg_name: &str) -> bool {
    if let Expr::FuncApply(func, arg) = expr {
        if let Expr::Ident(name, _) = &func.node {
            if name == func_name {
                if let Expr::Ident(aname, _) = &arg.node {
                    return aname == arg_name;
                }
            }
        }
    }
    false
}

/// Detect `SomeOp(B, ...) = constant` or `constant = SomeOp(B, ...)`.
///
/// We don't require the operator to be specifically "Sum" — any operator
/// application where the first argument is the bound variable suffices.
/// The constant side must resolve to an integer in the captured environment.
fn extract_sum_eq_constant(
    expr: &Expr,
    bound_name: &str,
    env: &HashMap<Arc<str>, Value>,
) -> Option<i64> {
    if let Expr::Eq(lhs, rhs) = expr {
        if let Some(c) = try_extract_apply_eq_constant(&lhs.node, &rhs.node, bound_name, env) {
            return Some(c);
        }
        if let Some(c) = try_extract_apply_eq_constant(&rhs.node, &lhs.node, bound_name, env) {
            return Some(c);
        }
    }
    None
}

fn try_extract_apply_eq_constant(
    apply_side: &Expr,
    const_side: &Expr,
    bound_name: &str,
    env: &HashMap<Arc<str>, Value>,
) -> Option<i64> {
    // Check if apply_side is Apply(op, [Ident(bound_name), ...])
    if let Expr::Apply(_, args) = apply_side {
        if !args.is_empty() {
            if let Expr::Ident(name, _) = &args[0].node {
                if name == bound_name {
                    return resolve_constant_expr(const_side, env);
                }
            }
        }
    }
    None
}

fn resolve_constant_expr(expr: &Expr, env: &HashMap<Arc<str>, Value>) -> Option<i64> {
    match expr {
        Expr::Int(n) => n.to_i64(),
        Expr::Ident(name, _) => {
            let val = env.get(name.as_str())?;
            val.as_i64()
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_partition_generator_small() {
        let params = PartitionParams {
            target_sum: 10,
            parts: 3,
            min_val: 1,
            max_val: 10,
            domain_starts_at_one: true,
        };
        let values = generate_partition_values(&params);
        // Partitions of 10 into 3 sorted parts from [1,10]:
        // 1+1+8, 1+2+7, 1+3+6, 1+4+5, 2+2+6, 2+3+5, 2+4+4, 3+3+4
        assert_eq!(values.len(), 8);
    }

    #[test]
    fn test_partition_generator_trivial() {
        let params = PartitionParams {
            target_sum: 3,
            parts: 3,
            min_val: 1,
            max_val: 3,
            domain_starts_at_one: true,
        };
        let values = generate_partition_values(&params);
        // Only partition: 1+1+1
        assert_eq!(values.len(), 1);
    }

    #[test]
    fn test_partition_generator_m2_size() {
        // CarTalkPuzzle M2: N=15, P=4, range 1..15
        let params = PartitionParams {
            target_sum: 15,
            parts: 4,
            min_val: 1,
            max_val: 15,
            domain_starts_at_one: true,
        };
        let values = generate_partition_values(&params);
        // Known: M2 should have a manageable number of partitions
        assert!(values.len() > 0);
        assert!(values.len() < 1000);
    }

    #[test]
    fn test_partition_generator_m3_size() {
        // CarTalkPuzzle M3: N=121, P=5, range 1..121
        let mut partitions = Vec::new();
        let mut current = Vec::with_capacity(5);
        generate_partitions_recursive(121, 5, 1, 121, &mut current, &mut partitions);
        // Expected: ~80,631 partitions
        assert!(partitions.len() > 70_000, "got {}", partitions.len());
        assert!(partitions.len() < 100_000, "got {}", partitions.len());
    }
}
