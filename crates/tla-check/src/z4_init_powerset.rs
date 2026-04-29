// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! z4-based Init enumeration for nested powerset patterns (SUBSET(SUBSET S)).
//!
//! Bridges `tla-z4::translate::nested_powerset::NestedPowersetEncoder` into the
//! model checker's Init enumeration pipeline. When the Init predicate contains
//! a `SUBSET(SUBSET S)` with a cardinality filter, this module computes the
//! base elements (k-element subsets of S) and uses AllSAT enumeration to
//! produce all valid initial states.
//!
//! # SpanTreeTest5Nodes Pattern
//!
//! ```text
//! Edges \in {E \in SUBSET(SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
//! ```
//!
//! With Nodes = {n1, n2, n3, n4, n5}:
//! - SUBSET Nodes has 2^5 = 32 elements
//! - SUBSET(SUBSET Nodes) has 2^32 ~ 4 billion elements (infeasible)
//! - The Cardinality(e) = 2 filter reduces to C(5,2) = 10 edges
//! - SUBSET({10 edges}) = 2^10 = 1024 valid Edges values
//!
//! This module creates 10 Boolean SAT variables (one per edge) and uses
//! AllSAT to enumerate all 1024 assignments in ~milliseconds.
//!
//! Part of #3826.

use std::sync::Arc;

use tla_z4::translate::nested_powerset::{
    k_subsets, BaseElement, NestedPowersetConfig, NestedPowersetEncoder,
};

use crate::eval::{EvalCtx, Value};
use crate::init_strategy::InitAnalysis;
use crate::state::State;

/// Check whether an `InitAnalysis` indicates a nested powerset pattern
/// that can be handled by the specialized encoder.
///
/// Part of #3826.
#[must_use]
pub(crate) fn has_nested_powerset_pattern(analysis: &InitAnalysis) -> bool {
    analysis.reasons.iter().any(|r| {
        matches!(
            r,
            crate::init_strategy::Z4Reason::NestedSubsetPattern { .. }
        )
    })
}

/// Information about a detected nested powerset Init pattern.
///
/// Extracted from the Init predicate AST to configure the encoder.
#[derive(Debug, Clone)]
pub(crate) struct NestedPowersetInitInfo {
    /// The variable being constrained (e.g., "Edges").
    pub(crate) var_name: Arc<str>,
    /// Base elements for the SAT encoder (indexed by position).
    /// Each entry corresponds to a k-element subset used as a Boolean SAT variable.
    pub(crate) base_elements: Vec<BaseElement>,
    /// The actual TLA+ Value representation for each base element.
    /// Parallel to `base_elements` -- `value_base_elements[i]` is the set of Values
    /// that base element `i` represents. This is needed because base set elements
    /// may be model values (e.g., `n1, n2, ...`) rather than integers.
    ///
    /// Part of #3826: fixes model value support for SpanTreeTest5Nodes.
    pub(crate) value_base_elements: Vec<Vec<Value>>,
    /// Other Init conjuncts that provide deterministic values for other variables.
    /// Maps variable name to its deterministic value.
    pub(crate) deterministic_vars: Vec<(Arc<str>, Value)>,
}

/// Attempt to detect and extract a nested powerset Init pattern.
///
/// Looks for Init predicates of the form:
/// ```text
/// Init == /\ var1 = expr1
///         /\ var2 = expr2
///         /\ edges_var \in {E \in SUBSET(SUBSET S) : \A e \in E : Cardinality(e) = k}
/// ```
///
/// Returns `None` if the pattern is not detected or cannot be extracted.
///
/// Part of #3826.
pub(crate) fn detect_nested_powerset_init(
    ctx: &EvalCtx,
    init_expr: &tla_core::Spanned<tla_core::ast::Expr>,
    vars: &[Arc<str>],
) -> Option<NestedPowersetInitInfo> {
    use tla_core::ast::Expr;

    // Collect top-level conjuncts from the Init predicate.
    let mut conjuncts = Vec::new();
    collect_conjuncts(&init_expr.node, &mut conjuncts);

    if conjuncts.is_empty() {
        return None;
    }

    // Look for a conjunct that matches:
    //   var \in {E \in SUBSET(SUBSET S) : \A e \in E : Cardinality(e) = k}
    //
    // This is: Expr::In(var_ident, set_filter) where set_filter is
    //   Expr::SetFilter(bound_var, body) with bound_var.domain = SUBSET(SUBSET S)
    let mut powerset_var: Option<(Arc<str>, ExtractedBase)> = None;
    let mut deterministic_vars: Vec<(Arc<str>, Value)> = Vec::new();

    for conjunct in &conjuncts {
        match conjunct {
            // var = expr (deterministic assignment)
            Expr::Eq(lhs, rhs) => {
                if let Some(var_name) = extract_state_var_name(&lhs.node, vars) {
                    // Try to evaluate the RHS to get a deterministic value
                    if let Ok(val) = crate::eval::eval(ctx, rhs) {
                        deterministic_vars.push((var_name, val));
                    }
                }
            }
            // var \in set_expr (membership constraint)
            Expr::In(lhs, rhs) => {
                if let Some(var_name) = extract_state_var_name(&lhs.node, vars) {
                    if let Some(extracted) = try_extract_nested_powerset_base(ctx, &rhs.node) {
                        powerset_var = Some((var_name, extracted));
                    }
                }
            }
            _ => {}
        }
    }

    let (var_name, extracted) = powerset_var?;

    Some(NestedPowersetInitInfo {
        var_name,
        base_elements: extracted.base_elements,
        value_base_elements: extracted.value_subsets,
        deterministic_vars,
    })
}

/// Enumerate Init states using the nested powerset encoder.
///
/// Given the extracted pattern info, creates Boolean SAT variables for each
/// base element and enumerates all subsets using AllSAT. Each solution is
/// combined with the deterministic variable values to produce a complete State.
///
/// Part of #3826.
pub(crate) fn enumerate_nested_powerset_init(
    info: &NestedPowersetInitInfo,
) -> Result<Vec<State>, String> {
    let mut encoder = NestedPowersetEncoder::new(info.base_elements.clone())
        .map_err(|e| format!("failed to create nested powerset encoder: {e}"))?;

    let config = NestedPowersetConfig::default();
    let solution = encoder
        .enumerate_all(&config)
        .map_err(|e| format!("nested powerset enumeration failed: {e}"))?;

    eprintln!(
        "[z4-init-powerset] Enumerated {} solutions for {} ({} base elements)",
        solution.solutions.len(),
        info.var_name,
        info.base_elements.len(),
    );

    // Convert each solution to a State.
    //
    // If value_base_elements is populated (model value case), use value-based
    // reconstruction. Each BaseElement has members = [idx] where idx is the
    // sequential index into value_base_elements.
    //
    // Part of #3826: value-based reconstruction supports model values.
    let has_value_elements = !info.value_base_elements.is_empty();

    let states: Vec<State> = solution
        .solutions
        .iter()
        .map(|selected_edges| {
            let edge_set = if has_value_elements {
                // Map each selected BaseElement back to its index via members[0]
                let selected_indices: Vec<usize> = selected_edges
                    .iter()
                    .filter_map(|elem| elem.members.first().map(|&idx| idx as usize))
                    .collect();
                value_base_elements_to_value(&selected_indices, &info.value_base_elements)
            } else {
                // Legacy integer-based path
                base_elements_to_value(selected_edges)
            };

            // Combine with deterministic variables
            let mut pairs: Vec<(Arc<str>, Value)> = info.deterministic_vars.clone();
            pairs.push((Arc::clone(&info.var_name), edge_set));

            State::from_pairs(pairs)
        })
        .collect();

    Ok(states)
}

/// Convert selected base element indices into a TLA+ set-of-sets Value.
///
/// Each selected index maps to the corresponding entry in `value_elements`,
/// which is a `Vec<Value>` representing the inner set members.
/// The outer collection becomes a set of those inner sets.
///
/// Part of #3826: uses actual TLA+ Values (supports model values, not just integers).
fn value_base_elements_to_value(
    selected_indices: &[usize],
    value_elements: &[Vec<Value>],
) -> Value {
    use crate::value::SortedSet;

    let inner_sets: Vec<Value> = selected_indices
        .iter()
        .map(|&idx| {
            let members = &value_elements[idx];
            Value::Set(Arc::new(SortedSet::from_iter(members.iter().cloned())))
        })
        .collect();

    Value::Set(Arc::new(SortedSet::from_iter(inner_sets)))
}

/// Convert a list of `BaseElement` (selected edges) into a TLA+ set-of-sets Value.
///
/// Each `BaseElement` with members [a, b] becomes the set {a, b} in TLA+.
/// The outer collection becomes a set of those inner sets.
///
/// NOTE: Only works for integer-valued base elements. For model values, use
/// `value_base_elements_to_value` instead.
fn base_elements_to_value(elements: &[BaseElement]) -> Value {
    use crate::value::SortedSet;

    let inner_sets: Vec<Value> = elements
        .iter()
        .map(|elem| {
            let members: Vec<Value> = elem.members.iter().map(|&m| Value::int(m)).collect();
            Value::Set(Arc::new(SortedSet::from_iter(members)))
        })
        .collect();

    Value::Set(Arc::new(SortedSet::from_iter(inner_sets)))
}

/// Collect top-level conjuncts from a conjunction tree.
///
/// Flattens nested `And` expressions into a flat list of conjuncts.
fn collect_conjuncts<'a>(expr: &'a tla_core::ast::Expr, out: &mut Vec<&'a tla_core::ast::Expr>) {
    use tla_core::ast::Expr;

    match expr {
        Expr::And(a, b) => {
            collect_conjuncts(&a.node, out);
            collect_conjuncts(&b.node, out);
        }
        _ => out.push(expr),
    }
}

/// Extract the state variable name from an expression, if it references a known state var.
fn extract_state_var_name(expr: &tla_core::ast::Expr, vars: &[Arc<str>]) -> Option<Arc<str>> {
    use tla_core::ast::Expr;

    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            vars.iter().find(|v| v.as_ref() == name).cloned()
        }
        _ => None,
    }
}

/// Result of extracting base elements from a nested powerset pattern.
///
/// Contains both the SAT-encoder-compatible `BaseElement`s (using sequential
/// integer indices) and the actual TLA+ `Value` representations for each
/// k-subset, so that model values (e.g., `n1, n2`) are preserved correctly.
///
/// Part of #3826.
struct ExtractedBase {
    /// SAT-encoder-compatible base elements with sequential integer indices.
    base_elements: Vec<BaseElement>,
    /// Actual TLA+ Value representations, parallel to `base_elements`.
    /// `value_subsets[i]` is the `Vec<Value>` for the k-subset at index `i`.
    value_subsets: Vec<Vec<Value>>,
}

/// Compute k-element subsets of a list of `Value`s.
///
/// Like `k_subsets` but works with arbitrary TLA+ Values (model values, strings, etc.)
/// instead of only integers. Returns pairs of (sequential index `BaseElement`, `Vec<Value>`).
///
/// Part of #3826: generalized for model value support.
fn k_subsets_of_values(elements: &[Value], k: usize) -> ExtractedBase {
    let n = elements.len();
    if k > n {
        return ExtractedBase {
            base_elements: Vec::new(),
            value_subsets: Vec::new(),
        };
    }
    if k == 0 {
        return ExtractedBase {
            base_elements: vec![BaseElement {
                members: Vec::new(),
            }],
            value_subsets: vec![Vec::new()],
        };
    }

    let mut base_elements = Vec::new();
    let mut value_subsets = Vec::new();
    let mut indices = (0..k).collect::<Vec<_>>();
    let mut seq_idx: i64 = 0;

    loop {
        // Emit current combination as Values
        let value_members: Vec<Value> = indices.iter().map(|&i| elements[i].clone()).collect();
        value_subsets.push(value_members);

        // Create a BaseElement with sequential index (SAT solver only needs the count)
        base_elements.push(BaseElement {
            members: vec![seq_idx],
        });
        seq_idx += 1;

        // Advance to next combination
        let mut i = k;
        loop {
            if i == 0 {
                return ExtractedBase {
                    base_elements,
                    value_subsets,
                };
            }
            i -= 1;
            indices[i] += 1;
            if indices[i] <= n - k + i {
                break;
            }
        }
        // Reset subsequent indices
        for j in (i + 1)..k {
            indices[j] = indices[j - 1] + 1;
        }
    }
}

/// Try to extract the base elements from a set expression that matches the
/// nested powerset pattern:
///
/// ```text
/// {E \in SUBSET(SUBSET S) : \A e \in E : Cardinality(e) = k}
/// ```
///
/// Returns the extracted base information if the pattern matches.
/// Supports both integer and model value base sets.
///
/// Part of #3826: generalized for model value support (SpanTreeTest5Nodes).
fn try_extract_nested_powerset_base(
    ctx: &EvalCtx,
    expr: &tla_core::ast::Expr,
) -> Option<ExtractedBase> {
    use tla_core::ast::Expr;

    // Must be a SetFilter: {E \in domain : predicate}
    let (bound_var, predicate) = match expr {
        Expr::SetFilter(bv, pred) => (bv, pred),
        _ => return None,
    };

    // Domain must be SUBSET(SUBSET S) or SUBSET(X) where X is a powerset
    let inner_set = match bound_var.domain.as_deref() {
        Some(domain_expr) => match &domain_expr.node {
            Expr::Powerset(inner) => match &inner.node {
                // SUBSET(SUBSET S) — the classic pattern
                Expr::Powerset(base) => Some(base.as_ref()),
                _ => None,
            },
            _ => None,
        },
        None => return None,
    }?;

    // Try to evaluate the base set S to get its elements as Values.
    // This works for both integer sets and model value sets.
    let base_value = crate::eval::eval(ctx, inner_set).ok()?;
    let base_values: Vec<Value> = base_value.iter_set()?.collect();

    if base_values.is_empty() {
        return None;
    }

    // Extract the cardinality constraint from the predicate.
    // Pattern: \A e \in E : Cardinality(e) = k
    let cardinality = try_extract_forall_cardinality_eq(&predicate.node, &bound_var.name.node)?;

    // Compute k-element subsets of the actual Values
    let extracted = k_subsets_of_values(&base_values, cardinality);

    if extracted.base_elements.is_empty() {
        return None;
    }

    eprintln!(
        "[z4-init-powerset] Detected nested powerset pattern: |S|={}, k={}, C({},{})={} base elements",
        base_values.len(),
        cardinality,
        base_values.len(),
        cardinality,
        extracted.base_elements.len(),
    );

    Some(extracted)
}

/// Try to extract cardinality k from a predicate of the form:
///
/// ```text
/// \A e \in E : Cardinality(e) = k
/// ```
///
/// where E is the outer bound variable name.
fn try_extract_forall_cardinality_eq(
    expr: &tla_core::ast::Expr,
    outer_var_name: &str,
) -> Option<usize> {
    use tla_core::ast::Expr;

    // Must be Forall with one bound variable
    let (bounds, body) = match expr {
        Expr::Forall(bounds, body) => (bounds, body),
        _ => return None,
    };

    if bounds.len() != 1 {
        return None;
    }

    let inner_bound = &bounds[0];

    // The domain must be the outer variable: \A e \in E
    let domain = inner_bound.domain.as_deref()?;
    match &domain.node {
        Expr::Ident(name, _) if name == outer_var_name => {}
        _ => return None,
    }

    // Body must be Cardinality(e) = k
    try_extract_cardinality_eq_from_body(&body.node, &inner_bound.name.node)
}

/// Try to extract k from: Cardinality(var_name) = k
fn try_extract_cardinality_eq_from_body(
    expr: &tla_core::ast::Expr,
    _var_name: &str,
) -> Option<usize> {
    use tla_core::ast::Expr;

    // Pattern: Cardinality(x) = k  (represented as Eq(Apply(Ident("Cardinality"), [x]), Int(k)))
    let (lhs, rhs) = match expr {
        Expr::Eq(l, r) => (&l.node, &r.node),
        _ => return None,
    };

    // Try both orderings: Cardinality(x) = k and k = Cardinality(x)
    if let Some(k) = try_cardinality_eq_pair(lhs, rhs) {
        return Some(k);
    }
    try_cardinality_eq_pair(rhs, lhs)
}

/// Check if (a, b) matches (Cardinality(x), Int(k)) and return k.
fn try_cardinality_eq_pair(a: &tla_core::ast::Expr, b: &tla_core::ast::Expr) -> Option<usize> {
    use tla_core::ast::Expr;

    // Check if a is Cardinality(x)
    let is_cardinality_call = match a {
        Expr::Apply(func, args) => {
            args.len() == 1
                && matches!(
                    &func.node,
                    Expr::Ident(name, _) if name == "Cardinality"
                )
        }
        _ => false,
    };

    if !is_cardinality_call {
        return None;
    }

    // Check if b is Int(k)
    match b {
        Expr::Int(k) => {
            let k_val: usize = k.try_into().ok()?;
            Some(k_val)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_base_elements_to_value_empty() {
        let val = base_elements_to_value(&[]);
        assert_eq!(val, Value::Set(Arc::new(crate::value::SortedSet::new())));
    }

    #[test]
    fn test_base_elements_to_value_single_edge() {
        let elements = vec![BaseElement {
            members: vec![1, 2],
        }];
        let val = base_elements_to_value(&elements);
        // Should be {{1, 2}}
        if let Value::Set(outer) = &val {
            assert_eq!(outer.len(), 1);
        } else {
            panic!("expected Set value");
        }
    }

    #[test]
    fn test_base_elements_to_value_multiple_edges() {
        let elements = vec![
            BaseElement {
                members: vec![1, 2],
            },
            BaseElement {
                members: vec![3, 4],
            },
        ];
        let val = base_elements_to_value(&elements);
        if let Value::Set(outer) = &val {
            assert_eq!(outer.len(), 2);
        } else {
            panic!("expected Set value");
        }
    }

    #[test]
    fn test_has_nested_powerset_pattern_positive() {
        use crate::init_strategy::{InitAnalysis, Z4Reason};
        let analysis = InitAnalysis::z4_smt(
            vec![Z4Reason::NestedSubsetPattern {
                description: "test".to_string(),
            }],
            80,
        );
        assert!(has_nested_powerset_pattern(&analysis));
    }

    #[test]
    fn test_has_nested_powerset_pattern_negative() {
        use crate::init_strategy::InitAnalysis;
        let analysis = InitAnalysis::brute_force();
        assert!(!has_nested_powerset_pattern(&analysis));
    }

    #[test]
    fn test_collect_conjuncts_single() {
        use tla_core::ast::Expr;
        let expr = Expr::Bool(true);
        let mut out = Vec::new();
        collect_conjuncts(&expr, &mut out);
        assert_eq!(out.len(), 1);
    }

    #[cfg(feature = "z4")]
    #[cfg_attr(test, ntest::timeout(60000))]
    #[test]
    fn test_enumerate_nested_powerset_init_five_nodes() {
        // Simulate SpanTreeTest5Nodes: 5 nodes, C(5,2) = 10 edges, 2^10 = 1024 Init states
        let nodes: Vec<i64> = (1..=5).collect();
        let edges = k_subsets(&nodes, 2);
        assert_eq!(edges.len(), 10);

        let info = NestedPowersetInitInfo {
            var_name: Arc::from("Edges"),
            base_elements: edges,
            value_base_elements: vec![],
            deterministic_vars: vec![],
        };

        let states = enumerate_nested_powerset_init(&info).expect("enumeration should succeed");
        assert_eq!(
            states.len(),
            1024,
            "SpanTreeTest5Nodes should have 1024 edge configurations"
        );
    }

    #[cfg(feature = "z4")]
    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_enumerate_nested_powerset_init_four_nodes() {
        // 4 nodes: C(4,2) = 6 edges, 2^6 = 64 Init states
        let nodes: Vec<i64> = (1..=4).collect();
        let edges = k_subsets(&nodes, 2);
        assert_eq!(edges.len(), 6);

        let info = NestedPowersetInitInfo {
            var_name: Arc::from("Edges"),
            base_elements: edges,
            value_base_elements: vec![],
            deterministic_vars: vec![],
        };

        let states = enumerate_nested_powerset_init(&info).expect("enumeration should succeed");
        assert_eq!(states.len(), 64);
    }

    #[cfg(feature = "z4")]
    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_enumerate_nested_powerset_with_deterministic_vars() {
        // Simulate: mom = [n \in Nodes |-> n], Edges in SUBSET(...)
        let nodes: Vec<i64> = (1..=3).collect();
        let edges = k_subsets(&nodes, 2);
        assert_eq!(edges.len(), 3); // C(3,2) = 3

        let mom_val = Value::int(42); // Simplified deterministic value

        let info = NestedPowersetInitInfo {
            var_name: Arc::from("Edges"),
            base_elements: edges,
            value_base_elements: vec![],
            deterministic_vars: vec![(Arc::from("mom"), mom_val)],
        };

        let states = enumerate_nested_powerset_init(&info).expect("enumeration should succeed");
        assert_eq!(states.len(), 8); // 2^3 = 8

        // Each state should have both "Edges" and "mom" variables
        for state in &states {
            assert!(
                state.get("Edges").is_some(),
                "state should have Edges variable"
            );
            assert!(state.get("mom").is_some(), "state should have mom variable");
        }
    }

    #[cfg(feature = "z4")]
    #[cfg_attr(test, ntest::timeout(60000))]
    #[test]
    fn test_enumerate_nested_powerset_with_model_values() {
        // Part of #3826: Test that model values (non-integer) are preserved correctly.
        // Simulates SpanTreeTest5Nodes with Nodes = {n1, n2, n3, n4, n5} as model values.
        use tla_value::interned_model_value;

        let n1 = interned_model_value("n1").expect("create model value n1");
        let n2 = interned_model_value("n2").expect("create model value n2");
        let n3 = interned_model_value("n3").expect("create model value n3");

        // 3 nodes → C(3,2) = 3 edges → 2^3 = 8 Init states
        let node_values = vec![n1.clone(), n2.clone(), n3.clone()];
        let extracted = k_subsets_of_values(&node_values, 2);
        assert_eq!(extracted.base_elements.len(), 3);
        assert_eq!(extracted.value_subsets.len(), 3);

        let info = NestedPowersetInitInfo {
            var_name: Arc::from("Edges"),
            base_elements: extracted.base_elements,
            value_base_elements: extracted.value_subsets,
            deterministic_vars: vec![],
        };

        let states = enumerate_nested_powerset_init(&info).expect("enumeration should succeed");
        assert_eq!(states.len(), 8, "2^3 = 8 subsets of 3 edges");

        // Verify that the Edges values contain model values, not integers
        for state in &states {
            let edges_val = state.get("Edges").expect("state should have Edges");
            if let Value::Set(outer) = edges_val {
                for inner_val in outer.iter() {
                    if let Value::Set(inner) = inner_val {
                        for member in inner.iter() {
                            assert!(
                                matches!(member, Value::ModelValue(_)),
                                "edge members should be ModelValues, got: {:?}",
                                member
                            );
                        }
                    }
                }
            } else {
                panic!("Edges should be a Set value");
            }
        }
    }

    #[test]
    fn test_k_subsets_of_values_basic() {
        let values = vec![Value::int(10), Value::int(20), Value::int(30)];
        let extracted = k_subsets_of_values(&values, 2);
        assert_eq!(extracted.base_elements.len(), 3); // C(3,2) = 3
        assert_eq!(extracted.value_subsets.len(), 3);
        // Check first subset is {10, 20}
        assert_eq!(extracted.value_subsets[0].len(), 2);
        assert_eq!(extracted.value_subsets[0][0], Value::int(10));
        assert_eq!(extracted.value_subsets[0][1], Value::int(20));
    }

    #[test]
    fn test_k_subsets_of_values_empty() {
        let values = vec![Value::int(1), Value::int(2)];
        let extracted = k_subsets_of_values(&values, 0);
        assert_eq!(extracted.base_elements.len(), 1);
        assert_eq!(extracted.value_subsets.len(), 1);
        assert!(extracted.value_subsets[0].is_empty());
    }

    #[test]
    fn test_k_subsets_of_values_k_too_large() {
        let values = vec![Value::int(1)];
        let extracted = k_subsets_of_values(&values, 3);
        assert!(extracted.base_elements.is_empty());
        assert!(extracted.value_subsets.is_empty());
    }

    #[test]
    fn test_value_base_elements_to_value_basic() {
        use crate::value::SortedSet;

        let value_elements = vec![
            vec![Value::int(1), Value::int(2)],
            vec![Value::int(3), Value::int(4)],
            vec![Value::int(5), Value::int(6)],
        ];

        // Select indices 0 and 2
        let val = value_base_elements_to_value(&[0, 2], &value_elements);
        if let Value::Set(outer) = &val {
            assert_eq!(outer.len(), 2, "should have 2 inner sets");
        } else {
            panic!("expected Set value");
        }
    }
}
