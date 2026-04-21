// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for SetPredValue trait contract compliance.
//!
//! Verifies that PartialEq, Ord, and Hash are mutually consistent,
//! especially across different source spans. Filed as #2030.

use super::super::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_core::ast::BoundVar;
use tla_core::span::{FileId, Span};
use tla_core::Spanned;

fn compute_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Regression test for #2030: SetPredValue PartialEq must be consistent with Ord
/// when predicates have the same AST node but different source spans.
///
/// Before the fix, PartialEq compared `Arc<Spanned<Expr>>` directly (including span),
/// while Ord only compared `pred.node` via Debug (excluding span).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_partialeq_ord_consistency_different_pred_spans() {
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };

    // Same predicate node, different source spans.
    let pred1 = Spanned::new(Expr::Bool(true), Span::new(FileId(0), 10, 20));
    let pred2 = Spanned::new(Expr::Bool(true), Span::new(FileId(0), 50, 60));

    let spv1 = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        pred1,
        HashMap::new(),
        None,
        None,
    );
    let spv2 = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        pred2,
        HashMap::new(),
        None,
        None,
    );

    // Ord should say Equal (same pred.node).
    assert_eq!(
        spv1.cmp(&spv2),
        std::cmp::Ordering::Equal,
        "Ord should compare SetPred structurally (ignoring pred span)"
    );

    // PartialEq MUST agree with Ord (contract: a == b iff a.cmp(b) == Equal).
    assert_eq!(
        spv1, spv2,
        "PartialEq must be consistent with Ord: same pred node → equal (#2030)"
    );

    // Hash MUST agree with PartialEq (contract: a == b → hash(a) == hash(b)).
    assert_eq!(
        compute_hash(&spv1),
        compute_hash(&spv2),
        "Hash must be consistent with PartialEq: equal values → equal hashes"
    );
}

/// Ensure that SetPredValues with different pred nodes remain distinguishable.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_different_pred_nodes_are_distinct() {
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };

    let spv1 = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        Spanned::new(Expr::Bool(true), Default::default()),
        HashMap::new(),
        None,
        None,
    );
    let spv2 = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        Spanned::new(Expr::Bool(false), Default::default()),
        HashMap::new(),
        None,
        None,
    );

    assert_ne!(spv1.cmp(&spv2), std::cmp::Ordering::Equal);
    assert_ne!(spv1, spv2);
}

/// Ensure that SetPredValues with different bound names are distinguishable.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_different_bound_names_different_spans_consistent() {
    let bound1 = BoundVar {
        name: Spanned::new("x".to_string(), Span::new(FileId(0), 0, 1)),
        domain: None,
        pattern: None,
    };
    let bound2 = BoundVar {
        name: Spanned::new("y".to_string(), Span::new(FileId(0), 100, 101)),
        domain: None,
        pattern: None,
    };
    let pred = Spanned::new(Expr::Bool(true), Default::default());

    let spv1 = SetPredValue::new(
        Value::StringSet,
        bound1,
        pred.clone(),
        HashMap::new(),
        None,
        None,
    );
    let spv2 = SetPredValue::new(
        Value::StringSet,
        bound2,
        pred.clone(),
        HashMap::new(),
        None,
        None,
    );

    // Different bound names → must be different in ALL three traits.
    let ord_result = spv1.cmp(&spv2);
    let eq_result = spv1 == spv2;

    assert_ne!(ord_result, std::cmp::Ordering::Equal);
    assert!(!eq_result);

    // Consistency check: Ord and PartialEq agree.
    assert_eq!(
        eq_result,
        ord_result == std::cmp::Ordering::Equal,
        "PartialEq and Ord must agree"
    );
}

/// Verify that the Eq/Ord/Hash consistency holds for Value::SetPred wrapper too.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_setpred_wrapper_trait_consistency() {
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };

    let pred1 = Spanned::new(Expr::Bool(true), Span::new(FileId(0), 10, 20));
    let pred2 = Spanned::new(Expr::Bool(true), Span::new(FileId(0), 50, 60));

    let v1 = Value::SetPred(Box::new(SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        pred1,
        HashMap::new(),
        None,
        None,
    )));
    let v2 = Value::SetPred(Box::new(SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        pred2,
        HashMap::new(),
        None,
        None,
    )));

    // All three traits must agree on the Value wrapper level too.
    let ord_eq = v1.cmp(&v2) == std::cmp::Ordering::Equal;
    let partial_eq = v1 == v2;
    let hash_eq = compute_hash(&v1) == compute_hash(&v2);

    assert!(
        ord_eq,
        "Value::SetPred Ord should treat same-node-different-span as equal"
    );
    assert!(
        partial_eq,
        "Value::SetPred PartialEq must match Ord (#2030)"
    );
    assert!(
        hash_eq,
        "Value::SetPred Hash must match PartialEq for equal values"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_identity_visitor_contract_order() {
    struct RecordingVisitor {
        events: Vec<String>,
    }

    impl SetPredIdentityVisitor for RecordingVisitor {
        fn visit_source(&mut self, source: &Value) {
            self.events.push(format!("source={source:?}"));
        }

        fn visit_bound_sig(&mut self, bound_sig: u64) {
            self.events.push(format!("bound={bound_sig}"));
        }

        fn visit_pred_sig(&mut self, pred_sig: u64) {
            self.events.push(format!("pred={pred_sig}"));
        }

        fn visit_env_len(&mut self, len: usize) {
            self.events.push(format!("env_len={len}"));
        }

        fn visit_env_entry(&mut self, name: &str, value: &Value) {
            self.events.push(format!("env[{name}]={value:?}"));
        }

        fn visit_captured_state(&mut self, captured_state: Option<&[Value]>) {
            self.events.push(format!(
                "captured_state={:?}",
                captured_state.map(<[Value]>::len)
            ));
        }

        fn visit_captured_next_state(&mut self, captured_next_state: Option<&[Value]>) {
            self.events.push(format!(
                "captured_next_state={:?}",
                captured_next_state.map(<[Value]>::len)
            ));
        }
    }

    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let pred = Spanned::new(Expr::Bool(true), Default::default());
    let mut env = HashMap::new();
    env.insert("z".into(), Value::int(3));
    env.insert("a".into(), Value::int(1));

    let spv = SetPredValue::new(
        Value::StringSet,
        bound,
        pred,
        env,
        Some(std::sync::Arc::from([Value::int(10), Value::int(20)])),
        Some(std::sync::Arc::from([Value::int(30)])),
    );

    let mut visitor = RecordingVisitor { events: Vec::new() };
    spv.visit_identity_fields(&mut visitor);

    assert_eq!(visitor.events.len(), 8);
    assert!(visitor.events[0].starts_with("source="));
    assert!(visitor.events[1].starts_with("bound="));
    assert!(visitor.events[2].starts_with("pred="));
    assert_eq!(visitor.events[3], "env_len=2");
    assert_eq!(visitor.events[4], "env[a]=1");
    assert_eq!(visitor.events[5], "env[z]=3");
    assert_eq!(visitor.events[6], "captured_state=Some(2)");
    assert_eq!(visitor.events[7], "captured_next_state=Some(1)");
}

/// Mock CapturedChain for testing OnceLock lazy materialization in isolation.
/// Simulates what BindingChain::materialize_locals does: inserts local bindings
/// into the env HashMap.
struct MockCapturedChain {
    locals: Vec<(Arc<str>, Value)>,
}

impl CapturedChain for MockCapturedChain {
    fn clone_box(&self) -> Box<dyn CapturedChain> {
        Box::new(MockCapturedChain {
            locals: self.locals.clone(),
        })
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn materialize_locals(&self, env: &mut HashMap<Arc<str>, Value>) {
        for (name, value) in &self.locals {
            env.insert(Arc::clone(name), value.clone());
        }
    }
}

/// Build paired eager/lazy SetPredValues from the same logical inputs.
/// Returns (eager, lazy) for identity comparison testing.
fn build_eager_lazy_pair(
    module_env: HashMap<Arc<str>, Value>,
    locals: Vec<(Arc<str>, Value)>,
    captured_state: Option<Arc<[Value]>>,
    captured_next_state: Option<Arc<[Value]>>,
) -> (SetPredValue, SetPredValue) {
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let pred = Spanned::new(Expr::Bool(true), Default::default());
    let module_env_arc = Arc::new(module_env);

    let mut eager_env = (*module_env_arc).clone();
    for (name, value) in &locals {
        eager_env.insert(Arc::clone(name), value.clone());
    }
    let eager = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        pred.clone(),
        eager_env,
        captured_state.clone(),
        captured_next_state.clone(),
    );

    let chain = MockCapturedChain { locals };
    let lazy = SetPredValue::new_with_captures(
        Value::StringSet,
        bound,
        pred,
        SetPredCaptures::new(
            Arc::clone(&module_env_arc),
            captured_state,
            captured_next_state,
        )
        .with_captured_chain(Box::new(chain), 2),
    );
    (eager, lazy)
}

/// Assert Eq, Ord, and Hash all agree between two SetPredValues.
fn assert_identity_equivalent(a: &SetPredValue, b: &SetPredValue) {
    assert_eq!(a, b, "SetPredValues must be PartialEq-equal");
    assert_eq!(
        a.cmp(b),
        std::cmp::Ordering::Equal,
        "SetPredValues must be Ord-equal"
    );
    assert_eq!(
        compute_hash(a),
        compute_hash(b),
        "SetPredValues must have identical hashes"
    );
}

/// Part of #2990: Verify that lazy (OnceLock) and eager SetPredValue construction
/// produce identical identity_fields, ensuring Eq/Ord/Hash consistency.
///
/// The lazy capture-bundle path defers env materialization via OnceLock::get_or_init.
/// The eager path (new) stores the already-captured env Arc directly.
/// Both must produce the same canonical identity for the state graph to be correct.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_lazy_vs_eager_identity_fields_equivalence() {
    let mut module_env = HashMap::new();
    module_env.insert(Arc::<str>::from("N"), Value::int(5));
    module_env.insert(
        Arc::<str>::from("S"),
        Value::set([Value::int(1), Value::int(2)]),
    );
    let locals = vec![
        (Arc::<str>::from("i"), Value::int(42)),
        (Arc::<str>::from("acc"), Value::string("hello")),
    ];
    let captured_state = Some(Arc::from([Value::int(10), Value::int(20)]));
    let captured_next_state = Some(Arc::from([Value::int(30)]));

    let (eager, lazy) =
        build_eager_lazy_pair(module_env, locals, captured_state, captured_next_state);
    assert_identity_equivalent(&eager, &lazy);

    // Verify env contents match exactly.
    let eager_env = eager.env();
    let lazy_env = lazy.env();
    assert_eq!(
        eager_env.len(),
        lazy_env.len(),
        "env entry count must match"
    );
    for (key, eager_val) in eager_env {
        assert_eq!(
            eager_val,
            lazy_env.get(key).expect("lazy env missing key"),
            "env[{key}] mismatch"
        );
    }
}

/// Part of #2990: Verify that lazy path with empty chain produces the same
/// identity as eager path with just the module env (no local overrides).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_lazy_vs_eager_empty_chain_equivalence() {
    let mut module_env = HashMap::new();
    module_env.insert(Arc::<str>::from("N"), Value::int(5));
    let (eager, lazy) = build_eager_lazy_pair(module_env, vec![], None, None);
    assert_identity_equivalent(&eager, &lazy);
}

/// Part of #2990: Verify that local bindings in the chain shadow module-level
/// env entries, matching BindingChain::write_locals_to_env semantics.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_lazy_chain_locals_shadow_module_env() {
    let mut module_env = HashMap::new();
    module_env.insert(Arc::<str>::from("N"), Value::int(5));
    module_env.insert(Arc::<str>::from("M"), Value::int(10));
    let locals = vec![(Arc::from("N"), Value::int(99))];
    let (eager, lazy) = build_eager_lazy_pair(module_env, locals, None, None);
    assert_identity_equivalent(&eager, &lazy);

    // Verify the shadowed value directly.
    let env = lazy.env();
    assert_eq!(
        env.get("N").unwrap(),
        &Value::int(99),
        "N must be shadowed to 99"
    );
    assert_eq!(
        env.get("M").unwrap(),
        &Value::int(10),
        "M must be unchanged"
    );
}
