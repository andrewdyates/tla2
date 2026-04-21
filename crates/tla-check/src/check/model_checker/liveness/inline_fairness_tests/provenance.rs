// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Part of #3100: Tests for actual-arg hint provenance matching.

use super::*;
use crate::test_support::parse_module_with_id;
use tla_core::FileId;

const DISJUNCTIVE_NEXT_SPEC: &str = r#"
---- MODULE DisjunctiveNext ----
EXTENDS Integers
VARIABLE x
Init == x = 0
A == x' = 1
B == x' = 2
Next == A \/ B
Prop == []<>(x = 0)
====
"#;

/// Design test §1: Disjunctive Next still multi-matches.
/// WF_x(Next) with split_action_meta having two "Next" entries with empty
/// bindings must record the same ActionPred tag in both provenance slots.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn disjunctive_next_provenance_multi_matches() {
    let module = parse_module(DISJUNCTIVE_NEXT_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);

    // Set split_action_meta to two "Next" entries with empty bindings
    // (simulating disjunctive Next == A \/ B split into two actions)
    checker.compiled.split_action_meta = Some(vec![
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("Next".to_string()),
            bindings: vec![],
            expr: None,
        },
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("Next".to_string()),
            bindings: vec![],
            expr: None,
        },
    ]);

    checker.set_fairness(vec![FairnessConstraint::Weak {
        vars: "x".to_string(),
        action: "Next".to_string(),
        action_node: None,
    }]);

    checker.prepare_inline_fairness_cache();

    // Both split action entries should have the same provenance tag
    assert_eq!(
        checker.liveness_cache.action_provenance_tags.len(),
        2,
        "should have provenance slots for both split actions"
    );
    assert!(
        !checker.liveness_cache.action_provenance_tags[0].is_empty(),
        "first Next split action should have provenance tags"
    );
    assert!(
        !checker.liveness_cache.action_provenance_tags[1].is_empty(),
        "second Next split action should have provenance tags"
    );
    assert_eq!(
        checker.liveness_cache.action_provenance_tags[0],
        checker.liveness_cache.action_provenance_tags[1],
        "both Next split actions should match the same WF ActionPred tag"
    );
}

const OP_FAIRNESS_SPEC: &str = r#"
---- MODULE OpFairness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Op(a) == x' = a
Next == Op(1) \/ Op(2)
\* Fairness as a TemporalRef operator for prepare_inline_fairness_cache path
MyWF == WF_x(Op(1))
Prop == []<>(x = 0)
====
"#;

/// Design test §2: Specialized operator applications match only correct actual args.
/// WF_x(Op(1)) should produce provenance only on Op(1) split actions, not Op(2).
/// Uses TemporalRef fairness to route through the temporal_convert path where
/// extract_action_hint captures const-level actual-arg bindings.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn specialized_op_provenance_matches_correct_actual_args() {
    let module = parse_module(OP_FAIRNESS_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);

    // Set split_action_meta for Op(1) and Op(2) with their actual-arg bindings
    checker.compiled.split_action_meta = Some(vec![
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("Op".to_string()),
            bindings: vec![(Arc::from("a"), Value::int(1))],
            expr: None,
        },
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("Op".to_string()),
            bindings: vec![(Arc::from("a"), Value::int(2))],
            expr: None,
        },
    ]);

    // Use TemporalRef fairness to route through temporal_convert path
    // where extract_action_hint captures the const-level actual-arg bindings.
    checker.set_fairness(vec![FairnessConstraint::TemporalRef {
        op_name: "MyWF".to_string(),
    }]);

    checker.prepare_inline_fairness_cache();

    assert_eq!(
        checker.liveness_cache.action_provenance_tags.len(),
        2,
        "should have provenance slots for both Op(1) and Op(2)"
    );

    // Op(1) entry should have the WF's ActionPred tag
    assert!(
        !checker.liveness_cache.action_provenance_tags[0].is_empty(),
        "Op(1) split action should match WF_x(Op(1)) provenance"
    );

    // Op(2) entry should NOT have the WF's ActionPred tag
    assert!(
        checker.liveness_cache.action_provenance_tags[1].is_empty(),
        "Op(2) split action must NOT match WF_x(Op(1)) — actual args differ"
    );
}

const WRAPPED_INSTANCE_FAIRNESS_SPEC: &str = r#"
---- MODULE WrappedInstanceFairness ----
EXTENDS Integers
VARIABLES x, y
Init == /\ x = 0 /\ y = 0
I == INSTANCE InstAction
Schedule == /\ I!Step /\ y' = y
Stutter == /\ x' = x /\ y' = y
Next == Schedule \/ Stutter
Prop == []<>(x = 0)
====
"#;

// Part of #3100: Tests for instance-qualified fairness provenance

const INSTANCE_ACTION_MODULE: &str = r#"
---- MODULE InstAction ----
VARIABLE x
Step == x' = 1 - x
====
"#;

/// Regression canary for #3161's root-wrapper path.
/// Weak fairness over a wrapper action that still contains `ModuleRef`
/// should preserve name-based provenance, but it must stay off the runtime
/// split-action fast path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn weak_wrapper_action_with_module_ref_stays_out_of_fast_path() {
    let inst_module = parse_module_with_id(INSTANCE_ACTION_MODULE, FileId(1));
    let module = parse_module_with_id(WRAPPED_INSTANCE_FAIRNESS_SPEC, FileId(0));
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&module, &[&inst_module], &config);
    checker.set_store_states(true);
    checker.compiled.split_action_meta = Some(vec![
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("Schedule".to_string()),
            bindings: vec![],
            expr: None,
        },
    ]);
    checker.set_fairness(vec![FairnessConstraint::Weak {
        vars: "<<x, y>>".to_string(),
        action: "Schedule".to_string(),
        action_node: None,
    }]);

    checker.prepare_inline_fairness_cache();

    assert_eq!(
        checker.liveness_cache.action_provenance_tags.len(),
        1,
        "wrapper action should still produce one provenance slot",
    );
    assert!(
        !checker.liveness_cache.action_provenance_tags[0].is_empty(),
        "wrapper action should keep name-based provenance for diagnostics",
    );
    assert_eq!(
        checker
            .liveness_cache
            .action_fast_path_provenance_tags
            .len(),
        1,
        "runtime fast-path slots should mirror split_action metadata",
    );
    assert!(
        checker.liveness_cache.action_fast_path_provenance_tags[0].is_empty(),
        "ModuleRef-containing wrapper actions must stay off the runtime fast path",
    );
    assert!(
        checker.liveness_cache.enabled_provenance.is_empty(),
        "ENABLED provenance must not infer wrapper-action enablement from split-action tags",
    );
}

const NAMED_INSTANCE_FAIRNESS_SPEC: &str = r#"
---- MODULE NamedInstanceFairness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
I == INSTANCE InstAction
Next == I!Step
MyWF == WF_x(I!Step)
Prop == []<>(x = 0)
====
"#;

/// Design test: Named instance target provenance canary.
/// WF_x(I!Step) where I == INSTANCE InstAction should produce a provenance
/// hit on split action entries named "I!Step".
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn named_instance_provenance_matches_module_ref() {
    let inst_module = parse_module_with_id(INSTANCE_ACTION_MODULE, FileId(1));
    let module = parse_module_with_id(NAMED_INSTANCE_FAIRNESS_SPEC, FileId(0));
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&module, &[&inst_module], &config);
    checker.set_store_states(true);

    // Manually seed split_action_meta with one I!Step entry
    checker.compiled.split_action_meta = Some(vec![
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("I!Step".to_string()),
            bindings: vec![],
            expr: None,
        },
    ]);

    checker.set_fairness(vec![FairnessConstraint::TemporalRef {
        op_name: "MyWF".to_string(),
    }]);

    checker.prepare_inline_fairness_cache();

    assert_eq!(
        checker.liveness_cache.action_provenance_tags.len(),
        1,
        "should have provenance slot for I!Step"
    );
    assert!(
        !checker.liveness_cache.action_provenance_tags[0].is_empty(),
        "I!Step split action should match WF_x(I!Step) provenance — named instance"
    );
    assert_eq!(
        checker
            .liveness_cache
            .action_fast_path_provenance_tags
            .len(),
        1,
        "runtime fast-path slots should mirror split-action metadata"
    );
    assert!(
        checker.liveness_cache.action_fast_path_provenance_tags[0].is_empty(),
        "INSTANCE-qualified provenance stays evaluator-backed until the split-action fast path is proven sound"
    );
}

const PARAM_INSTANCE_MODULE: &str = r#"
---- MODULE ParamInst ----
CONSTANT c
VARIABLE x
Step == x' = c
====
"#;

const PARAM_INSTANCE_FAIRNESS_SPEC: &str = r#"
---- MODULE ParamInstanceFairness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
I(n) == INSTANCE ParamInst WITH c <- n
Next == I(1)!Step \/ I(2)!Step
MyWF == WF_x(I(1)!Step)
Prop == []<>(x = 0)
====
"#;

/// Design test: Parameterized target identity canary.
/// WF_x(I(1)!Step) should produce provenance only on the I!Step split action
/// with binding n=1, not n=2.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn parameterized_instance_provenance_discriminates_target_actuals() {
    let inst_module = parse_module_with_id(PARAM_INSTANCE_MODULE, FileId(1));
    let module = parse_module_with_id(PARAM_INSTANCE_FAIRNESS_SPEC, FileId(0));
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&module, &[&inst_module], &config);
    checker.set_store_states(true);

    // Seed split_action_meta with two I!Step entries differing on target formal "n"
    checker.compiled.split_action_meta = Some(vec![
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("I!Step".to_string()),
            bindings: vec![(Arc::from("n"), Value::int(1))],
            expr: None,
        },
        crate::check::model_checker::mc_struct::ActionInstanceMeta {
            name: Some("I!Step".to_string()),
            bindings: vec![(Arc::from("n"), Value::int(2))],
            expr: None,
        },
    ]);

    checker.set_fairness(vec![FairnessConstraint::TemporalRef {
        op_name: "MyWF".to_string(),
    }]);

    checker.prepare_inline_fairness_cache();

    assert_eq!(
        checker.liveness_cache.action_provenance_tags.len(),
        2,
        "should have provenance slots for both I(1)!Step and I(2)!Step"
    );

    // I(1)!Step entry should match WF_x(I(1)!Step)
    assert!(
        !checker.liveness_cache.action_provenance_tags[0].is_empty(),
        "I(1)!Step should match WF_x(I(1)!Step) — matching target actuals"
    );
    assert_eq!(
        checker
            .liveness_cache
            .action_fast_path_provenance_tags
            .len(),
        2,
        "runtime fast-path slots should mirror split-action metadata"
    );
    assert!(
        checker.liveness_cache.action_fast_path_provenance_tags[0].is_empty(),
        "INSTANCE-qualified provenance should not pre-populate runtime action results yet"
    );

    // I(2)!Step entry should NOT match
    assert!(
        checker.liveness_cache.action_provenance_tags[1].is_empty(),
        "I(2)!Step must NOT match WF_x(I(1)!Step) — different target actuals"
    );
    assert!(
        checker.liveness_cache.action_fast_path_provenance_tags[1].is_empty(),
        "non-matching INSTANCE target actuals must also stay out of the runtime fast path"
    );
}
