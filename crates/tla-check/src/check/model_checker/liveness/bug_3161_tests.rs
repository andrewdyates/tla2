// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::config::Config;
use crate::liveness::LiveExpr;
use crate::state::{ArrayState, State};
use crate::test_support::parse_module_with_id as parse_module;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::{Expr, ModuleTarget};
use tla_core::{FileId, Spanned};

fn is_named_module_ref(expr: &Arc<Spanned<Expr>>, instance: &str, op_name: &str) -> bool {
    matches!(
        &expr.node,
        Expr::ModuleRef(ModuleTarget::Named(name), actual_op, args)
            if name == instance && actual_op == op_name && args.is_empty()
    )
}

fn build_sched_allocator_checker() -> ModelChecker<'static> {
    let scheduler = parse_module(
        r#"
---- MODULE SchedulerTemporal ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Schedule ==
    /\ x < 2
    /\ x' = x + 1

Stutter == x' = x

Next == Schedule \/ Stutter

vars == x

Liveness == WF_vars(Schedule)

Allocator == Init /\ [][Next]_vars /\ Liveness

====
"#,
        FileId(2),
    );

    let concrete = parse_module(
        r#"
---- MODULE ConcreteSchedulerTemporal ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Sched == INSTANCE SchedulerTemporal

Next == Sched!Next

SchedAllocator == Sched!Allocator

====
"#,
        FileId(3),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["SchedAllocator".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let scheduler = Box::leak(Box::new(scheduler));
    let concrete = Box::leak(Box::new(concrete));
    let config = Box::leak(Box::new(config));
    let mut checker = ModelChecker::new_with_extends(concrete, &[scheduler], config);
    checker.set_store_states(true);
    checker.prepare_inline_liveness_cache();
    checker
}

#[allow(clippy::struct_field_names)]
struct SchedAllocatorTags {
    enabled_tag: u32,
    action_tag: u32,
    state_changed_tag: u32,
}

fn record_sched_allocator_property_results(
    checker: &mut ModelChecker<'static>,
) -> (State, State, State) {
    let registry = checker.ctx.var_registry().clone();
    let zero = State::from_pairs([("x", Value::int(0))]);
    let one = State::from_pairs([("x", Value::int(1))]);
    let two = State::from_pairs([("x", Value::int(2))]);

    let transitions = [
        (
            zero.fingerprint(),
            ArrayState::from_state(&zero, &registry),
            vec![(ArrayState::from_state(&one, &registry), one.fingerprint())],
            "0 -> 1 transition should record property inline results",
        ),
        (
            one.fingerprint(),
            ArrayState::from_state(&one, &registry),
            vec![(ArrayState::from_state(&two, &registry), two.fingerprint())],
            "1 -> 2 transition should record property inline results",
        ),
        (
            two.fingerprint(),
            ArrayState::from_state(&two, &registry),
            vec![(ArrayState::from_state(&two, &registry), two.fingerprint())],
            "2 -> 2 stuttering transition should record property inline results",
        ),
    ];

    for (current_fp, current_arr, successors, message) in transitions {
        checker
            .record_inline_liveness_results(current_fp, &current_arr, &successors, &[])
            .expect(message);
    }

    (zero, one, two)
}

fn sched_allocator_plan<'a>(checker: &'a ModelChecker<'static>) -> &'a InlineLivenessPropertyPlan {
    checker
        .inline_property_plan("SchedAllocator")
        .expect("SchedAllocator should produce an inline property plan")
}

fn find_sched_allocator_tags(plan: &InlineLivenessPropertyPlan) -> SchedAllocatorTags {
    let enabled_tag = plan
        .state_leaves
        .iter()
        .find_map(|leaf| match leaf {
            LiveExpr::Enabled {
                action,
                require_state_change: true,
                ..
            } if is_named_module_ref(action, "Sched", "Schedule") => leaf.tag(),
            _ => None,
        })
        .expect("property plan should contain ENABLED(Sched!Schedule)");
    let action_tag = plan
        .action_leaves
        .iter()
        .find_map(|leaf| match leaf {
            LiveExpr::ActionPred { expr, .. } if is_named_module_ref(expr, "Sched", "Schedule") => {
                leaf.tag()
            }
            _ => None,
        })
        .expect("property plan should contain ActionPred(Sched!Schedule)");
    let state_changed_tag = plan
        .action_leaves
        .iter()
        .find_map(|leaf| match leaf {
            LiveExpr::StateChanged {
                subscript: Some(_), ..
            } => leaf.tag(),
            _ => None,
        })
        .expect("property plan should contain subscripted state-change leaf");

    SchedAllocatorTags {
        enabled_tag,
        action_tag,
        state_changed_tag,
    }
}

#[allow(clippy::too_many_arguments)]
fn assert_sched_allocator_results(
    plan: &InlineLivenessPropertyPlan,
    current: &State,
    next: &State,
    tags: &SchedAllocatorTags,
    enabled: bool,
    action: bool,
    state_changed: bool,
    label: &str,
) {
    let state_bits = plan
        .state_bitmasks
        .get(&current.fingerprint())
        .unwrap_or_else(|| panic!("state bitmask missing for {label}"));
    assert_eq!(
        state_bits & (1u64 << tags.enabled_tag) != 0,
        enabled,
        "WF_vars(Sched!Schedule) enabled result mismatch for {label}",
    );
    let action_bits = plan
        .action_bitmasks
        .get(&(current.fingerprint(), next.fingerprint()))
        .unwrap_or_else(|| panic!("action bitmask missing for {label}"));
    assert_eq!(
        action_bits & (1u64 << tags.action_tag) != 0,
        action,
        "Sched!Schedule action result mismatch for {label}",
    );
    assert_eq!(
        action_bits & (1u64 << tags.state_changed_tag) != 0,
        state_changed,
        "fairness subscript result mismatch for {label}",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_3161_property_plan_records_instance_fairness_leaf_results() {
    let mut checker = build_sched_allocator_checker();
    let (zero, one, two) = record_sched_allocator_property_results(&mut checker);
    let plan = sched_allocator_plan(&checker);
    let tags = find_sched_allocator_tags(plan);

    assert_sched_allocator_results(plan, &zero, &one, &tags, true, true, true, "0 -> 1");
    assert_sched_allocator_results(plan, &two, &two, &tags, false, false, false, "2 -> 2");
}
