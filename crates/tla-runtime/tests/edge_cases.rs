// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_runtime::{
    model_check, range_set, tla_set, MonitoredStateMachine, SpecViolation, StateMachine, TlaSet,
};

#[test]
fn test_tla_set_empty_set_algebra() {
    let empty: TlaSet<i32> = tla_set![];
    let a = tla_set![1, 2];

    let union = a.union(&empty);
    assert_eq!(
        union, a,
        "union with empty set should preserve all elements"
    );

    let intersect = a.intersect(&empty);
    assert!(
        intersect.is_empty(),
        "intersection with empty set should be empty"
    );

    let difference = a.difference(&empty);
    assert_eq!(
        difference, a,
        "difference against empty set should preserve all elements"
    );

    // Symmetric cases: empty on the left
    let union_rev = empty.union(&a);
    assert_eq!(
        union_rev, a,
        "empty union non-empty should equal the non-empty set"
    );

    let intersect_rev = empty.intersect(&a);
    assert!(
        intersect_rev.is_empty(),
        "empty intersect non-empty should be empty"
    );

    let diff_rev = empty.difference(&a);
    assert!(
        diff_rev.is_empty(),
        "empty difference non-empty should be empty"
    );

    // Both empty
    let empty2: TlaSet<i32> = tla_set![];
    let union_both = empty.union(&empty2);
    assert!(union_both.is_empty(), "empty union empty should be empty");
    let intersect_both = empty.intersect(&empty2);
    assert!(
        intersect_both.is_empty(),
        "empty intersect empty should be empty"
    );
    let diff_both = empty.difference(&empty2);
    assert!(
        diff_both.is_empty(),
        "empty difference empty should be empty"
    );
}

#[test]
fn test_range_set_singleton() {
    let r = range_set(5, 5);
    assert_eq!(r.len(), 1);
    assert!(r.contains(&5));
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CounterState {
    count: i64,
}

struct Counter {
    max: i64,
}

impl StateMachine for Counter {
    type State = CounterState;

    fn init(&self) -> Vec<Self::State> {
        vec![CounterState { count: 0 }]
    }

    fn next(&self, state: &Self::State) -> Vec<Self::State> {
        if state.count < self.max {
            vec![CounterState {
                count: state.count + 1,
            }]
        } else {
            Vec::new()
        }
    }
}

#[test]
fn test_model_check_max_states_zero() {
    let machine = Counter { max: 5 };
    let result = model_check(&machine, 0);

    assert_eq!(
        result.states_explored, 1,
        "max_states=0 currently explores exactly one state before cut-off"
    );
    assert_eq!(
        result.distinct_states, 1,
        "only the initial state should be considered before cut-off"
    );
    assert!(result.violation.is_none());
    assert!(result.deadlock.is_none());
}

#[test]
fn test_model_check_invariant_violation_in_initial_state() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct InitState {
        val: i64,
    }

    struct InitViolationMachine;
    impl StateMachine for InitViolationMachine {
        type State = InitState;

        fn init(&self) -> Vec<Self::State> {
            vec![InitState { val: -1 }]
        }

        fn next(&self, state: &Self::State) -> Vec<Self::State> {
            vec![InitState { val: state.val + 1 }]
        }

        fn check_invariant(&self, state: &Self::State) -> Option<bool> {
            Some(state.val >= 0)
        }
    }

    let result = model_check(&InitViolationMachine, 10);
    assert_eq!(result.states_explored, 1);
    let violation = result
        .violation
        .as_ref()
        .expect("initial state should fail invariant");
    assert_eq!(violation.state.val, -1);
    assert!(result.deadlock.is_none());
}

#[test]
fn test_model_check_multiple_initial_states() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct MultiInitState(i64);

    struct MultiInitMachine;
    impl StateMachine for MultiInitMachine {
        type State = MultiInitState;

        fn init(&self) -> Vec<Self::State> {
            vec![MultiInitState(0), MultiInitState(1)]
        }

        fn next(&self, state: &Self::State) -> Vec<Self::State> {
            vec![state.clone()]
        }
    }

    let result = model_check(&MultiInitMachine, 10);
    assert!(
        result.is_ok(),
        "self-looping initial states should terminate without deadlock or invariant violation"
    );
    assert_eq!(result.distinct_states, 2);
    assert_eq!(result.states_explored, 2);
}

#[test]
fn test_monitored_state_machine_empty_init() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct EmptyState;

    struct EmptyInitMachine;
    impl StateMachine for EmptyInitMachine {
        type State = EmptyState;

        fn init(&self) -> Vec<Self::State> {
            Vec::new()
        }

        fn next(&self, _state: &Self::State) -> Vec<Self::State> {
            Vec::new()
        }
    }

    assert!(matches!(
        MonitoredStateMachine::new(EmptyInitMachine),
        Err(SpecViolation::EmptyInit)
    ));
}
