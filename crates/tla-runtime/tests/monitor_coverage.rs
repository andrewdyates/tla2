// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for MonitoredStateMachine paths that had zero coverage:
//! - MonitorStats accumulation
//! - MonitorConfig::check_invariants = false
//! - apply() with out-of-range action_index (ActionNotEnabled)
//! - reset()
//!
//! Filed as Part of #1597 — coverage gaps in tla-runtime discovered during
//! Prover code-quality audit.

use tla_runtime::{MonitorConfig, MonitoredStateMachine, SpecViolation, StateMachine};

// --- Test helpers ---

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
            vec![]
        }
    }

    fn check_invariant(&self, state: &Self::State) -> Option<bool> {
        Some(state.count <= self.max)
    }
}

// Machine that always violates invariant after first step
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct BadState {
    val: i64,
}

struct AlwaysViolates;

impl StateMachine for AlwaysViolates {
    type State = BadState;

    fn init(&self) -> Vec<Self::State> {
        vec![BadState { val: 0 }]
    }

    fn next(&self, state: &Self::State) -> Vec<Self::State> {
        vec![BadState { val: state.val + 1 }]
    }

    fn check_invariant(&self, state: &Self::State) -> Option<bool> {
        Some(state.val < 1) // Violated at val=1
    }
}

// --- MonitorStats accumulation ---

#[test]
fn test_stats_transitions_counted() {
    let mut m = MonitoredStateMachine::new(Counter { max: 5 }).unwrap();
    assert_eq!(m.stats().transitions, 0);

    m.step().unwrap(); // 0 -> 1
    assert_eq!(m.stats().transitions, 1);

    m.step().unwrap(); // 1 -> 2
    assert_eq!(m.stats().transitions, 2);

    m.step().unwrap(); // 2 -> 3
    assert_eq!(m.stats().transitions, 3);
}

#[test]
fn test_stats_deadlocks_counted() {
    let mut m = MonitoredStateMachine::new(Counter { max: 1 }).unwrap();
    m.step().unwrap(); // 0 -> 1
    assert_eq!(m.stats().deadlocks, 0);

    let result = m.step(); // 1 -> deadlock
    assert!(matches!(result, Err(SpecViolation::Deadlock { .. })));
    assert_eq!(m.stats().deadlocks, 1);
}

#[test]
fn test_stats_violations_counted() {
    let mut m = MonitoredStateMachine::new(AlwaysViolates).unwrap();
    assert_eq!(m.stats().violations, 0);

    let result = m.step(); // 0 -> 1 (violates invariant)
    assert!(matches!(
        result,
        Err(SpecViolation::InvariantViolated { .. })
    ));
    assert_eq!(m.stats().violations, 1);
}

#[test]
fn test_stats_deadlock_at_max_zero() {
    let mut m = MonitoredStateMachine::new(Counter { max: 0 }).unwrap();
    // At state count=0, there's exactly 0 next states (max=0, count is not < max)
    // Actually Counter deadlocks at max, but max=0 means init is already at max
    // So apply(0) should return ActionNotEnabled or Deadlock
    let result = m.apply(0);
    // With Counter{max:0}, init is count=0, next returns empty (0 < 0 is false)
    // So for_each_next yields nothing -> deadlock
    assert!(matches!(result, Err(SpecViolation::Deadlock { .. })));
    assert_eq!(m.stats().deadlocks, 1);
}

// --- ActionNotEnabled path ---

#[test]
fn test_apply_action_not_enabled() {
    // Counter{max:5} at state 0 has exactly 1 successor (index 0).
    // Requesting action_index=1 should return ActionNotEnabled.
    let mut m = MonitoredStateMachine::new(Counter { max: 5 }).unwrap();
    let result = m.apply(1);
    assert!(matches!(
        result,
        Err(SpecViolation::ActionNotEnabled { action_index: 1 })
    ));
    assert_eq!(m.stats().disabled_actions, 1);
    // State should not have changed
    assert_eq!(m.state().count, 0);
}

#[test]
fn test_apply_action_not_enabled_large_index() {
    let mut m = MonitoredStateMachine::new(Counter { max: 5 }).unwrap();
    let result = m.apply(999);
    assert!(matches!(
        result,
        Err(SpecViolation::ActionNotEnabled { action_index: 999 })
    ));
    assert_eq!(m.stats().disabled_actions, 1);
}

// --- MonitorConfig::check_invariants = false ---

#[test]
fn test_config_check_invariants_disabled() {
    let config = MonitorConfig {
        check_invariants: false,
        ..Default::default()
    };
    let mut m = MonitoredStateMachine::with_config(AlwaysViolates, config).unwrap();

    // With invariant checking disabled, step() should succeed even though
    // the invariant would be violated at val=1
    m.step()
        .expect("step should succeed with invariant checking disabled");
    assert_eq!(m.state().val, 1);
    assert_eq!(m.stats().violations, 0);
}

#[test]
fn test_config_check_invariants_disabled_via_apply() {
    let config = MonitorConfig {
        check_invariants: false,
        ..Default::default()
    };
    let mut m = MonitoredStateMachine::with_config(AlwaysViolates, config).unwrap();

    m.apply(0)
        .expect("apply should succeed with invariant checking disabled");
    assert_eq!(m.state().val, 1);
    assert_eq!(m.stats().violations, 0);
}

// --- reset() ---

#[test]
fn test_reset_returns_to_initial() {
    let mut m = MonitoredStateMachine::new(Counter { max: 10 }).unwrap();
    m.step().unwrap(); // 0 -> 1
    m.step().unwrap(); // 1 -> 2
    m.step().unwrap(); // 2 -> 3
    assert_eq!(m.state().count, 3);

    m.reset().unwrap();
    assert_eq!(m.state().count, 0);
}

#[test]
fn test_reset_allows_continued_stepping() {
    let mut m = MonitoredStateMachine::new(Counter { max: 2 }).unwrap();
    m.step().unwrap(); // 0 -> 1
    m.step().unwrap(); // 1 -> 2
                       // Now at deadlock state
    assert!(matches!(m.step(), Err(SpecViolation::Deadlock { .. })));

    m.reset().unwrap();
    // Should be able to step again from initial state
    m.step().expect("step after reset should succeed");
    assert_eq!(m.state().count, 1);
}

// --- apply() valid path with stats ---

#[test]
fn test_apply_valid_action_updates_stats() {
    let mut m = MonitoredStateMachine::new(Counter { max: 5 }).unwrap();
    assert_eq!(m.stats().transitions, 0);

    m.apply(0).unwrap(); // 0 -> 1
    assert_eq!(m.stats().transitions, 1);
    assert_eq!(m.state().count, 1);

    m.apply(0).unwrap(); // 1 -> 2
    assert_eq!(m.stats().transitions, 2);
    assert_eq!(m.state().count, 2);
}

// --- max_violations enforcement ---

#[test]
fn test_max_violations_allows_below_threshold() {
    let config = MonitorConfig {
        max_violations: Some(3),
        ..Default::default()
    };
    let mut m = MonitoredStateMachine::with_config(AlwaysViolates, config).unwrap();

    // First 3 violations should return InvariantViolated
    for i in 1..=3 {
        let result = m.step();
        assert!(matches!(
            result,
            Err(SpecViolation::InvariantViolated { .. })
        ));
        assert_eq!(m.stats().violations, i);
    }
}

#[test]
fn test_max_violations_exceeded_via_step() {
    let config = MonitorConfig {
        max_violations: Some(1),
        ..Default::default()
    };
    let mut m = MonitoredStateMachine::with_config(AlwaysViolates, config).unwrap();

    // First violation returns InvariantViolated (violations=1, 1 > 1 is false)
    let result = m.step();
    assert!(matches!(
        result,
        Err(SpecViolation::InvariantViolated { .. })
    ));

    // Second violation returns MaxViolationsExceeded (violations=2, 2 > 1 is true)
    let result = m.step();
    assert!(matches!(
        result,
        Err(SpecViolation::MaxViolationsExceeded {
            violations: 2,
            max: 1
        })
    ));
}

#[test]
fn test_max_violations_zero_exceeds_on_first() {
    let config = MonitorConfig {
        max_violations: Some(0),
        ..Default::default()
    };
    let mut m = MonitoredStateMachine::with_config(AlwaysViolates, config).unwrap();

    // First violation returns MaxViolationsExceeded (violations=1, 1 > 0 is true)
    let result = m.step();
    assert!(matches!(
        result,
        Err(SpecViolation::MaxViolationsExceeded {
            violations: 1,
            max: 0
        })
    ));
}

#[test]
fn test_max_violations_exceeded_via_apply() {
    let config = MonitorConfig {
        max_violations: Some(0),
        ..Default::default()
    };
    let mut m = MonitoredStateMachine::with_config(AlwaysViolates, config).unwrap();

    // apply() path should also enforce max_violations
    let result = m.apply(0);
    assert!(matches!(
        result,
        Err(SpecViolation::MaxViolationsExceeded {
            violations: 1,
            max: 0
        })
    ));
}

// --- EmptyInit ---

#[test]
fn test_new_empty_init_returns_error() {
    struct EmptyMachine;

    impl StateMachine for EmptyMachine {
        type State = CounterState;

        fn init(&self) -> Vec<Self::State> {
            vec![] // No initial states
        }

        fn next(&self, _state: &Self::State) -> Vec<Self::State> {
            vec![]
        }
    }

    let result = MonitoredStateMachine::new(EmptyMachine);
    assert!(matches!(result, Err(SpecViolation::EmptyInit)));
}

#[test]
fn test_with_config_empty_init_returns_error() {
    struct EmptyMachine;

    impl StateMachine for EmptyMachine {
        type State = CounterState;

        fn init(&self) -> Vec<Self::State> {
            vec![]
        }

        fn next(&self, _state: &Self::State) -> Vec<Self::State> {
            vec![]
        }
    }

    let config = MonitorConfig {
        check_invariants: false,
        ..Default::default()
    };
    let result = MonitoredStateMachine::with_config(EmptyMachine, config);
    assert!(matches!(result, Err(SpecViolation::EmptyInit)));
}
