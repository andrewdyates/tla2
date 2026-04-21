// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

//! TLA+ Runtime Library
//!
//! This crate provides runtime support for Rust code generated from TLA+ specifications.
//! It includes:
//! - The `StateMachine` trait that generated specs implement
//! - Runtime types that mirror TLA+ values (sets, sequences, functions)
//! - A BFS model checker for verifying generated code
//! - Runtime monitoring for invariant checking in production
//!
//! # Example
//!
//! ```rust
//! // Generated code from a TLA+ spec
//! use tla_runtime::prelude::*;
//!
//! #[derive(Clone, Debug, PartialEq, Eq, Hash)]
//! struct CounterState {
//!     count: i64,
//! }
//!
//! struct Counter;
//!
//! impl StateMachine for Counter {
//!     type State = CounterState;
//!
//!     fn init(&self) -> Vec<Self::State> {
//!         vec![CounterState { count: 0 }]
//!     }
//!
//!     fn next(&self, state: &Self::State) -> Vec<Self::State> {
//!         vec![CounterState { count: state.count + 1 }]
//!     }
//! }
//! ```

mod model_check;
mod monitor;
mod state_machine;
pub mod temporal;
mod types;

pub use model_check::{collect_states, model_check, model_check_with_invariant};
pub use model_check::{InvariantViolation, ModelCheckResult};
pub use monitor::{MonitorConfig, MonitorStats, MonitoredStateMachine, SpecViolation};
pub use state_machine::StateMachine;
pub use temporal::{TemporalCheckResult, TemporalProp};
pub use types::{
    boolean_set, cartesian_product, func_merge, is_finite_set, k_subsets, permutations, powerset,
    random_element, range_set, seq_set, TlaFunc, TlaRecord, TlaSet, Value,
};

/// Create a TlaSet from a list of elements
#[macro_export]
macro_rules! tla_set {
    () => { $crate::TlaSet::new() };
    ($($elem:expr),+ $(,)?) => {
        [$($elem),+].into_iter().collect::<$crate::TlaSet<_>>()
    };
}

/// Create a TlaRecord from field-value pairs
#[macro_export]
macro_rules! tla_record {
    () => { $crate::TlaRecord::new() };
    ($($field:ident => $value:expr),+ $(,)?) => {
        $crate::TlaRecord::from_fields([$(
            (stringify!($field), $value)
        ),+])
    };
}

/// Stack overflow protection for generated recursive operators.
///
/// Wraps `stacker::maybe_grow` with canonical constants (1MB red zone, 16MB
/// growth) matching the evaluator. Generated recursive TLA+ operators call
/// this to grow the stack on demand instead of overflowing.
#[inline(always)]
pub fn recursive_stack_guard<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(1024 * 1024, 16 * 1024 * 1024, f)
}

/// Prelude module - import everything commonly needed
pub mod prelude {
    pub use super::{
        boolean_set, cartesian_product, collect_states, func_merge, is_finite_set, k_subsets,
        model_check, model_check_with_invariant, permutations, powerset, random_element,
        range_set, recursive_stack_guard, seq_set, ModelCheckResult, StateMachine,
        TemporalCheckResult, TemporalProp, TlaFunc, TlaRecord, TlaSet, Value,
    };
    pub use crate::{tla_record, tla_set};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_set_basic() {
        let s = tla_set![1, 2, 3];
        assert_eq!(s.len(), 3);
        assert!(s.contains(&2));
        assert!(!s.contains(&4));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_set_union() {
        let a = tla_set![1, 2];
        let b = tla_set![2, 3];
        let c = a.union(&b);
        assert_eq!(c.len(), 3);
        assert!(c.contains(&1));
        assert!(c.contains(&2));
        assert!(c.contains(&3));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_set_intersect() {
        let a = tla_set![1, 2, 3];
        let b = tla_set![2, 3, 4];
        let c = a.intersect(&b);
        assert_eq!(c.len(), 2);
        assert!(c.contains(&2));
        assert!(c.contains(&3));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_func_basic() {
        let f: TlaFunc<i32, &str> = [(1, "a"), (2, "b")].into_iter().collect();
        assert_eq!(f.apply(&1), Some(&"a"));
        assert_eq!(f.apply(&2), Some(&"b"));
        assert_eq!(f.apply(&3), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_func_except() {
        let f: TlaFunc<i32, &str> = [(1, "a"), (2, "b")].into_iter().collect();
        let g = f.except(2, "c");
        assert_eq!(f.apply(&2), Some(&"b")); // Original unchanged
        assert_eq!(g.apply(&2), Some(&"c")); // New has update
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_range_set() {
        let r = range_set(1, 3);
        assert_eq!(r.len(), 3);
        assert!(r.contains(&1));
        assert!(r.contains(&2));
        assert!(r.contains(&3));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_range_set_empty() {
        let r = range_set(5, 3);
        assert!(r.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_powerset() {
        let s = tla_set![1, 2];
        let ps = powerset(&s);
        assert_eq!(ps.len(), 4); // 2^2 = 4

        assert!(ps.contains(&tla_set![]));
        assert!(ps.contains(&tla_set![1]));
        assert!(ps.contains(&tla_set![2]));
        assert!(ps.contains(&tla_set![1, 2]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cartesian_product() {
        let a = tla_set![1, 2];
        let b = tla_set!["x", "y"];
        let cp = cartesian_product(&a, &b);
        assert_eq!(cp.len(), 4);
        assert!(cp.contains(&(1, "x")));
        assert!(cp.contains(&(1, "y")));
        assert!(cp.contains(&(2, "x")));
        assert!(cp.contains(&(2, "y")));
    }

    // Test the StateMachine trait with a simple counter
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
                vec![] // Deadlock at max
            }
        }

        fn check_invariant(&self, state: &Self::State) -> Option<bool> {
            Some(state.count <= self.max)
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_machine_counter() {
        let machine = Counter { max: 3 };

        let init_states = machine.init();
        assert_eq!(init_states.len(), 1);
        assert_eq!(init_states[0].count, 0);

        let next_states = machine.next(&init_states[0]);
        assert_eq!(next_states.len(), 1);
        assert_eq!(next_states[0].count, 1);

        // Check invariant
        assert_eq!(
            machine.check_invariant(&CounterState { count: 2 }),
            Some(true)
        );
        assert_eq!(
            machine.check_invariant(&CounterState { count: 5 }),
            Some(false)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_monitored_state_machine_uses_streaming_next() {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        struct S(i32);

        struct StreamOnly;

        impl StateMachine for StreamOnly {
            type State = S;

            fn init(&self) -> Vec<Self::State> {
                vec![S(0)]
            }

            fn next(&self, _state: &Self::State) -> Vec<Self::State> {
                panic!("next() should not be called by MonitoredStateMachine");
            }

            fn for_each_next<F>(&self, state: &Self::State, mut f: F) -> std::ops::ControlFlow<()>
            where
                F: FnMut(Self::State) -> std::ops::ControlFlow<()>,
            {
                f(S(state.0 + 1))
            }
        }

        let mut m = MonitoredStateMachine::new(StreamOnly).unwrap();
        assert_eq!(m.state(), &S(0));
        m.step().unwrap();
        assert_eq!(m.state(), &S(1));
        m.apply(0).unwrap();
        assert_eq!(m.state(), &S(2));
        assert_eq!(m.enabled_actions(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_func_update() {
        let mut f: TlaFunc<i32, &str> = [(1, "a"), (2, "b")].into_iter().collect();
        f.update(2, "c");
        assert_eq!(f.apply(&2), Some(&"c"));
        f.update(3, "d");
        assert_eq!(f.apply(&3), Some(&"d"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_record_basic() {
        let r = TlaRecord::from_fields([("a", 1), ("b", 2)]);
        assert_eq!(r.get("a"), Some(&1));
        assert_eq!(r.get("b"), Some(&2));
        assert_eq!(r.get("c"), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_record_set() {
        let mut r = TlaRecord::from_fields([("x", 10), ("y", 20)]);
        r.set("x", 30);
        assert_eq!(r.get("x"), Some(&30));
        r.set("z", 40);
        assert_eq!(r.get("z"), Some(&40));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_record_macro() {
        let r = tla_record![x => 1, y => 2];
        assert_eq!(r.get("x"), Some(&1));
        assert_eq!(r.get("y"), Some(&2));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tla_record_fields() {
        let r = TlaRecord::from_fields([("a", 1), ("b", 2)]);
        let fields = r.fields();
        assert_eq!(fields.len(), 2);
        assert!(fields.contains(&"a".to_string()));
        assert!(fields.contains(&"b".to_string()));
    }

    // Tests for model checker helper
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_model_check_basic() {
        let machine = Counter { max: 5 };
        let result = model_check(&machine, 100);

        // Counter deadlocks at max
        assert!(result.violation.is_none());
        assert!(result.deadlock.is_some());
        assert_eq!(result.deadlock.as_ref().unwrap().count, 5);
        assert_eq!(result.distinct_states, 6); // 0, 1, 2, 3, 4, 5
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_model_check_invariant_violation() {
        // A machine that violates its invariant
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        struct BadState {
            val: i64,
        }

        struct BadMachine;
        impl StateMachine for BadMachine {
            type State = BadState;
            fn init(&self) -> Vec<Self::State> {
                vec![BadState { val: 0 }]
            }
            fn next(&self, state: &Self::State) -> Vec<Self::State> {
                vec![BadState { val: state.val + 1 }]
            }
            fn check_invariant(&self, state: &Self::State) -> Option<bool> {
                Some(state.val < 3) // Violated when val >= 3
            }
        }

        let result = model_check(&BadMachine, 100);
        assert!(result.violation.is_some());
        assert_eq!(result.violation.as_ref().unwrap().state.val, 3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_model_check_with_custom_invariant() {
        let machine = Counter { max: 10 };
        let result = model_check_with_invariant(&machine, 100, |s| s.count <= 5);

        // Custom invariant should be violated at count = 6
        assert!(result.violation.is_some());
        assert_eq!(result.violation.as_ref().unwrap().state.count, 6);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_collect_states() {
        let machine = Counter { max: 5 };
        let states = collect_states(&machine, 100);

        // Should collect all 6 states
        assert_eq!(states.len(), 6);

        // Verify states are 0 through 5
        let counts: Vec<_> = states.iter().map(|s| s.count).collect();
        for i in 0..=5 {
            assert!(counts.contains(&i), "Missing state with count={}", i);
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_collect_states_limited() {
        let machine = Counter { max: 100 };
        let states = collect_states(&machine, 10);

        // Should be limited to 10 states
        assert_eq!(states.len(), 10);

        // Verify state content: BFS from init (count=0) should yield counts 0..9
        let counts: Vec<_> = states.iter().map(|s| s.count).collect();
        for i in 0..10i64 {
            assert!(
                counts.contains(&i),
                "Missing state with count={} in limited collection",
                i
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_monitored_state_machine() {
        let machine = Counter { max: 5 };
        let mut monitored = MonitoredStateMachine::new(machine).unwrap();

        // Initial state should be 0
        assert_eq!(monitored.state().count, 0);

        // Apply valid transitions
        monitored.step().expect("step 0->1 should succeed");
        assert_eq!(monitored.state().count, 1);

        monitored.step().expect("step 1->2 should succeed");
        assert_eq!(monitored.state().count, 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_monitored_detects_deadlock() {
        let machine = Counter { max: 2 };
        let mut monitored = MonitoredStateMachine::new(machine).unwrap();

        monitored.step().expect("step 0->1 should succeed"); // 0 -> 1
        monitored.step().expect("step 1->2 should succeed"); // 1 -> 2
        assert!(matches!(
            monitored.step(),
            Err(SpecViolation::Deadlock { .. })
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_monitored_detects_invariant_violation() {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        struct BadState {
            val: i64,
        }

        struct BadMachine;
        impl StateMachine for BadMachine {
            type State = BadState;
            fn init(&self) -> Vec<Self::State> {
                vec![BadState { val: 0 }]
            }
            fn next(&self, s: &Self::State) -> Vec<Self::State> {
                vec![BadState { val: s.val + 1 }]
            }
            fn check_invariant(&self, s: &Self::State) -> Option<bool> {
                Some(s.val < 3)
            }
        }

        let mut monitored = MonitoredStateMachine::new(BadMachine).unwrap();
        monitored.step().expect("step 0->1 should succeed"); // 0 -> 1
        monitored.step().expect("step 1->2 should succeed"); // 1 -> 2
        assert!(matches!(
            monitored.step(),
            Err(SpecViolation::InvariantViolated { .. })
        )); // 2 -> 3
    }
}
