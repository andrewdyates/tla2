// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Andrew Yates

use tla_runtime::{MonitoredStateMachine, SpecViolation, StateMachine};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_monitored_reports_violated_invariant_names() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct BadState {
        val: i64,
    }

    struct BadMachine;
    impl BadMachine {
        fn check_inv_a(&self, state: &BadState) -> bool {
            state.val < 3
        }

        fn check_inv_b(&self, state: &BadState) -> bool {
            state.val != 5
        }
    }

    impl StateMachine for BadMachine {
        type State = BadState;

        fn init(&self) -> Vec<Self::State> {
            vec![BadState { val: 0 }]
        }

        fn next(&self, state: &Self::State) -> Vec<Self::State> {
            vec![BadState { val: state.val + 1 }]
        }

        fn check_invariant(&self, state: &Self::State) -> Option<bool> {
            Some(self.check_inv_a(state) && self.check_inv_b(state))
        }

        fn invariant_names(&self) -> Vec<&'static str> {
            vec!["InvA", "InvB"]
        }

        fn check_named_invariant(&self, name: &str, state: &Self::State) -> Option<bool> {
            match name {
                "InvA" => Some(self.check_inv_a(state)),
                "InvB" => Some(self.check_inv_b(state)),
                _ => None,
            }
        }
    }

    let mut monitored = MonitoredStateMachine::new(BadMachine).unwrap();
    monitored
        .step()
        .expect("step 0->1 should succeed before invariant violation at val=3"); // 0 -> 1
    monitored
        .step()
        .expect("step 1->2 should succeed before invariant violation at val=3"); // 1 -> 2
    assert!(matches!(
        monitored.step(),
        Err(SpecViolation::InvariantViolated {
            violated_invariants,
            ..
        }) if violated_invariants == vec!["InvA".to_string()]
    )); // 2 -> 3
}
