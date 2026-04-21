// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Andrew Yates

use std::ops::ControlFlow;
use std::sync::atomic::{AtomicUsize, Ordering};

use tla_runtime::StateMachine;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_for_each_next_short_circuits() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct S(i64);

    struct M {
        next_calls: AtomicUsize,
    }

    impl StateMachine for M {
        type State = S;

        fn init(&self) -> Vec<Self::State> {
            vec![S(0)]
        }

        fn next(&self, state: &Self::State) -> Vec<Self::State> {
            self.next_calls.fetch_add(1, Ordering::Relaxed);
            vec![S(state.0 + 1), S(state.0 + 2)]
        }
    }

    let m = M {
        next_calls: AtomicUsize::new(0),
    };

    let mut succ_calls = 0usize;
    let result = m.for_each_next(&S(0), |_s| {
        succ_calls += 1;
        ControlFlow::Break(())
    });

    assert!(matches!(result, ControlFlow::Break(())));
    assert_eq!(succ_calls, 1);
    assert_eq!(m.next_calls.load(Ordering::Relaxed), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_for_each_next_visits_all_successors_on_continue() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct S(i64);

    struct M;

    impl StateMachine for M {
        type State = S;

        fn init(&self) -> Vec<Self::State> {
            vec![S(0)]
        }

        fn next(&self, state: &Self::State) -> Vec<Self::State> {
            vec![S(state.0 + 1), S(state.0 + 2), S(state.0 + 3)]
        }
    }

    let m = M;

    let mut succs = Vec::new();
    let result = m.for_each_next(&S(0), |s| {
        succs.push(s.0);
        ControlFlow::Continue(())
    });

    assert!(matches!(result, ControlFlow::Continue(())));
    assert_eq!(succs, vec![1, 2, 3]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_for_each_next_empty_successors() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct S;

    struct M;

    impl StateMachine for M {
        type State = S;

        fn init(&self) -> Vec<Self::State> {
            vec![S]
        }

        fn next(&self, _state: &Self::State) -> Vec<Self::State> {
            vec![]
        }
    }

    let m = M;

    let mut called = false;
    let result = m.for_each_next(&S, |_s| {
        called = true;
        ControlFlow::Continue(())
    });

    assert!(matches!(result, ControlFlow::Continue(())));
    assert!(!called);
}
