// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Andrew Yates

use std::ops::ControlFlow;
use std::sync::atomic::{AtomicUsize, Ordering};

use tla_runtime::StateMachine;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_for_each_init_short_circuits() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct S(i64);

    struct M {
        init_calls: AtomicUsize,
    }

    impl StateMachine for M {
        type State = S;

        fn init(&self) -> Vec<Self::State> {
            self.init_calls.fetch_add(1, Ordering::Relaxed);
            vec![S(0), S(1), S(2)]
        }

        fn next(&self, _state: &Self::State) -> Vec<Self::State> {
            vec![]
        }
    }

    let m = M {
        init_calls: AtomicUsize::new(0),
    };

    let mut init_state_calls = 0usize;
    let result = m.for_each_init(|_s| {
        init_state_calls += 1;
        ControlFlow::Break(())
    });

    assert!(matches!(result, ControlFlow::Break(())));
    assert_eq!(init_state_calls, 1);
    assert_eq!(m.init_calls.load(Ordering::Relaxed), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_for_each_init_visits_all_initials_on_continue() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct S(i64);

    struct M;

    impl StateMachine for M {
        type State = S;

        fn init(&self) -> Vec<Self::State> {
            vec![S(0), S(1), S(2)]
        }

        fn next(&self, _state: &Self::State) -> Vec<Self::State> {
            vec![]
        }
    }

    let m = M;

    let mut initials = Vec::new();
    let result = m.for_each_init(|s| {
        initials.push(s.0);
        ControlFlow::Continue(())
    });

    assert!(matches!(result, ControlFlow::Continue(())));
    assert_eq!(initials, vec![0, 1, 2]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_for_each_init_empty_initials() {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct S;

    struct M;

    impl StateMachine for M {
        type State = S;

        fn init(&self) -> Vec<Self::State> {
            vec![]
        }

        fn next(&self, _state: &Self::State) -> Vec<Self::State> {
            vec![]
        }
    }

    let m = M;

    let mut called = false;
    let result = m.for_each_init(|_s| {
        called = true;
        ControlFlow::Continue(())
    });

    assert!(matches!(result, ControlFlow::Continue(())));
    assert!(!called);
}
