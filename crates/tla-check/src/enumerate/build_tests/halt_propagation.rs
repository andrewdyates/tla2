// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{build_successors_with_deferred, enumerate_combinations, SuccessorEmitter};
use super::*;
use crate::error::EvalError;
use crate::var_index::VarRegistry;
use std::ops::ControlFlow;

struct StopAfterNEmitter {
    stop_after: usize,
    emitted: usize,
}

impl StopAfterNEmitter {
    fn new(stop_after: usize) -> Self {
        Self {
            stop_after,
            emitted: 0,
        }
    }
}

impl SuccessorEmitter for StopAfterNEmitter {
    type Halt = ();

    fn emit(
        &mut self,
        _base: &ArrayState,
        _working: &ArrayState,
        _registry: &VarRegistry,
    ) -> Result<ControlFlow<Self::Halt, ()>, EvalError> {
        self.emitted += 1;
        if self.emitted >= self.stop_after {
            return Ok(ControlFlow::Break(()));
        }
        Ok(ControlFlow::Continue(()))
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_combinations_stop_after_n_breaks_recursion() {
    let src = r#"
---- MODULE HaltRecursion ----
VARIABLE x, y
====
"#;
    let (_module, ctx, _vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let base = ArrayState::from_values(vec![Value::int(0), Value::int(0)]);
    let mut working = base.clone();

    let assignment_map = vec![
        Some(vec![Value::int(1), Value::int(2)]),
        Some(vec![Value::int(10), Value::int(20)]),
    ];

    let mut emitter = StopAfterNEmitter::new(2);
    let flow = enumerate_combinations(
        &assignment_map,
        0,
        &base,
        &mut working,
        &registry,
        false,
        &mut emitter,
    )
    .expect("stop emitter should not produce EvalError");

    assert_eq!(flow, ControlFlow::Break(()));
    assert_eq!(emitter.emitted, 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_build_successors_with_deferred_break_stops_iteration() {
    let src = r#"
---- MODULE HaltDeferred ----
VARIABLE x, y
====
"#;
    let (_module, ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let current_array = ArrayState::from_values(vec![Value::int(0), Value::int(0)]);

    let assignments = vec![
        PrimedAssignment::InSet(Arc::from("x"), vec![Value::int(1), Value::int(2)]),
        PrimedAssignment::InSet(Arc::from("y"), vec![Value::int(10), Value::int(20)]),
    ];

    let mut emitter = StopAfterNEmitter::new(3);
    let flow = build_successors_with_deferred(
        &current_array,
        &vars,
        &assignments,
        &registry,
        &ctx,
        "halt_break_test",
        &mut emitter,
    )
    .expect("stop emitter should not produce EvalError");

    assert_eq!(flow, ControlFlow::Break(()));
    assert_eq!(emitter.emitted, 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_build_successors_with_deferred_stop_after_max_enumerates_all() {
    let src = r#"
---- MODULE HaltDeferredAll ----
VARIABLE x, y
====
"#;
    let (_module, ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let current_array = ArrayState::from_values(vec![Value::int(0), Value::int(0)]);

    let assignments = vec![
        PrimedAssignment::InSet(Arc::from("x"), vec![Value::int(1), Value::int(2)]),
        PrimedAssignment::InSet(
            Arc::from("y"),
            vec![Value::int(10), Value::int(20), Value::int(30)],
        ),
    ];

    let mut emitter = StopAfterNEmitter::new(usize::MAX);
    let flow = build_successors_with_deferred(
        &current_array,
        &vars,
        &assignments,
        &registry,
        &ctx,
        "halt_full_enum_test",
        &mut emitter,
    )
    .expect("max stop emitter should not produce EvalError");

    assert_eq!(flow, ControlFlow::Continue(()));
    assert_eq!(emitter.emitted, 6);
}
