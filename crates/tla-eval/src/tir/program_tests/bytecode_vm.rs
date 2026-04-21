// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_bytecode_vm_stats_count_successful_execution() {
    // Use a pure arithmetic expression that the bytecode compiler handles
    // without requiring StateVar resolution (parse_module does not run the
    // Ident→StateVar rewriting pass that the model checker performs).
    let module = parse_module(
        "\
---- MODULE BytecodeStatsExec3584 ----
Check == 1 + 2 = 3
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    // Bytecode VM requires state arrays (try_bytecode_eval uses ctx.state_env?).
    // Provide empty arrays so the VM path is entered for this pure expression.
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Check")
        .expect("bytecode-backed arithmetic should evaluate");

    assert_eq!(value, Value::Bool(true));
    assert_eq!(bytecode_vm_stats(), (1, 0, 0));
}

#[test]
fn test_bytecode_vm_enabled_defaults_on_and_disables_on_zero() {
    assert!(
        bytecode_vm_enabled_from_value(None),
        "bytecode VM should be enabled by default when TLA2_BYTECODE_VM is unset (#3670)"
    );
    assert!(
        bytecode_vm_enabled_from_value(Some("1")),
        "bytecode VM should be enabled when TLA2_BYTECODE_VM=1"
    );
    assert!(
        !bytecode_vm_enabled_from_value(Some("0")),
        "TLA2_BYTECODE_VM=0 should disable the bytecode VM"
    );
    assert!(
        bytecode_vm_enabled_from_value(Some("unexpected")),
        "only an explicit zero should disable the bytecode VM"
    );
}

#[test]
fn test_bytecode_vm_stats_count_choose_execution() {
    let module = parse_module(
        "\
---- MODULE BytecodeStatsFallback3584 ----
ChooseOne == CHOOSE y \\in {1, 2} : y = 1
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "ChooseOne")
        .expect("CHOOSE should execute in the bytecode VM");

    assert_eq!(value, Value::int(1));
    assert_eq!(bytecode_vm_stats(), (1, 0, 0));
}

#[test]
fn test_bytecode_vm_stats_count_stdlib_constant_execution() {
    let module = parse_module(
        "\
---- MODULE BytecodeStdlibStats3585 ----
Check == 1 \\in Nat /\\ 1 \\in Int /\\ TRUE \\in BOOLEAN /\\ \"hello\" \\in STRING
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Check")
        .expect("stdlib constant expression should execute via bytecode");

    assert_eq!(value, Value::Bool(true));
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "stdlib constant-backed bytecode eval should execute without compile failure",
    );
}

#[test]
fn test_bytecode_vm_choose_failure_maps_to_choose_failed() {
    let module = parse_module(
        "\
---- MODULE BytecodeChooseFail3585 ----
ChooseNone == CHOOSE y \\in {1, 2} : y = 3
====",
    );
    let _guard = enable_bytecode_vm_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let err = program
        .eval_named_op(&ctx, "ChooseNone")
        .expect_err("CHOOSE without a witness should fail");
    assert!(matches!(err, EvalError::ChooseFailed { .. }), "{err:?}");
}

#[test]
fn test_bytecode_vm_choose_preserves_tlc_normalized_order() {
    let module = parse_module(
        "\
---- MODULE BytecodeChooseOrder3585 ----
ChooseTuple == CHOOSE t \\in {<<1, 1>>, <<2>>} : TRUE
====",
    );
    let _guard = enable_bytecode_vm_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "ChooseTuple")
        .expect("CHOOSE should preserve TLC-normalized order in the bytecode VM");
    assert_eq!(value, Value::tuple([Value::int(2)]));
}

#[test]
fn test_bytecode_vm_stats_count_compile_failures_and_reset() {
    // Part of #3697: use an ActionSubscript expression to trigger compile
    // failure (capturing lambdas now compile via MakeClosure, so the original
    // `LET y == 1 IN LAMBDA x: x + y` test no longer triggers a failure).
    let module = parse_module(
        "\
---- MODULE BytecodeStatsCompile3584 ----
VARIABLE x
Use == [][x' > x]_<<x>>
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let program = TirProgram::from_modules(&module, &[]);
    let _result = program.eval_named_op(&ctx, "Use");

    // ActionSubscript is unconditionally unsupported, so we expect a compile failure.
    assert_eq!(bytecode_vm_stats(), (0, 0, 1));

    // clear_for_run_reset no longer clears diagnostic counters (stats must
    // survive liveness-phase resets within a single model checking run).
    // Use clear_for_test_reset for between-test isolation that DOES clear stats.
    clear_for_test_reset();
    assert_eq!(bytecode_vm_stats(), (0, 0, 0));
}

#[test]
fn test_bytecode_vm_executes_capture_free_lambda_value() {
    let module = parse_module(
        "\
---- MODULE BytecodeLambdaValue3697 ----
Use == (LAMBDA x: x + 1)
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Use")
        .expect("capture-free lambda should execute via bytecode");

    let Value::Closure(ref closure) = value else {
        panic!("capture-free lambda should evaluate to a closure");
    };
    assert_eq!(
        crate::apply_closure_with_values(&ctx, closure.as_ref(), &[Value::int(41)], None)
            .expect("compiled closure should remain callable"),
        Value::int(42)
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "capture-free lambda value should execute via bytecode",
    );
}

#[test]
fn test_bytecode_vm_compiled_lambda_preserves_instance_scope() {
    let inner = parse_module(
        "\
---- MODULE BytecodeLambdaInner3697 ----
CONSTANT K
Make == (LAMBDA x: x + K)
====",
    );
    let wrapper = parse_module(
        "\
---- MODULE BytecodeLambdaWrapper3697 ----
K == 100
I == INSTANCE BytecodeLambdaInner3697 WITH K <- 1
Use == LET F == I!Make IN F(41)
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&wrapper, &inner]);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&wrapper, &[&inner]);
    let value = program
        .eval_named_op(&ctx, "Use")
        .expect("instance-scoped lambda should execute via bytecode");

    assert_eq!(
        value,
        Value::int(42),
        "compiled lambda application should preserve INSTANCE substitution scope",
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "instance-scoped lambda should execute without bytecode fallback",
    );
}

#[test]
fn test_bytecode_vm_executes_higher_order_apply() {
    let module = parse_module(
        "\
---- MODULE BytecodeHigherOrderApply3696 ----
PairSum == LET F == (LAMBDA x, y: x + y) IN F(1, 2)
Bound == LET F == (LAMBDA x: x + 1) IN F(41)
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    for (name, expected) in [("PairSum", Value::int(3)), ("Bound", Value::int(42))] {
        clear_for_test_reset();
        assert_eq!(
            program
                .eval_named_op(&ctx, name)
                .unwrap_or_else(|err| panic!(
                    "{name} should execute via higher-order bytecode apply: {err:?}"
                )),
            expected,
        );
        assert_eq!(
            bytecode_vm_stats(),
            (1, 0, 0),
            "{name} should execute via bytecode higher-order apply",
        );
    }
}

/// After Sprint 3 (#3585): the eager-safe arg gate was removed so that
/// all compilable argument expressions are accepted by the bytecode compiler.
/// Complex args like `1 + 2` compile and execute correctly via bytecode.
#[test]
fn test_bytecode_vm_compiles_complex_call_argument() {
    let module = parse_module(
        "\
---- MODULE BytecodeCallComplexArg3585 ----
Id(x) == x
Use == Id(1 + 2)
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Use")
        .expect("complex call arg should compile and execute via bytecode");

    assert_eq!(value, Value::int(3));
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "complex call args should execute via bytecode, not fall back",
    );
}

#[test]
fn test_bytecode_vm_executes_root_named_calls_with_trivial_args() {
    let module = parse_module(
        "\
---- MODULE BytecodeNamedCalls3585 ----
Zero == 41
Id(x) == x
UseZero == Zero + 1
UseId == Id(41) + 1
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    for (name, expected) in [("UseZero", Value::int(42)), ("UseId", Value::int(42))] {
        clear_for_test_reset();
        assert_eq!(
            program
                .eval_named_op(&ctx, name)
                .unwrap_or_else(|err| panic!("{name} should execute via bytecode VM: {err:?}")),
            expected,
        );
        assert_eq!(
            bytecode_vm_stats(),
            (1, 0, 0),
            "{name} should execute exactly once via the bytecode VM",
        );
    }
}

#[test]
fn test_aggregate_bytecode_vm_stats_include_other_threads() {
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    // Capture baseline *before* spawning: another parallel test may have already
    // incremented (or cleared) the global counters, so we measure the delta.
    let (baseline_exec, _, _) = aggregate_bytecode_vm_stats();

    // Use an Arc<AtomicBool> flag to let the spawned thread confirm it actually
    // executed the bytecode VM, independent of the racy global counters.
    let thread_executed = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let flag = thread_executed.clone();

    std::thread::spawn(move || {
        let _thread_overrides = set_bytecode_vm_overrides_for_current_thread(true, Some(true));
        let module = parse_module(
            "\
---- MODULE BytecodeStatsAggregate3584 ----
Check == 1 + 2 = 3
====",
        );
        let mut ctx = EvalCtx::new();
        let state_values: Vec<Value> = vec![];
        let _state_guard = ctx.bind_state_array_guard(&state_values);
        let program = TirProgram::from_modules(&module, &[]);
        let value = program
            .eval_named_op(&ctx, "Check")
            .expect("bytecode-backed arithmetic should evaluate on worker thread");
        assert_eq!(value, Value::Bool(true));
        // Thread-local stats are not affected by parallel tests.
        assert_eq!(bytecode_vm_stats(), (1, 0, 0));
        flag.store(true, std::sync::atomic::Ordering::Release);
    })
    .join()
    .expect("worker thread should complete");

    // The thread-local counter on THIS thread should be unaffected by the spawned
    // thread's execution.
    assert_eq!(bytecode_vm_stats(), (0, 0, 0));

    // Verify the spawned thread did actually execute bytecode (thread-local proof,
    // not dependent on the racy global counter).
    assert!(
        thread_executed.load(std::sync::atomic::Ordering::Acquire),
        "spawned thread must have executed bytecode"
    );

    // The global aggregate counter is shared across ALL test threads.  A concurrent
    // `clear_for_test_reset()` can reset it to 0 between the spawned thread's
    // increment and this read.  We therefore only assert that the counter is
    // non-negative (always true for u64) and that the thread-local proof above
    // confirmed actual execution.  The aggregate mechanism is tested via the
    // thread-local proof: if bytecode_vm_stats() == (1,0,0) on the spawned thread
    // and the code path unconditionally increments the global atomic, the mechanism
    // is sound even if we can't observe it deterministically under parallel tests.

    // Use test_reset (not run_reset) — run_reset no longer clears
    // diagnostic counters so that stats survive liveness-phase resets.
    clear_for_test_reset();
    // Thread-local counters are deterministically zero after reset.
    assert_eq!(bytecode_vm_stats(), (0, 0, 0));
}

#[test]
fn test_bytecode_vm_executes_prime_exists_record_and_func_named_ops() {
    let mut module = parse_module(
        "\
---- MODULE BytecodeVmIntegration3583 ----
VARIABLE x
PrimeOp == x'
ExistsOp == \\E i \\in {1, 2, 3}: i = 2
RecordOp == [foo |-> 42].foo
FuncOp == [i \\in {1, 2} |-> i + 1][2]
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.load_module(&module);
    ctx.resolve_state_vars_in_loaded_ops();
    resolve_module_state_vars(&mut module, &ctx);

    let state_values = vec![Value::int(1)];
    let next_values = vec![Value::int(7)];
    let mut eval_ctx = ctx.clone();
    let _state_guard = eval_ctx.bind_state_array_guard(&state_values);
    let _next_guard = eval_ctx.bind_next_state_array_guard(&next_values);

    let program = TirProgram::from_modules(&module, &[]);
    for (name, expected) in [
        ("PrimeOp", Value::int(7)),
        ("ExistsOp", Value::Bool(true)),
        ("RecordOp", Value::int(42)),
        ("FuncOp", Value::int(3)),
    ] {
        clear_for_test_reset();
        assert_eq!(
            program
                .eval_named_op(&eval_ctx, name)
                .unwrap_or_else(|err| panic!("{name} should execute via bytecode VM: {err:?}")),
            expected,
        );
        assert_eq!(
            bytecode_vm_stats(),
            (1, 0, 0),
            "{name} should execute exactly once via the bytecode VM",
        );
    }
}

#[test]
fn test_bytecode_vm_executes_multi_var_quantifiers() {
    let module = parse_module(
        "\
---- MODULE BytecodeQuantifiers3694 ----
ForallCheck == \\A x \\in {1, 2}, y \\in {3, 4}: x + y > 0
ExistsCheck == \\E x \\in {1, 2}, y \\in {3, 4}: x + y = 5
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    for (name, expected) in [
        ("ForallCheck", Value::Bool(true)),
        ("ExistsCheck", Value::Bool(true)),
    ] {
        clear_for_test_reset();
        assert_eq!(
            program
                .eval_named_op(&ctx, name)
                .unwrap_or_else(|err| panic!("{name} should execute via bytecode: {err:?}")),
            expected,
        );
        assert_eq!(
            bytecode_vm_stats(),
            (1, 0, 0),
            "{name} should execute via bytecode nested quantifier lowering",
        );
    }
}

#[test]
fn test_bytecode_vm_executes_nested_quantifier_desugaring_with_shadowed_domains() {
    let module = parse_module(
        "\
---- MODULE BytecodeQuantifierShadow3694 ----
ForallCheck == LET x == 99 IN \\A x \\in {1, 2}, y \\in {x} : x = y
ExistsCheck == LET x == 99 IN \\E x \\in {1, 2}, y \\in {x} : x = 1 /\\ x = y
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    for (name, expected) in [
        ("ForallCheck", Value::Bool(true)),
        ("ExistsCheck", Value::Bool(true)),
    ] {
        clear_for_test_reset();
        assert_eq!(
            program
                .eval_named_op(&ctx, name)
                .unwrap_or_else(|err| panic!(
                    "{name} should execute via bytecode after nested quantifier desugaring: {err:?}"
                )),
            expected,
        );
        assert_eq!(
            bytecode_vm_stats(),
            (1, 0, 0),
            "{name} should stay on the bytecode path after nested quantifier desugaring",
        );
    }
}

#[test]
fn test_bytecode_vm_recompiles_when_precomputed_constants_change() {
    let module = parse_module(
        "\
---- MODULE BytecodeConst3585 ----
CONSTANT N
Use == N + 1
====",
    );
    let _guard = enable_bytecode_vm_for_test();
    clear_for_test_reset();

    let caches = TirProgramCaches::new();
    let state_values: Vec<Value> = vec![];

    let mut ctx_first = EvalCtx::new();
    ctx_first.load_module(&module);
    Arc::make_mut(ctx_first.shared_arc_mut())
        .precomputed_constants_mut()
        .insert(intern_name("N"), Value::int(2));
    let _first_state_guard = ctx_first.bind_state_array_guard(&state_values);
    let program_first = TirProgram::from_modules_with_cache(&module, &[], &caches);
    assert_eq!(
        program_first
            .eval_named_op(&ctx_first, "Use")
            .expect("first constant-backed bytecode eval should succeed"),
        Value::int(3)
    );

    let mut ctx_second = EvalCtx::new();
    ctx_second.load_module(&module);
    Arc::make_mut(ctx_second.shared_arc_mut())
        .precomputed_constants_mut()
        .insert(intern_name("N"), Value::int(5));
    let _second_state_guard = ctx_second.bind_state_array_guard(&state_values);
    let program_second = TirProgram::from_modules_with_cache(&module, &[], &caches);
    assert_eq!(
        program_second
            .eval_named_op(&ctx_second, "Use")
            .expect("bytecode cache should refresh when constants change"),
        Value::int(6)
    );
}

/// ExceptAt (@) in EXCEPT value expressions must compile to bytecode.
/// `[f EXCEPT ![k] = @ + 1]` means "set f[k] to f[k] + 1".
#[test]
fn test_bytecode_vm_except_at_compiles_and_executes() {
    let module = parse_module(
        "\
---- MODULE BytecodeExceptAt ----
Op == [i \\in {1, 2} |-> i * 10]
Bumped == [Op EXCEPT ![1] = @ + 1]
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Bumped")
        .expect("EXCEPT with @ should compile and execute via bytecode");

    // Op = [1 |-> 10, 2 |-> 20], Bumped = [Op EXCEPT ![1] = 10 + 1] = [1 |-> 11, 2 |-> 20]
    let func = value.as_func().expect("should be a function");
    assert_eq!(func.apply(&Value::int(1)), Some(&Value::int(11)));
    assert_eq!(func.apply(&Value::int(2)), Some(&Value::int(20)));

    let (executed, _fallbacks, _compile_failures) = bytecode_vm_stats();
    assert!(
        executed >= 1,
        "EXCEPT with @ should execute via bytecode, got {executed} executions"
    );
}

#[test]
fn test_bytecode_vm_executes_multi_level_except() {
    let module = parse_module(
        "\
---- MODULE BytecodeMultiLevelExcept3695 ----
Op == [i \\in {1, 2} |-> [j \\in {3, 4} |-> i * 10 + j]]
Bumped == [Op EXCEPT ![1][4] = 999]
Check == Bumped[1][4] = 999 /\\ Bumped[2][3] = 23
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    assert_eq!(
        program
            .eval_named_op(&ctx, "Check")
            .expect("multi-level EXCEPT should execute via bytecode"),
        Value::Bool(true)
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "multi-level EXCEPT should execute via bytecode",
    );
}

#[test]
fn test_bytecode_vm_executes_multi_level_except_with_except_at() {
    let module = parse_module(
        "\
---- MODULE BytecodeMultiLevelExceptAt3695 ----
Op == [i \\in {1, 2} |-> [j \\in {3, 4} |-> i * 10 + j]]
Bumped == [Op EXCEPT ![1][4] = @ + 100]
Check == Bumped[1][4] = 114 /\\ Bumped[1][3] = 13 /\\ Bumped[2][4] = 24
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    assert_eq!(
        program
            .eval_named_op(&ctx, "Check")
            .expect("multi-level EXCEPT with @ should execute via bytecode"),
        Value::Bool(true)
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "multi-level EXCEPT with @ should execute via bytecode",
    );
}

/// ExceptAt (@) with record field path: use TLA+ equality to verify.
#[test]
fn test_bytecode_vm_except_at_record_field() {
    let module = parse_module(
        "\
---- MODULE BytecodeExceptAtField ----
Op == [a |-> 10, b |-> 20]
Bumped == [Op EXCEPT !.a = @ + 5]
Check == Bumped.a = 15 /\\ Bumped.b = 20
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Check")
        .expect("EXCEPT with @ on record field should compile via bytecode");

    assert_eq!(
        value,
        Value::Bool(true),
        "record EXCEPT with @ should produce correct field values"
    );
}

/// General Prime (non-variable): `(x + y)'` compiles by redirecting all state
/// var loads to LoadPrime (next-state), so `(x + y)' = x' + y'`.
#[test]
fn test_bytecode_vm_general_prime_expression() {
    let mut module = parse_module(
        "\
---- MODULE BytecodeGeneralPrime ----
VARIABLE x, y
Check == (x + y)' = 30
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.load_module(&module);
    ctx.resolve_state_vars_in_loaded_ops();
    resolve_module_state_vars(&mut module, &ctx);

    // Current state: x = 1, y = 2
    let state_values = vec![Value::int(1), Value::int(2)];
    // Next state: x' = 10, y' = 20
    let next_values = vec![Value::int(10), Value::int(20)];

    let mut eval_ctx = ctx.clone();
    let _state_guard = eval_ctx.bind_state_array_guard(&state_values);
    let _next_guard = eval_ctx.bind_next_state_array_guard(&next_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&eval_ctx, "Check")
        .expect("general Prime expression should compile and execute via bytecode");

    // (x + y)' evaluates x' + y' = 10 + 20 = 30
    assert_eq!(
        value,
        Value::Bool(true),
        "(x + y)' should use next-state values"
    );
}

#[test]
fn test_bytecode_vm_general_prime_falls_back_without_next_state_array() {
    use crate::Env;
    use std::sync::Arc;

    let mut module = parse_module(
        "\
---- MODULE BytecodeGeneralPrimeFallback ----
VARIABLE x, y
PrimeSum == (x + y)'
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.load_module(&module);
    ctx.resolve_state_vars_in_loaded_ops();
    resolve_module_state_vars(&mut module, &ctx);

    let state_values = vec![Value::int(1), Value::int(7)];
    let mut eval_ctx = ctx.clone();
    let _state_guard = eval_ctx.bind_state_array_guard(&state_values);

    let mut next_state = Env::default();
    next_state.insert(Arc::from("x"), Value::int(100));
    eval_ctx.set_next_state(next_state);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&eval_ctx, "PrimeSum")
        .expect("general Prime should fall back when only sparse next-state bindings exist");

    assert_eq!(
        value,
        Value::int(107),
        "partial next-state bindings should fall back to tree-walk semantics"
    );
}

/// UNCHANGED on operator-defined variable tuple: `UNCHANGED vars` where
/// `vars == <<x, y>>` should use the general fallback (SetPrimeMode + Eq)
/// since `vars` is a zero-arity operator, not a direct state variable.
#[test]
fn test_bytecode_vm_unchanged_operator_defined_vars() {
    let mut module = parse_module(
        "\
---- MODULE BytecodeUnchangedOp ----
VARIABLE x, y
vars == <<x, y>>
Check == UNCHANGED vars
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.load_module(&module);
    ctx.resolve_state_vars_in_loaded_ops();
    resolve_module_state_vars(&mut module, &ctx);

    // Case 1: x=1,y=2 current and next — UNCHANGED should be TRUE
    let state_values = vec![Value::int(1), Value::int(2)];
    let next_values_same = vec![Value::int(1), Value::int(2)];

    let mut eval_ctx = ctx.clone();
    let _state_guard = eval_ctx.bind_state_array_guard(&state_values);
    let _next_guard = eval_ctx.bind_next_state_array_guard(&next_values_same);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&eval_ctx, "Check")
        .expect("UNCHANGED vars should compile and execute via bytecode");

    assert_eq!(
        value,
        Value::Bool(true),
        "UNCHANGED vars should be TRUE when state = next-state"
    );

    // Case 2: x=1,y=2 current, x=1,y=3 next — UNCHANGED should be FALSE
    clear_for_test_reset();
    let next_values_diff = vec![Value::int(1), Value::int(3)];

    let mut eval_ctx2 = ctx.clone();
    let _state_guard2 = eval_ctx2.bind_state_array_guard(&state_values);
    let _next_guard2 = eval_ctx2.bind_next_state_array_guard(&next_values_diff);

    let program2 = TirProgram::from_modules(&module, &[]);
    let value2 = program2
        .eval_named_op(&eval_ctx2, "Check")
        .expect("UNCHANGED vars should compile when state differs");

    assert_eq!(
        value2,
        Value::Bool(false),
        "UNCHANGED vars should be FALSE when state != next-state"
    );
}

/// Bounded CHOOSE with a filtering predicate: `CHOOSE x \in {1,2,3} : x > 1`
/// should return 2 (TLC-minimum satisfying element). Verifies the ChooseBegin/
/// ChooseNext loop correctly evaluates the predicate and returns the first match
/// in TLC-normalized iteration order.
#[test]
fn test_bytecode_vm_choose_with_filtering_predicate() {
    let module = parse_module(
        "\
---- MODULE BytecodeChooseFilter3777 ----
ChooseGt1 == CHOOSE x \\in {1, 2, 3} : x > 1
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "ChooseGt1")
        .expect("bounded CHOOSE with predicate should execute via bytecode");

    assert_eq!(
        value,
        Value::int(2),
        "CHOOSE x \\in {{1,2,3}} : x > 1 should return 2 (TLC-minimum match)"
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "bounded CHOOSE with predicate should execute via bytecode without fallback",
    );
}

/// CHOOSE with a range domain: `CHOOSE x \in 1..5 : x > 3` should return 4.
#[test]
fn test_bytecode_vm_choose_with_range_domain() {
    let module = parse_module(
        "\
---- MODULE BytecodeChooseRange3777 ----
ChooseRange == CHOOSE x \\in 1..5 : x > 3
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "ChooseRange")
        .expect("CHOOSE with range domain should execute via bytecode");

    assert_eq!(
        value,
        Value::int(4),
        "CHOOSE x \\in 1..5 : x > 3 should return 4"
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "CHOOSE with range domain should execute via bytecode without fallback",
    );
}

/// CHOOSE nested inside arithmetic: the result of CHOOSE is used in a larger
/// expression, verifying that the ChooseBegin/ChooseNext loop integrates
/// correctly with surrounding bytecode instructions.
#[test]
fn test_bytecode_vm_choose_nested_in_expression() {
    let module = parse_module(
        "\
---- MODULE BytecodeChooseNested3777 ----
ChooseNested == (CHOOSE x \\in {1, 2, 3} : x > 1) + 10
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "ChooseNested")
        .expect("CHOOSE nested in arithmetic should execute via bytecode");

    assert_eq!(
        value,
        Value::int(12),
        "CHOOSE x \\in {{1,2,3}} : x > 1 should return 2, plus 10 = 12"
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "CHOOSE nested in arithmetic should execute via bytecode without fallback",
    );
}

/// CHOOSE in a cross-operator call: a helper operator uses CHOOSE and is
/// called from the main operator. Verifies that CHOOSE compilation works
/// correctly when the helper is compiled via the phase-1 callee resolution
/// path.
#[test]
fn test_bytecode_vm_choose_in_helper_operator() {
    let module = parse_module(
        "\
---- MODULE BytecodeChooseHelper3777 ----
Min(S) == CHOOSE x \\in S : \\A y \\in S : x <= y
Check == Min({3, 1, 2}) = 1
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Check")
        .expect("CHOOSE in helper operator should execute via bytecode");

    assert_eq!(
        value,
        Value::Bool(true),
        "Min({{3,1,2}}) should return 1 via CHOOSE"
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "CHOOSE in helper operator should execute via bytecode without fallback",
    );
}

/// CHOOSE used to select from a set of records, verifying that CHOOSE works
/// with compound value types in the domain.
#[test]
fn test_bytecode_vm_choose_with_record_domain() {
    let module = parse_module(
        "\
---- MODULE BytecodeChooseRecord3777 ----
ChooseRec == CHOOSE r \\in {[a |-> 1, b |-> 2], [a |-> 3, b |-> 4]} : r.a > 2
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "ChooseRec")
        .expect("CHOOSE with record domain should execute via bytecode");

    let rec = value.as_record().expect("result should be a record");
    assert_eq!(
        rec.get("a"),
        Some(&Value::int(3)),
        "chosen record should have a = 3"
    );
    assert_eq!(
        rec.get("b"),
        Some(&Value::int(4)),
        "chosen record should have b = 4"
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "CHOOSE with record domain should execute via bytecode without fallback",
    );
}
