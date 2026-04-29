// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(2000))]
#[test]
fn test_eval_let_recursive_function_def_uses_lazy_func() {
    // Regression test: recursive local function definitions like PermSeqs(perms) in
    // SchedulingAllocator previously stack overflowed due to eager FuncDef evaluation.
    let v = eval_str(
        r#"LET perms[ss \in SUBSET {1,2}] ==
               IF ss = {} THEN {<<>>}
               ELSE LET ps == [x \in ss |->
                                 { Append(sq, x) : sq \in perms[ss \ {x}] }]
                    IN UNION { ps[x] : x \in ss }
           IN perms[{1,2}]"#,
    )
    .unwrap();

    let set = v.as_set().expect("Expected set result");
    assert_eq!(set.len(), 2);
    assert!(set.contains(&Value::Seq(Arc::new(
        vec![Value::int(1), Value::int(2)].into()
    ))));
    assert!(set.contains(&Value::Seq(Arc::new(
        vec![Value::int(2), Value::int(1)].into()
    ))));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_recursive_max_over_subset() {
    // Issue #100, #610: Recursive Maximum function over SUBSET domain
    // This is the pattern from PaxosCommit.tla
    //
    // Run in explicit 16MB stack thread because debug-mode recursive eval
    // exceeds default stack before stacker can grow it.
    let result = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            // Single element case
            assert_eq!(
                eval_str(
                    r#"LET S == {0}
                           Max[T \in SUBSET S] ==
                               IF T = {} THEN -1
                               ELSE LET n == CHOOSE n \in T : TRUE
                                        rmax == Max[T \ {n}]
                                    IN IF n >= rmax THEN n ELSE rmax
                       IN Max[S]"#,
                )
                .unwrap(),
                Value::int(0)
            );

            // Two element case - inline recursive call
            assert_eq!(
                eval_str(
                    r#"LET S == {0, 1}
                           Max[T \in SUBSET S] ==
                               IF T = {} THEN -1
                               ELSE LET n == CHOOSE n \in T : TRUE
                                    IN IF n >= Max[T \ {n}] THEN n ELSE Max[T \ {n}]
                       IN Max[S]"#,
                )
                .unwrap(),
                Value::int(1)
            );

            // Two element case - nested LET with rmax binding
            assert_eq!(
                eval_str(
                    r#"LET S == {0, 1}
                           Max[T \in SUBSET S] ==
                               IF T = {} THEN -1
                               ELSE LET n == CHOOSE n \in T : TRUE
                                        rmax == Max[T \ {n}]
                                    IN IF n >= rmax THEN n ELSE rmax
                       IN Max[S]"#,
                )
                .unwrap(),
                Value::int(1)
            );

            // Three element case to verify deeper recursion
            assert_eq!(
                eval_str(
                    r#"LET S == {1, 2, 3}
                           Max[T \in SUBSET S] ==
                               IF T = {} THEN -1
                               ELSE LET n == CHOOSE n \in T : TRUE
                                        rmax == Max[T \ {n}]
                                    IN IF n >= rmax THEN n ELSE rmax
                       IN Max[S]"#,
                )
                .unwrap(),
                Value::int(3)
            );
        })
        .expect("Failed to spawn test thread")
        .join();

    // Propagate any panic from the test thread
    if let Err(e) = result {
        std::panic::resume_unwind(e);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_recursive_two_param_function_domain() {
    // Coverage for eval_let_func_domain() multi-bound branch (TupleSet domain).
    // This recursive function has two bounded parameters, so LET processing
    // must build a lazy recursive function over a tuple domain.
    // Note: This exercises eval_let_func_domain() (LET path), NOT
    // eval_ident_func_domain() (module-level op path), because eval_let()
    // pre-binds recursive functions in local_stack before eval_ident runs.
    let v = eval_str(
        r#"LET F[i \in {0, 1}, j \in {0, 1}] ==
               IF i = 0 /\ j = 0 THEN 0
               ELSE IF j = 0 THEN F[i - 1, 1]
               ELSE F[i, j - 1]
           IN F[1, 1]"#,
    )
    .unwrap();
    assert_eq!(v, Value::int(0));
}

/// Regression test for #1448: RECURSIVE operator with parameters.
/// Sum(f, S) calls itself recursively — parameters f and S must survive across calls.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_recursive_operator_params_preserved() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Op == LET sc == [i \in {1, 2} |-> i]
      IN Sum(sc, {1, 2})
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    // Sum(sc, {1, 2}) should yield sc[1] + sc[2] = 1 + 2 = 3
    let val = ctx.eval_op("Op").unwrap();
    assert_eq!(val, Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_fold_named_add_shadows_dyadic_builtin() {
    let v = eval_with_extended_modules(
        r#"EXTENDS DyadicRationals
           RECURSIVE SumSlow(_)
           SumSlow(S) ==
               IF S = {} THEN 0
               ELSE LET x == CHOOSE x \in S : TRUE
                    IN Add(x, SumSlow(S \ {x}))
           Add(a, b) == a + b"#,
        "SumSlow({1, 2, 3, 4})",
        &["DyadicRationals"],
    )
    .unwrap();
    assert_eq!(
        v,
        Value::int(10),
        "recursive fold helper must preserve main-module Add shadowing"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_ident_func_domain_multi_bound() {
    // Coverage for eval_ident_func_domain() multi-bound branch (TupleSet domain).
    // Unlike test_eval_recursive_two_param_function_domain above, this defines
    // the recursive function at module level (not inside LET), so eval_ident()
    // resolves it and calls eval_ident_func_domain() to build the TupleSet domain.
    let src = r#"
---- MODULE Test ----
F[i \in {0, 1}, j \in {0, 1}] ==
IF i = 0 /\ j = 0 THEN 0
ELSE IF j = 0 THEN F[i - 1, 1]
ELSE F[i, j - 1]
Op == F[1, 1]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let val = ctx.eval_op("Op").unwrap();
    assert_eq!(val, Value::int(0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_domain_of_lazy_function_preserves_finite_product_components() {
    let v = eval_str(
        r#"LET f[x \in {2, 1}, y \in Nat] == x + y
           IN DOMAIN f = ({1, 2} \X Nat)"#,
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_ident_func_domain_single_bound() {
    // Coverage for eval_ident fast-path single-bound recursive function.
    // Module-level (not LET) so eval_ident() resolves it via shared.ops fast path.
    // Exercises the same code path as the multi-bound test above but for the
    // single-bound branch in build_lazy_func_from_ctx (bounds.len() == 1).
    let src = r#"
---- MODULE Test ----
Fib[n \in 0..10] ==
IF n <= 1 THEN n
ELSE Fib[n - 1] + Fib[n - 2]
Op == Fib[6]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let val = ctx.eval_op("Op").unwrap();
    assert_eq!(val, Value::int(8)); // Fib(6) = 8
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_recursive_let_function_over_nat() {
    assert_eq!(
        eval_str(r#"LET f[n \in Nat] == IF n = 0 THEN 0 ELSE f[n-1] + 1 IN f[3]"#).unwrap(),
        Value::int(3)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_let_fast_path_does_not_reuse_sibling_function_bindings() {
    // Regression for #3395: sibling recursive lazy functions defined in the same
    // LET scope share the same captured env Arc, but they do not share the same
    // captured binding chain. Reusing G's caller context for F would let G's
    // parameter binding shadow F's captured outer `n`.
    assert_eq!(
        eval_str(
            r#"LET n == 10 IN
               LET F[i \in 0..1] == IF i = 0 THEN n ELSE F[i - 1]
                   G[n \in 0..1] == IF n = 0 THEN 0 ELSE F[0] + G[n - 1]
               IN G[1]"#,
        )
        .unwrap(),
        Value::int(10)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_transitive_closure_style_let_recursion() {
    // This evaluation is deeply recursive and can overflow the default test thread stack.
    let expr = r#"
LET S == {1, 2, 3}
R == [x, y \in S |-> (x = 1 /\ y = 2) \/ (x = 2 /\ y = 3)]
N == Cardinality(S)
trcl[n \in Nat] ==
    [x, y \in S |->
        IF n = 0
        THEN R[x, y]
        ELSE \/ trcl[n-1][x, y]
             \/ \E z \in S : trcl[n-1][x, z] /\ trcl[n-1][z, y]]
IN  /\ trcl[N][1, 3]
/\ ~trcl[N][3, 1]
/\ ~trcl[N][1, 1]
"#;

    let handle = std::thread::Builder::new()
        .name("test_eval_transitive_closure_style_let_recursion".to_string())
        .stack_size(16 * 1024 * 1024)
        .spawn(move || eval_str(expr))
        .expect("spawn test thread");

    let result = handle.join().expect("join test thread");
    assert_eq!(result.unwrap(), Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_func_operator_tuple_pattern_destructures() {
    let src = r#"
---- MODULE Test ----
sc[<<x, y>> \in {<<1, 2>>}] == x + y
Test == sc[<<1, 2>>]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let val = ctx.eval_op("Test").unwrap();
    assert_eq!(val, Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_func_operator_tuple_pattern_sc_game_of_life_shape() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
CONSTANT N
VARIABLE grid

Pos == {<<x, y>> : x, y \in 1..N}
Grid == [p \in Pos |-> TRUE]

sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
CASE \/ x = 0 \/ y = 0
     \/ x > N \/ y > N
     \/ ~grid[<<x, y>>] -> 0
[] OTHER -> 1

Test == sc[<<1, 1>>]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    // Fix #3014: Register VARIABLE so dep tracking records state reads.
    ctx.register_var("grid".to_string());

    ctx.bind_mut("N", Value::int(2));
    let grid = ctx.eval_op("Grid").unwrap();
    ctx.bind_mut("grid", grid);

    let val = ctx.eval_op("Test").unwrap();
    assert_eq!(val, Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_game_of_life_score_no_undefined_x() {
    // This evaluation is deeply recursive and can overflow the default test thread stack.
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
CONSTANT N
VARIABLE grid

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                   ELSE LET x == CHOOSE x \in S : TRUE
                        IN  f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}
Grid == [p \in Pos |-> TRUE]

sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
CASE \/ x = 0 \/ y = 0
     \/ x > N \/ y > N
     \/ ~grid[<<x, y>>] -> 0
[] OTHER -> 1

score(p) == LET nbrs == {x \in {-1, 0, 1} \X
                           {-1, 0, 1} : x /= <<0, 0>>}
            points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
        IN Sum(sc, points)

Test == score(<<1, 1>>)
====
"#;

    let handle = std::thread::Builder::new()
        .name("test_eval_game_of_life_score_no_undefined_x".to_string())
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let tree = parse_to_syntax_tree(src);
            let lower_result = lower(FileId(0), &tree);
            assert!(
                lower_result.errors.is_empty(),
                "Errors: {:?}",
                lower_result.errors
            );

            let module = lower_result.module.unwrap();
            let mut ctx = EvalCtx::new();
            ctx.load_module(&module);
            // Fix #3014: Register VARIABLE so dep tracking records state reads.
            ctx.register_var("grid".to_string());

            ctx.bind_mut("N", Value::int(2));
            let grid = ctx.eval_op("Grid").unwrap();
            ctx.bind_mut("grid", grid);

            ctx.eval_op("Test")
        })
        .expect("spawn test thread");

    let val = handle
        .join()
        .expect("join test thread")
        .expect("Test should evaluate");
    assert!(val.as_i64().is_some(), "Expected Int, got {:?}", val);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_recursive_sum_with_choose_and_let() {
    let src = r#"
---- MODULE Test ----
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                   ELSE LET x == CHOOSE x \in S : TRUE
                        IN  f[x] + Sum(f, S \ {x})

Test == LET f == [x \in {1, 2} |-> 1]
        IN Sum(f, {1, 2})
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let val = ctx.eval_op("Test").unwrap();
    assert_eq!(val, Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_preserves_local_stack_bindings() {
    // Regression test: LET expressions must preserve local_stack bindings from enclosing scopes.
    // This was a bug where LET created a new context with empty local_stack, causing
    // "Undefined variable" errors when the LET body referenced variables bound by
    // enclosing operators or quantifiers (e.g., EXISTS-bound vars, operator parameters).
    //
    // Pattern that triggered the bug (from Chameneos spec):
    //   Op(cid) == ... LET v == f[cid][1] IN [f EXCEPT ![cid] = <<v, ...>>]
    //   Next == \E c \in IDs : Op(c)
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
Op(x) == LET y == x + 1 IN y * 2
Result == Op(5)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // Op(5) should evaluate: y = 5 + 1 = 6, result = 6 * 2 = 12
    let result = ctx.eval_op("Result");
    assert!(result.is_ok(), "Should not error: {:?}", result);
    assert_eq!(result.unwrap(), Value::int(12));
}

/// Regression test for #2566: RECURSIVE operator with deep recursion should not OOM.
///
/// This mimics the DllToBst pattern: multiple RECURSIVE operators that recurse over
/// set elements, creating function values at each level. With the old bind_all() path,
/// each recursive call cloned and grew the env HashMap, causing O(k²) memory growth.
/// With bind_all_fast(), the env stays constant-size and parameters go through the
/// O(1) fast_bindings linked list.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_operator_deep_recursion_no_oom() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers

RECURSIVE ListLen(_, _)
ListLen(addrs, mem) ==
    IF addrs = {} THEN 0
    ELSE LET a == CHOOSE a \in addrs : TRUE
         IN  1 + ListLen(addrs \ {a}, mem)

RECURSIVE ListSum(_, _)
ListSum(addrs, mem) ==
    IF addrs = {} THEN 0
    ELSE LET a == CHOOSE a \in addrs : TRUE
         IN  mem[a] + ListSum(addrs \ {a}, mem)

Test == LET S == {1, 2, 3, 4, 5}
            mem == [x \in S |-> x * 10]
        IN  <<ListLen(S, mem), ListSum(S, mem)>>
====
"#;
    let handle = std::thread::Builder::new()
        .name("test_recursive_operator_deep_recursion_no_oom".to_string())
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let tree = parse_to_syntax_tree(src);
            let lower_result = lower(FileId(0), &tree);
            assert!(
                lower_result.errors.is_empty(),
                "Errors: {:?}",
                lower_result.errors
            );

            let module = lower_result.module.unwrap();
            let mut ctx = EvalCtx::new();
            ctx.load_module(&module);

            ctx.eval_op("Test")
        })
        .expect("spawn test thread");

    let val = handle
        .join()
        .expect("join test thread")
        .expect("Test should evaluate");
    // ListLen({1,2,3,4,5}, mem) = 5
    // ListSum({1,2,3,4,5}, mem) = 10+20+30+40+50 = 150
    assert_eq!(
        val,
        Value::Seq(Arc::new(vec![Value::int(5), Value::int(150)].into()))
    );
}

/// Regression test for #2566: RECURSIVE operator that creates function values inside
/// the recursive body. This verifies captured_env() includes fast_bindings, so
/// parameters are visible to closures created during RECURSIVE evaluation.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_operator_captures_params_in_func_value() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers

RECURSIVE TreeInorder(_, _)
TreeInorder(addrs, tree) ==
    IF addrs = {} THEN <<>>
    ELSE LET a == CHOOSE a \in addrs : TRUE
             rest == TreeInorder(addrs \ {a}, tree)
             \* Create a function value that references the parameter 'tree'
             vals == [x \in addrs |-> tree[x]]
         IN  Append(rest, vals[a])

Test == LET S == {1, 2, 3}
            t == [x \in S |-> x * x]
        IN  TreeInorder(S, t)
====
"#;
    let handle = std::thread::Builder::new()
        .name("test_recursive_operator_captures_params_in_func_value".to_string())
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let tree = parse_to_syntax_tree(src);
            let lower_result = lower(FileId(0), &tree);
            assert!(
                lower_result.errors.is_empty(),
                "Errors: {:?}",
                lower_result.errors
            );

            let module = lower_result.module.unwrap();
            let mut ctx = EvalCtx::new();
            ctx.load_module(&module);

            ctx.eval_op("Test")
        })
        .expect("spawn test thread");

    let val = handle
        .join()
        .expect("join test thread")
        .expect("Test should evaluate without undefined variable error");
    // Should produce a sequence with 3 elements (squares of chosen elements)
    if let Value::Seq(elems) = &val {
        assert_eq!(elems.len(), 3, "Expected 3-element sequence, got {:?}", val);
    } else {
        panic!("Expected sequence, got {:?}", val);
    }
}
