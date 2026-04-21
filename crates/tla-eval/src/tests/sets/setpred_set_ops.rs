// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1896: SetPred on BOTH sides of intersection and difference.
/// Before #1896, `eval_intersect` and `eval_set_minus` used `Value::iter_set()` which
/// returns `None` for SetPred, causing silent fallthrough to lazy SetCap/SetDiff that
/// produce incorrect results when both operands are SetPred. The fix uses
/// `eval_iter_set()` which materializes SetPred transparently.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_both_sides_intersection_and_difference() {
    // S1 = {x ∈ SUBSET {1,2} : 1 ∈ x} = {{1}, {1,2}}
    // S2 = {x ∈ SUBSET {1,2} : 2 ∈ x} = {{2}, {1,2}}
    // S1 ∩ S2 = {{1,2}}
    // S1 \ S2 = {{1}}
    // S2 \ S1 = {{2}}
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
S1 == {x \in SUBSET {1, 2} : 1 \in x}
S2 == {x \in SUBSET {1, 2} : 2 \in x}

\* Both sides SetPred: intersection
CapBothPred == S1 \cap S2 = {{1, 2}}

\* Both sides SetPred: difference (S1 \ S2)
DiffBothPred1 == S1 \ S2 = {{1}}

\* Both sides SetPred: difference (S2 \ S1)
DiffBothPred2 == S2 \ S1 = {{2}}

\* Cardinality over intersection (tests materialization)
CapCard == Cardinality(S1 \cap S2) = 1

\* Membership in intersection result
CapMember == {1, 2} \in (S1 \cap S2)

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

    assert_eq!(
        ctx.eval_op("CapBothPred").unwrap(),
        Value::Bool(true),
        "#1896: SetPred ∩ SetPred should produce {{1,2}}"
    );
    assert_eq!(
        ctx.eval_op("DiffBothPred1").unwrap(),
        Value::Bool(true),
        "#1896: SetPred \\ SetPred should produce {{1}}"
    );
    assert_eq!(
        ctx.eval_op("DiffBothPred2").unwrap(),
        Value::Bool(true),
        "#1896: SetPred \\ SetPred (reversed) should produce {{2}}"
    );
    assert_eq!(
        ctx.eval_op("CapCard").unwrap(),
        Value::Bool(true),
        "#1896: Cardinality of SetPred ∩ SetPred should be 1"
    );
    assert_eq!(
        ctx.eval_op("CapMember").unwrap(),
        Value::Bool(true),
        "#1896: {{1,2}} should be in (SetPred ∩ SetPred)"
    );
}

/// Regression test for #1896 latent gap: SetPred LHS with concrete RHS in set
/// difference produces lazy SetDiff(SetPred, concrete). Membership checks work
/// (via set_contains_with_ctx) but Cardinality requires materialization via
/// eval_iter_set, which may fail on the lazy wrapper. This test exercises the
/// membership path to confirm at least that path is correct.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_lhs_concrete_rhs_difference_membership() {
    // S1 = {x ∈ SUBSET {1,2} : 1 ∈ x} = {{1}, {1,2}}
    // {1} ∈ S1 \ {{1,2}} should be TRUE (SetPred LHS, concrete RHS)
    // {1,2} ∈ S1 \ {{1,2}} should be FALSE
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
S1 == {x \in SUBSET {1, 2} : 1 \in x}

\* Membership in SetPred \ concrete
DiffMember1 == {1} \in (S1 \ {{1, 2}})
DiffMember2 == ~({1, 2} \in (S1 \ {{1, 2}}))

\* SetPred LHS, concrete RHS intersection membership
CapMember == {1, 2} \in (S1 \cap {{1, 2}, {3}})

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

    assert_eq!(
        ctx.eval_op("DiffMember1").unwrap(),
        Value::Bool(true),
        "#1896: {{1}} should be in (SetPred \\ concrete)"
    );
    assert_eq!(
        ctx.eval_op("DiffMember2").unwrap(),
        Value::Bool(true),
        "#1896: {{1,2}} should NOT be in (SetPred \\ concrete)"
    );
    assert_eq!(
        ctx.eval_op("CapMember").unwrap(),
        Value::Bool(true),
        "#1896: {{1,2}} should be in (SetPred ∩ concrete)"
    );
}

/// Regression test for #1483: SetCup/SetDiff/SetCap with SetPred operands.
/// SetPred membership requires eval context, but lazy set ops used to
/// collapse None (indeterminate) to false via unwrap_or(false).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_ops_with_set_pred_membership() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers

\* 2 \in ({1} \cup {n \in Nat : n > 1}) should be TRUE
CupPred == 2 \in ({1} \cup {n \in Nat : n > 1})

\* 2 should NOT be in ({1, 2, 3} \ {n \in Nat : n > 1})
DiffPred == ~(2 \in ({1, 2, 3} \ {n \in Nat : n > 1}))

\* 2 \in ({1, 2, 3} \cap {n \in Nat : n > 1}) should be TRUE
CapPred == 2 \in ({1, 2, 3} \cap {n \in Nat : n > 1})

\* Set difference materialization: {1, 2, 3} \ {n \in {1, 2, 3} : n > 1} = {1}
DiffMaterialize == ({1, 2, 3} \ {n \in {1, 2, 3} : n > 1}) = {1}

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

    assert_eq!(
        ctx.eval_op("CupPred").unwrap(),
        Value::Bool(true),
        "#1483: 2 should be in {{1}} \\cup {{n \\in Nat : n > 1}}"
    );
    assert_eq!(
        ctx.eval_op("DiffPred").unwrap(),
        Value::Bool(true),
        "#1483: 2 should NOT be in {{1,2,3}} \\ {{n \\in Nat : n > 1}}"
    );
    assert_eq!(
        ctx.eval_op("CapPred").unwrap(),
        Value::Bool(true),
        "#1483: 2 should be in {{1,2,3}} \\cap {{n \\in Nat : n > 1}}"
    );
    assert_eq!(
        ctx.eval_op("DiffMaterialize").unwrap(),
        Value::Bool(true),
        "#1483: {{1,2,3}} \\ {{n \\in {{1,2,3}} : n > 1}} should equal {{1}}"
    );
}

// === #1828 regression tests: iter_set() call sites with SetPred guards ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_over_setpred_domain() {
    // Regression test for #1828: SubsetEq where LHS is a SetPred (filtered subset).
    assert_eq!(
        eval_str(r#"{x \in SUBSET {1, 2, 3} : 2 \in x} \subseteq SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"{x \in {1, 2, 3} : x > 1} \subseteq {2, 3}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"{x \in {1, 2, 3} : x > 1} \subseteq {3}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonempty_setpred_domain() {
    // Regression test for #1828: {x \in D : P(x)} /= {} where D evaluates to SetPred.
    assert_eq!(
        eval_str(r#"{x \in {y \in SUBSET {1, 2} : 1 \in y} : 2 \in x} /= {}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"{x \in {1, 2, 3} : x > 5} /= {}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_membership_over_setpred_domain() {
    // Regression test for #1828: elem \in UNION {SetPred domain}
    assert_eq!(
        eval_str(r#"1 \in UNION {x \in SUBSET {1, 2, 3} : 1 \in x}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"4 \in UNION {x \in SUBSET {1, 2, 3} : 1 \in x}"#).unwrap(),
        Value::Bool(false)
    );
}

/// Regression test: materialize_setpred_to_vec must use captured state_env,
/// not the caller's current state. SetPredValue captures state at creation time
/// (via snapshot_state_envs in eval_set_filter); materialization must restore it.
///
/// Without the fix, the predicate evaluates against the wrong state, producing
/// incorrect results when state changes between SetPred creation and materialization.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_materialize_setpred_uses_captured_state_not_current() {
    clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
VARIABLE x
Filtered == {r \in SUBSET {1, 2} : x \in r}
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // Evaluate with x = 1: creates lazy SetPred capturing state_env where x=1
    let state1 = vec![Value::int(1)];
    ctx.bind_state_array(&state1);
    let setpred_val = ctx.eval_op("Filtered").unwrap();

    // Verify the result is lazy (SetPred), not eagerly materialized
    assert!(
        matches!(setpred_val, Value::SetPred(_)),
        "SUBSET domain should produce lazy SetPred, got: {:?}",
        setpred_val
    );

    // Change state to x = 99 (not in {1, 2} — no subset contains 99)
    let state2 = vec![Value::int(99)];
    ctx.bind_state_array(&state2);

    // Materialize the SetPred — must use captured state (x=1), not current (x=99)
    if let Value::SetPred(ref spv) = setpred_val {
        let result = materialize_setpred_to_vec(&ctx, spv).unwrap();
        // With captured state x=1: {{1}, {1,2}} — subsets of {1,2} containing 1
        // With wrong state x=99: {} — no subset of {1,2} contains 99
        assert!(
            !result.is_empty(),
            "materialize_setpred_to_vec should use captured state (x=1), \
             not current state (x=99); got empty result"
        );
        assert_eq!(
            result.len(),
            2,
            "Expected 2 subsets of {{1,2}} containing 1: {{1}} and {{1,2}}, got {:?}",
            result
        );
    } else {
        unreachable!();
    }
}

/// Part of #3979: SetPred membership where the source is a composite set containing
/// another SetPred. Before #3979, check_set_pred_membership would error with
/// "SetPred source doesn't support membership check" when set_contains returned None
/// on a composite source (SetCup, SetCap, SetDiff containing SetPred operands).
/// The fix delegates to set_contains_with_ctx for these indeterminate cases.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_membership_with_composite_source_3979() {
    // {x \in ({n \in {1,2,3} : n > 1} \cup {10}) : x < 5}
    // Source is SetCup(SetPred({1,2,3}, n > 1), {10})
    //   = {2, 3} \cup {10} = {2, 3, 10}
    // After predicate x < 5: {2, 3}
    //
    // When this SetPred is materialized and then used as a Value::SetPred in a
    // membership check, the source is a SetCup containing a SetPred, which makes
    // set_contains return None. The fix uses set_contains_with_ctx to handle this.
    let src = r#"
---- MODULE Test ----
EXTENDS Integers

\* Source is union of SetPred and concrete set
CompositeSrc == {x \in ({n \in {1, 2, 3} : n > 1} \cup {10}) : x < 5}

\* Direct membership (exercises check_set_pred_membership with composite source)
Member2 == 2 \in CompositeSrc
Member3 == 3 \in CompositeSrc
NonMember1 == ~(1 \in CompositeSrc)
NonMember10 == ~(10 \in CompositeSrc)

\* Source is intersection of SetPred and concrete set
CapSrc == {x \in ({n \in {1, 2, 3, 4, 5} : n > 2} \cap {3, 4, 5, 6}) : x < 5}
CapMember3 == 3 \in CapSrc
CapMember4 == 4 \in CapSrc
CapNonMember5 == ~(5 \in CapSrc)
CapNonMember2 == ~(2 \in CapSrc)

\* Source is difference of SetPred and concrete set
DiffSrc == {x \in ({n \in {1, 2, 3, 4, 5} : n > 1} \ {3, 5}) : x < 5}
DiffMember2 == 2 \in DiffSrc
DiffMember4 == 4 \in DiffSrc
DiffNonMember3 == ~(3 \in DiffSrc)
DiffNonMember5 == ~(5 \in DiffSrc)

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

    // Union source tests
    assert_eq!(
        ctx.eval_op("Member2").unwrap(),
        Value::Bool(true),
        "#3979: 2 should be in SetPred with SetCup source"
    );
    assert_eq!(
        ctx.eval_op("Member3").unwrap(),
        Value::Bool(true),
        "#3979: 3 should be in SetPred with SetCup source"
    );
    assert_eq!(
        ctx.eval_op("NonMember1").unwrap(),
        Value::Bool(true),
        "#3979: 1 should NOT be in SetPred with SetCup source (fails source pred)"
    );
    assert_eq!(
        ctx.eval_op("NonMember10").unwrap(),
        Value::Bool(true),
        "#3979: 10 should NOT be in SetPred with SetCup source (fails outer pred)"
    );

    // Intersection source tests
    assert_eq!(
        ctx.eval_op("CapMember3").unwrap(),
        Value::Bool(true),
        "#3979: 3 should be in SetPred with SetCap source"
    );
    assert_eq!(
        ctx.eval_op("CapMember4").unwrap(),
        Value::Bool(true),
        "#3979: 4 should be in SetPred with SetCap source"
    );
    assert_eq!(
        ctx.eval_op("CapNonMember5").unwrap(),
        Value::Bool(true),
        "#3979: 5 should NOT be in SetPred with SetCap source (fails outer pred)"
    );
    assert_eq!(
        ctx.eval_op("CapNonMember2").unwrap(),
        Value::Bool(true),
        "#3979: 2 should NOT be in SetPred with SetCap source (fails inner pred)"
    );

    // Difference source tests
    assert_eq!(
        ctx.eval_op("DiffMember2").unwrap(),
        Value::Bool(true),
        "#3979: 2 should be in SetPred with SetDiff source"
    );
    assert_eq!(
        ctx.eval_op("DiffMember4").unwrap(),
        Value::Bool(true),
        "#3979: 4 should be in SetPred with SetDiff source"
    );
    assert_eq!(
        ctx.eval_op("DiffNonMember3").unwrap(),
        Value::Bool(true),
        "#3979: 3 should NOT be in SetPred with SetDiff source (removed by diff)"
    );
    assert_eq!(
        ctx.eval_op("DiffNonMember5").unwrap(),
        Value::Bool(true),
        "#3979: 5 should NOT be in SetPred with SetDiff source (removed by diff)"
    );
}

/// Same test for values_equal path: the private materialize_setpred inside
/// values_equal must also restore captured state when comparing SetPred values.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_equality_uses_captured_state_not_current() {
    clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
VARIABLE x
Filtered == {r \in SUBSET {1, 2} : x \in r}
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // Evaluate with x = 1
    let state1 = vec![Value::int(1)];
    ctx.bind_state_array(&state1);
    let setpred_val = ctx.eval_op("Filtered").unwrap();

    // Build expected result: subsets of {1,2} containing 1 = {{1}, {1,2}}
    let expected = Value::set([
        Value::set([Value::int(1)]),
        Value::set([Value::int(1), Value::int(2)]),
    ]);

    // Change state to x = 99
    let state2 = vec![Value::int(99)];
    ctx.bind_state_array(&state2);

    // values_equal compares SetPred by materializing — must use captured state
    let eq = values_equal(&ctx, &setpred_val, &expected, None).unwrap();
    assert!(
        eq,
        "SetPred equality should use captured state (x=1), not current (x=99)"
    );
}
