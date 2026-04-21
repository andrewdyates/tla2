// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Higher-order operator closure bugs - Bug #174 variants
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config};

// ============================================================================
// Bug #174: Higher-order operator closure bug with quantified variables
// ============================================================================

/// Bug #174: Closure capture doesn't include local_stack bindings
///
/// When a LET-defined operator references a variable bound by an outer quantifier
/// (e.g., `\A R \in ... : LET RR(s,t) == <<s,t>> \in R ...`), and that operator
/// is passed to a higher-order operator, the closure didn't capture the
/// quantified variable R because:
/// 1. Closure creation only captured `ctx.env`, not `ctx.local_stack`
/// 2. Quantified variables are often bound only in `local_stack`
///
/// Without the fix: InR closure can't find R, returns FALSE for ApplyPred(InR, 2)
/// With the fix: R is captured in closure, ApplyPred(InR, 2) correctly returns TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_174_closure_captures_quantified_variables() {
    let spec = r#"
---- MODULE ClosureBug174Test ----
EXTENDS Integers, FiniteSets

VARIABLE x

\* Simple higher-order operator - applies P to y
ApplyPred(P(_), y) == P(y)

\* Test 1: LET operator with constant - baseline
Test1 ==
    LET S == {1, 2, 3}
        InS(y) == y \in S
    IN ApplyPred(InS, 2)

\* Test 2: LET operator with quantified variable - the bug
\* R is bound by \A, and InR captures R
Test2 ==
    \A R \in {{1, 2, 3}} :
        LET InR(y) == y \in R   \* InR must capture R from quantifier
        IN ApplyPred(InR, 2)    \* Should be TRUE (2 \in {1,2,3})

\* Test 3: LET operator with EXISTS-bound variable
Test3 ==
    \E R \in {{1, 2, 3}} :
        LET InR(y) == y \in R
        IN ApplyPred(InR, 2)

\* All tests should be TRUE
AllPass == Test1 /\ Test2 /\ Test3

Init == x = 0
Next == x' = x

\* Invariant - if any test fails, this will be violated
Inv == AllPass
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected: All tests pass, invariant holds
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #174 not fixed! Invariant {} violated - closure didn't capture quantified variable",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #174b: Higher-order + zero-arg operator combination with ForAll-bound variables
// ============================================================================

/// Bug #174b: ZERO_ARG_OP_CACHE returns stale values when BOTH a higher-order operator
/// AND a zero-arg operator reference a ForAll-bound variable.
///
/// The bug specifically triggers when:
/// 1. ForAll binds variable R
/// 2. Higher-order operator RR(s,t) references R in its body
/// 3. Zero-arg operator S calls a module-level operator with R
/// 4. Both RR and S are passed to a function that uses them
///
/// Each individual pattern works correctly:
/// - Higher-order RR alone with hardcoded S: PASSES
/// - Zero-arg S == Support(R) alone without higher-order: PASSES
/// - Both together: FAILS
///
/// Root cause: eval_forall uses bind_bound_var (ctx.bind) which doesn't add R to
/// local_stack. When both operator types reference R, some caching interaction
/// causes incorrect evaluation. The dependency tracking fails to properly
/// invalidate cached results.
///
/// Minimal reproduction from TransitiveClosure spec (tc_debug3.tla).
///
/// Fix: Change bind_bound_var to bind_local_bound_var in eval_forall (eval.rs:10750)
/// and eval_exists (eval.rs:10786) so quantified variables are tracked for caching.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_174b_higher_order_plus_zero_arg_forall_bound() {
    // Minimal reproduction from tc_debug3.tla (TransitiveClosure):
    // - ForAll binds R to a set of tuples: {<<1, 2>>, <<2, 1>>}
    // - RR(s,t) is higher-order operator: <<s,t>> \in R
    // - S is zero-arg operator: Support(R) which computes {1, 2}
    // - TC5(RR, S, 1, 1) uses both to check transitive closure
    //
    // TLC returns TRUE (correct).
    // TLA2 returns FALSE (bug) when BOTH operators are used.
    //
    // Verified working cases:
    // - RR + S={1,2} hardcoded: PASSES
    // - S=Support(R) + R passed directly (no higher-order): PASSES
    let spec = r#"
---- MODULE Bug174Full ----
EXTENDS Integers, FiniteSets

Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}

NatOverride == 0..10

\* TC5 with higher-order R and set S
TC5(R(_,_), S, s, t) ==
  LET CR[n \in NatOverride, v \in S] ==
          IF n = 0 THEN R(s, v)
                   ELSE \/ CR[n-1, v]
                        \/ \E u \in S : CR[n-1, u] /\ R(u, v)
  IN  /\ s \in S
      /\ t \in S
      /\ CR[Cardinality(S)-1, t]

\* Test: Both RR and S reference ForAll-bound R
\* TLC returns TRUE, TLA2 returns FALSE (bug)
Test ==
    \A R \in {{<<1, 2>>, <<2, 1>>}} :
         LET RR(s, t) == <<s, t>> \in R   \* Higher-order: references R
             S == Support(R)               \* Zero-arg: calls module-level op with R
         IN  TC5(RR, S, 1, 1)

VARIABLE x
Init == x = 0
Next == x' = x
Inv == Test
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected after fix: TC5 returns TRUE, invariant holds
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #174b confirmed! Invariant {} violated - higher-order + zero-arg operator combination \
                 fails with ForAll-bound variable. Fix: change bind_bound_var to bind_local_bound_var at eval.rs:10750",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #174c: CHOOSE with higher-order + zero-arg operator caching bug
// ============================================================================

/// Bug #174c: CHOOSE uses bind_bound_var instead of bind_local_bound_var
///
/// Same root cause as #174b, but affects CHOOSE expressions.
/// The bug requires BOTH a higher-order operator AND a zero-arg operator
/// referencing the CHOOSE-bound variable. The combination triggers caching
/// issues because the bound variable isn't tracked in local_stack.
///
/// Fix: Change bind_bound_var to bind_local_bound_var at eval.rs:10817
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_174c_choose_with_zero_arg_op_caching() {
    // Same TC5 pattern as 174b, but using CHOOSE instead of ForAll
    // The CHOOSE picks the set where TC5 returns TRUE
    let spec = r#"
---- MODULE Bug174Choose ----
EXTENDS Integers, FiniteSets

Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}

NatOverride == 0..10

\* TC5 with higher-order R and set S
TC5(R(_,_), S, s, t) ==
  LET CR[n \in NatOverride, v \in S] ==
          IF n = 0 THEN R(s, v)
                   ELSE \/ CR[n-1, v]
                        \/ \E u \in S : CR[n-1, u] /\ R(u, v)
  IN  /\ s \in S
      /\ t \in S
      /\ CR[Cardinality(S)-1, t]

\* Test: CHOOSE with both higher-order and zero-arg operators referencing R
\* CHOOSE should find a valid R where TC5(RR, S, 1, 1) is TRUE
Test ==
    LET ChosenR == CHOOSE R \in {{<<1, 2>>, <<2, 1>>}} :
                       LET RR(s, t) == <<s, t>> \in R   \* Higher-order: references R
                           S == Support(R)               \* Zero-arg: calls module-level op with R
                       IN  TC5(RR, S, 1, 1)
    IN  ChosenR = {<<1, 2>>, <<2, 1>>}  \* The only candidate, TC5 should return TRUE

VARIABLE x
Init == x = 0
Next == x' = x
Inv == Test
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected after fix: CHOOSE correctly evaluates with fresh cache entries
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #174c confirmed! Invariant {} violated - CHOOSE with higher-order + zero-arg \
                 operator fails. Fix: change bind_bound_var to bind_local_bound_var at eval.rs:10817",
                invariant
            );
        }
        // EvalError (ChooseFailed) would also indicate bug - TC5 returned FALSE, CHOOSE found no match
        other => panic!(
            "Bug #174c: Unexpected result (possibly ChooseFailed due to caching bug): {:?}",
            other
        ),
    }
}

// ============================================================================
// Bug #174d: SetBuilder with higher-order + zero-arg operator caching bug
// ============================================================================

/// Bug #174d: SetBuilder {expr : x \in S} uses bind_bound_var instead of bind_local_bound_var
///
/// Same root cause as #174b, but affects set builder expressions.
/// The bug requires BOTH a higher-order operator AND a zero-arg operator
/// referencing the SetBuilder-bound variable.
///
/// Fix: Change bind_bound_var to bind_local_bound_var at eval.rs:10866
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_174d_set_builder_with_zero_arg_op_caching() {
    // Same TC5 pattern as 174b, but using SetBuilder instead of ForAll
    // Build a set of TC5 results for each R in the domain
    let spec = r#"
---- MODULE Bug174SetBuilder ----
EXTENDS Integers, FiniteSets

Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}

NatOverride == 0..10

\* TC5 with higher-order R and set S
TC5(R(_,_), S, s, t) ==
  LET CR[n \in NatOverride, v \in S] ==
          IF n = 0 THEN R(s, v)
                   ELSE \/ CR[n-1, v]
                        \/ \E u \in S : CR[n-1, u] /\ R(u, v)
  IN  /\ s \in S
      /\ t \in S
      /\ CR[Cardinality(S)-1, t]

\* Test: SetBuilder with both higher-order and zero-arg operators referencing R
\* Build set of TC5 results - should be {TRUE} since there's only one R
Test ==
    LET Results == { LET RR(s, t) == <<s, t>> \in R   \* Higher-order: references R
                         S == Support(R)               \* Zero-arg: calls module-level op with R
                     IN  TC5(RR, S, 1, 1)
                   : R \in {{<<1, 2>>, <<2, 1>>}} }
    IN  Results = {TRUE}  \* TC5 should return TRUE

VARIABLE x
Init == x = 0
Next == x' = x
Inv == Test
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected after fix: SetBuilder correctly evaluates with fresh cache entries
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #174d confirmed! Invariant {} violated - SetBuilder with higher-order + \
                 zero-arg operator fails. Fix: change bind_bound_var to bind_local_bound_var at eval.rs:10866",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}
