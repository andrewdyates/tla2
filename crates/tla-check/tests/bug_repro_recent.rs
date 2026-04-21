// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recent bug fixes - Bugs #2566, #2834, #2899, #2822
//!
//! Split from bug_reproductions.rs — Part of #2850
//! Spec-loading tests (#3118, #3125) moved to bug_repro_spec_loading.rs — Part of #3671

mod common;

use common::parse_module;
use std::collections::HashMap;
use tla_check::{
    check_module, check_module_parallel, CheckResult, Config, ConstantValue, ModelChecker,
};

// ============================================================================
// Bug #2566: RECURSIVE operator evaluation causes OOM — bind_all() cloned
// entire env HashMap per call. Fixed by routing eval_apply through
// bind_all_fast() (O(1) per binding), matching TLC's Context.cons approach.
// ============================================================================

/// Spec with 5 RECURSIVE operators used as invariants. ADDRS={a1..a4},
/// VALUES={1,2} produces 16 distinct states matching TLC.
const SPEC_2566_RECURSIVE_OOM: &str = r#"
---- MODULE RecursiveOOMBug2566 ----
EXTENDS Integers, FiniteSets
CONSTANTS ADDRS, VALUES
VARIABLE mem
RECURSIVE SetSum(_, _)
SetSum(f, S) == IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE IN f[x] + SetSum(f, S \ {x})
RECURSIVE SetMax(_, _)
SetMax(f, S) == IF Cardinality(S) = 1 THEN f[CHOOSE x \in S : TRUE]
    ELSE LET x == CHOOSE x \in S : TRUE
             rest == S \ {x}
         IN IF f[x] >= SetMax(f, rest) THEN f[x] ELSE SetMax(f, rest)
RECURSIVE SetMin(_, _)
SetMin(f, S) == IF Cardinality(S) = 1 THEN f[CHOOSE x \in S : TRUE]
    ELSE LET x == CHOOSE x \in S : TRUE
             rest == S \ {x}
         IN IF f[x] <= SetMin(f, rest) THEN f[x] ELSE SetMin(f, rest)
RECURSIVE Hash(_, _)
Hash(f, S) == IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE IN (f[x] * 31 + 7) + Hash(f, S \ {x})
RECURSIVE Depth(_, _, _)
Depth(f, S, acc) == IF S = {} THEN acc
    ELSE LET x == CHOOSE x \in S : TRUE IN Depth(f, S \ {x}, acc + f[x])
Init == mem \in [ADDRS -> VALUES]
Swap(a1, a2) == /\ a1 /= a2
    /\ mem' = [mem EXCEPT ![a1] = mem[a2], ![a2] = mem[a1]]
Next == \E a1, a2 \in ADDRS : Swap(a1, a2)
SumOk == SetSum(mem, ADDRS) = SetSum(mem, ADDRS)
MaxOk == SetMax(mem, ADDRS) \in VALUES
MinOk == SetMin(mem, ADDRS) \in VALUES
HashOk == Hash(mem, ADDRS) >= 0
DepthOk == Depth(mem, ADDRS, 0) >= 0
====
"#;

/// Bug #2566: RECURSIVE operators must not OOM during model checking.
/// Before fix: OOM on DllToBst-like specs. After: <1s matching TLC (release mode).
/// Uses 2 addresses so double-recursive operators (SetMax, SetMin) complete in
/// unoptimized debug builds. Still exercises all 5 RECURSIVE operator patterns
/// (single-recursion: SetSum, Hash, Depth; double-recursion: SetMax, SetMin).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bug_2566_recursive_operators_no_oom() {
    let module = parse_module(SPEC_2566_RECURSIVE_OOM);
    let mut constants = HashMap::new();
    constants.insert("ADDRS".into(), ConstantValue::Value("{a1, a2}".into()));
    constants.insert("VALUES".into(), ConstantValue::Value("{1, 2}".into()));
    let invariants = ["SumOk", "MaxOk", "MinOk", "HashOk", "DepthOk"];
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: invariants.iter().map(|s| (*s).to_string()).collect(),
        constants,
        ..Default::default()
    };
    // TLC baseline: 4 distinct states (2^2 functions [ADDRS -> VALUES])
    let check = |mode: &str, result: CheckResult| match result {
        CheckResult::Success(stats) => assert_eq!(
            stats.states_found, 4,
            "{mode}: expected 4 states, got {}",
            stats.states_found
        ),
        other => panic!("{mode}: expected success, got: {:?}", other),
    };
    check("sequential", check_module(&module, &config));
    check("parallel", check_module_parallel(&module, &config, 2));
}

// ============================================================================
// Bug #2834: ModuleRef Fallback guard reads_next flag — INSTANCE property crash
// ============================================================================

/// Bug #2834: PROPERTY `[][M!Next]_M!vars` where M is an INSTANCE crashes with
/// "Primed variable cannot be evaluated (no next-state context)".
///
/// Root cause: `compile_guard_expr` for `Expr::ModuleRef` computed `reads_next`
/// via `expr_contains_prime_with_ctx`, which does a syntactic scan that cannot
/// follow ModuleRef indirection. The referenced operator's body contains primed
/// variables (e.g., `x' = ...`) but the ModuleRef expression itself has no
/// `Expr::Prime` node. With `reads_next: false`, the Fallback evaluator skips
/// setting up the next-state context, causing PrimedVariableNotBound during BFS.
///
/// Fix: Set `reads_next: true` (conservative) for all ModuleRef Fallback guards.
/// Confirmed on EWD998PCal (321,370 states) and MCKVsnap (32,293 states).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_2834_module_ref_implied_action_reads_next() {
    // Base module: defines an action with primed variables.
    let base_src = r#"
---- MODULE BaseAction ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = (x + 1) % 3
vars == x
====
"#;

    // Main module: instances the base module and asserts its spec as a PROPERTY.
    // The PROPERTY `[][BaseAction!Next]_BaseAction!vars` creates an implied action
    // with ModuleRef nodes. The `reads_next` flag must be true for the Fallback
    // guard to properly set up the next-state context.
    let main_src = r#"
---- MODULE MainRefinement ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = (x + 1) % 3
BaseAction == INSTANCE BaseAction
RefProp == BaseAction!Init /\ [][BaseAction!Next]_BaseAction!vars
====
"#;

    let base_module = parse_module(base_src);
    let main_module = parse_module(main_src);
    let extended_modules = vec![&base_module];

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["RefProp".to_string()],
        ..Default::default()
    };

    // Before fix: PrimedVariableNotBound error at first transition
    // After fix: 3 states (x=0, x=1, x=2), property satisfied
    let mut checker = ModelChecker::new_with_extends(&main_module, &extended_modules, &config);
    let result = checker.check();

    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "Expected 3 states (x=0,1,2), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Bug #2834 regression: ModuleRef implied action failed: {:?}",
                error
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #2899: Temporal operator behind Ident crashes safety-temporal fast path
// ============================================================================

/// Bug #2899: PROPERTY containing a bare INSTANCE'd spec whose body has
/// temporal operators behind identifiers (e.g., `ABCFairness == WF_vars(A)`)
/// crashes with "Temporal operators cannot be directly evaluated".
///
/// Root cause: `check_safety_temporal_property` flattens the property body
/// into And-terms, then classifies each term using a syntactic temporal
/// scanner (`contains_temporal_for_safety_temporal_fast_path`).  The scanner
/// treats `Ident("ABCFairness")` as a leaf, missing the temporal operators
/// (`WeakFair`) in the referenced operator's body.  The identifier is
/// incorrectly classified as an `init_term` and `eval_entry()` fails when
/// it resolves the body to `WF_vars(...) /\ WF_vars(...)`.
///
/// Fix: After the syntactic check, also check the resolved expression level
/// via `AstToLive::get_level_with_ctx()`, which follows operator references.
/// If temporal, return `NotApplicable` so the full liveness checker handles it.
///
/// Reproduces the MCAlternatingBit pattern: bare INSTANCE with a spec property
/// containing `Init /\ [][Next]_vars /\ Fairness`.
///
/// Expected result: LivenessViolation. The PROPERTY `Spec` includes
/// `WF_vars(Next)` which requires Next to fire infinitely often. Since the
/// model (INIT/NEXT config) allows infinite stuttering without fairness
/// assumptions, there exist behaviors that stutter forever, violating WF.
/// Before #3210, this test passed vacuously because liveness checking was
/// skipped in fp-only mode. Now that fp-only liveness works (#3210), the
/// correct violation is detected. Re: #3217.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_2899_temporal_ident_in_safety_temporal_fast_path() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    // Base module: defines Init, Next, vars, Fairness (temporal), and Spec.
    let base_src = r#"
---- MODULE TemporalBase ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = (x + 1) % 3
vars == x
Fairness == WF_vars(Next)
Spec == Init /\ [][Next]_vars /\ Fairness
====
"#;

    // Main module: bare INSTANCE imports all operators including Spec.
    // PROPERTY Spec triggers the safety-temporal fast path.
    let main_src = r#"
---- MODULE TemporalIdent ----
EXTENDS Naturals
VARIABLE x

INSTANCE TemporalBase
====
"#;

    let base_module = parse_module(base_src);
    let main_module = parse_module(main_src);
    let extended_modules = vec![&base_module];

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Spec".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&main_module, &extended_modules, &config);
    let result = checker.check();

    // The property Spec includes WF_vars(Next), which is violated by infinite
    // stuttering. The model has no FAIRNESS assumptions (INIT/NEXT config), so
    // unfair behaviors exist. The liveness checker correctly finds this violation.
    // Bug #2899 was about a crash — the key assertion is that we get a proper
    // result (LivenessViolation), not an Error from the safety-temporal crash.
    match &result {
        CheckResult::LivenessViolation {
            property, stats, ..
        } => {
            assert_eq!(
                stats.states_found, 3,
                "Expected 3 states (x=0,1,2), got {}",
                stats.states_found
            );
            assert_eq!(
                property, "Spec",
                "Expected violation of property 'Spec', got '{property}'"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Bug #2899 regression: temporal ident crashed safety-temporal fast path: {:?}",
                error
            );
        }
        other => panic!(
            "Expected LivenessViolation for WF_vars(Next) without fairness assumptions, got: {:?}",
            other
        ),
    }
}

// ============================================================================
// Bug #2822: ModelValue type mismatch — 'expected Record, got ModelValue'
// ============================================================================

/// Bug #2822: TLA2 raised "Type error: expected Record, got ModelValue" when
/// model values (from CONSTANT overrides) coexisted with records as function
/// values, and record field access occurred in invariant checking.
///
/// Affected specs: Huang (458/81256 states), MCKVsnap (319/32293 states).
///
/// Root cause: Integer overflow in release mode (without overflow-checks) and
/// scope isolation bugs (clone-at-branch) caused incorrect state exploration,
/// leading to states where model values appeared in record positions.
///
/// Fix: overflow-checks=true in release profile (083bc45cb) + clone-at-branch
/// scope isolation (189713a41).
///
/// This test exercises the pattern: model values as function domain elements
/// with records as function values, plus record field access in an invariant.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_2822_model_value_with_record_field_access() {
    let spec = r#"
---- MODULE Bug2822ModelValueRecord ----
EXTENDS Naturals

CONSTANTS Nodes

VARIABLE state

\* state maps model-value Nodes to records with fields
Init == state = [n \in Nodes |-> [val |-> FALSE]]

\* Toggle the val field — exercises record field access on function of model values
Next == \E n \in Nodes : state' = [state EXCEPT ![n] = [val |-> ~state[n].val]]

\* Invariant accesses record fields in context where model values are domain elements
TypeOK == \A n \in Nodes : state[n].val \in BOOLEAN

====
"#;

    let module = parse_module(spec);

    let mut constants = HashMap::new();
    constants.insert(
        "Nodes".to_string(),
        ConstantValue::ModelValueSet(vec!["n1".into(), "n2".into()]),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        constants,
        ..Default::default()
    };

    // Before fix: "Type error: expected Record, got ModelValue" during state exploration.
    // After fix: 4 states (2 nodes × 2 boolean values = 2^2 = 4).
    // TLC baseline: 4 states.
    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "Expected 4 states (2^2 for 2 boolean nodes), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Bug #2822 regression: model value type error in record context: {:?}",
                error
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Bug #2822 variant: model values as both domain elements AND values alongside
/// records, with record field access guarded by a condition. This mirrors the
/// MCKVsnap pattern where NoVal (model value) coexists with transaction records.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_2822_model_value_coexisting_with_records_in_range() {
    let spec = r#"
---- MODULE Bug2822ModelValueRange ----
EXTENDS Naturals

CONSTANTS Keys, NoVal

VARIABLE store

\* store maps Keys to either a record or NoVal (model value)
Init == store = [k \in Keys |-> NoVal]

\* Write a record value to a key, or reset to NoVal
Next ==
    \E k \in Keys :
        \/ store' = [store EXCEPT ![k] = [val |-> 1, ts |-> 0]]
        \/ store' = [store EXCEPT ![k] = NoVal]

\* Invariant: if a key has a record, its fields are valid
\* This exercises the pattern where model values and records share a domain
TypeOK ==
    \A k \in Keys :
        \/ store[k] = NoVal
        \/ /\ store[k].val \in Nat
           /\ store[k].ts \in Nat

====
"#;

    let module = parse_module(spec);

    let mut constants = HashMap::new();
    constants.insert(
        "Keys".to_string(),
        ConstantValue::ModelValueSet(vec!["k1".into(), "k2".into()]),
    );
    constants.insert("NoVal".to_string(), ConstantValue::ModelValue);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        constants,
        ..Default::default()
    };

    // 2 keys, each can be NoVal or [val|->1, ts|->0] = 2 values per key.
    // Total: 2^2 = 4 states.
    // TLC baseline: 4 states.
    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "Expected 4 states (2^2 for 2 keys × 2 values), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Bug #2822 regression: model value/record coexistence type error: {:?}",
                error
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}
