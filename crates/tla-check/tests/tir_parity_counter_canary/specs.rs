// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Spec constants and shared helpers for TIR parity canary tests.

use std::collections::BTreeMap;

use crate::common::parse_module;
use tla_check::{resolve_spec_from_config, CheckResult, Config, ModelChecker};
use tla_core::parse_to_syntax_tree;
use tla_eval::tir::TirEvalProbeCounts;

pub const COUNTER_SPEC: &str = "\
---- MODULE TirParityCounter ----
VARIABLE x
Init == x = [a |-> 1, b |-> <<2, 3>>]
Next ==
    IF x.a < 2
    THEN x' = [x EXCEPT !.a = x.a + 1]
    ELSE x' = x
TypeOK == x.a \\in {1, 2}
====";

pub const RENAMED_COUNTER_SPEC: &str = "\
---- MODULE TirParityResolvedCounter ----
VARIABLE x
Boot == x = [a |-> 1, b |-> <<2, 3>>]
Step ==
    IF x.a < 2
    THEN x' = [x EXCEPT !.a = x.a + 1]
    ELSE x' = x
Safe == x.a \\in {1, 2}
====";

pub const INIT_FALLBACK_SPEC: &str = "\
---- MODULE TirInitFallbackProbe ----
VARIABLE x
TypeOK == x \\in {0, 1, 2}
Init == x > 0 /\\ x < 2
Next == x' = x
====";

pub const LIVENESS_COUNTER_SPEC: &str = "\
---- MODULE TirParityLivenessCounter ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == IF x = 0 THEN x' = 1 ELSE x' = x
Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)
Live == []<>(x = 1)
====";

pub const PROMOTED_PROPERTY_INVARIANT_SPEC: &str = "\
---- MODULE TirPromotedPropertyInvariant ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Safe == x <= 1
AlwaysSafe == []Safe
====";

pub const DIEHARD_SPEC: &str = "\
---- MODULE TirParityDieHard ----
VARIABLE big, small
SmallCap == 3
BigCap == 5
Init ==
    /\\ big = 0
    /\\ small = 0
Min(m, n) == IF m < n THEN m ELSE n
FillSmallJug  ==
    /\\ small' = SmallCap
    /\\ big' = big
FillBigJug ==
    /\\ big' = BigCap
    /\\ small' = small
EmptySmallJug ==
    /\\ small' = 0
    /\\ big' = big
EmptyBigJug ==
    /\\ big' = 0
    /\\ small' = small
SmallToBig ==
    /\\ big' = Min(big + small, BigCap)
    /\\ small' = small - (big' - big)
BigToSmall ==
    /\\ small' = Min(big + small, SmallCap)
    /\\ big' = big - (small' - small)
Next ==
    \\/ FillSmallJug
    \\/ FillBigJug
    \\/ EmptySmallJug
    \\/ EmptyBigJug
    \\/ SmallToBig
    \\/ BigToSmall
TypeOK ==
    /\\ small \\in {0, 1, 2, 3}
    /\\ big \\in {0, 1, 2, 3, 4, 5}
====";

pub const RICH_SPEC: &str = "\
---- MODULE TirParityRich ----
VARIABLE pos, flags
Positions == {1, 2}
Init ==
    /\\ pos = 1
    /\\ flags = [p \\in Positions |-> FALSE]
Next ==
    LET other == CHOOSE p \\in Positions : p /= pos
    IN
        /\\ pos' = other
        /\\ flags' = [flags EXCEPT ![pos] = TRUE]
Inv ==
    /\\ pos \\in Positions
    /\\ \\A p \\in DOMAIN flags : flags[p] \\in {TRUE, FALSE}
    /\\ \\E p \\in Positions : TRUE
    /\\ {p \\in Positions : flags[p] = TRUE} \\subseteq Positions
    /\\ LET count == flags[1] IN count \\in {TRUE, FALSE}
====";

pub const CONSTRAINT_TERMINAL_SPEC: &str = "\
---- MODULE TirParityConstraintTerminal ----
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE x' = x
Bound == x <= 1
ActionOk == x' <= 1
Done == x = 1
====";

/// Part of #3163: LAMBDA closure round-trip through TIR.
pub const LAMBDA_SPEC: &str = "\
---- MODULE TirLambdaRoundTrip ----
VARIABLE x
Apply(op(_), v) == op(v)
Init == x = Apply(LAMBDA y : y + 1, 0)
Next == IF x < 3 THEN x' = Apply(LAMBDA y : y + 1, x) ELSE x' = x
TypeOK == x \\in 1..3
====";

/// Part of #3262: parameterized LET lowered to LAMBDA in TIR.
pub const PARAMETERIZED_LET_SPEC: &str = "\
---- MODULE TirParityParamLet ----
VARIABLE pos
Init == pos = 0
Next ==
    LET Inc(x) == x + 1
        Add(a, b) == a + b
    IN
        IF pos < 3
        THEN pos' = Inc(pos)
        ELSE pos' = Add(pos, 0)
TypeOK == pos \\in 0..3
====";

/// Regression test for #3276 Root Cause B: parameterized operators in an OR
/// with EXCEPT expressions that reference state variables.
pub const MULTI_ACTION_EXCEPT_SPEC: &str = "\
---- MODULE TirEvalMultiActionExcept ----
VARIABLE x, pc
N == 3
Procs == 0..(N-1)
A(self) ==
    /\\ pc[self] = \"a\"
    /\\ pc' = [pc EXCEPT ![self] = \"b\"]
    /\\ x' = [x EXCEPT ![self] = 1]
B(self) ==
    /\\ pc[self] = \"b\"
    /\\ pc' = [pc EXCEPT ![self] = \"Done\"]
    /\\ x' = [x EXCEPT ![self] = x[self] + 1]
Init ==
    /\\ pc = [p \\in Procs |-> \"a\"]
    /\\ x = [p \\in Procs |-> 0]
Next == \\E self \\in Procs : A(self) \\/ B(self)
TypeOK ==
    /\\ \\A p \\in Procs : pc[p] \\in {\"a\", \"b\", \"Done\"}
    /\\ \\A p \\in Procs : x[p] \\in 0..2
====";

pub const SUBSET_CONSTRAINED_SPEC: &str = "\
---- MODULE TirSubsetConstrainedParity ----
VARIABLE vals, done
S == {1, 2, 3}
Init ==
    /\\ vals = {}
    /\\ done = FALSE
Pick ==
    /\\ done = FALSE
    /\\ \\E r \\in SUBSET S : vals \\subseteq r /\\ r \\subseteq S /\\ vals' = r /\\ done' = done
Finish ==
    /\\ done = FALSE
    /\\ done' = TRUE
    /\\ vals' = vals
Stutter ==
    /\\ done = TRUE
    /\\ UNCHANGED <<vals, done>>
Next == Pick \\/ Finish \\/ Stutter
TypeOK ==
    /\\ vals \\subseteq S
    /\\ done \\in {TRUE, FALSE}
====";

pub fn check_liveness_property_spec(src: &str, property: &str) -> CheckResult {
    let module = parse_module(src);
    let tree = parse_to_syntax_tree(src);
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved =
        resolve_spec_from_config(&spec_config, &tree).expect("spec resolution should succeed");
    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec![property.to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.check()
}

pub fn check_promoted_property_invariant_spec(src: &str, property: &str) -> CheckResult {
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec![property.to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.check()
}

pub fn probe_counts(
    snapshot: &BTreeMap<String, TirEvalProbeCounts>,
    name: &str,
) -> TirEvalProbeCounts {
    snapshot.get(name).copied().unwrap_or_default()
}

pub fn probe_delta(
    before: &BTreeMap<String, TirEvalProbeCounts>,
    after: &BTreeMap<String, TirEvalProbeCounts>,
    name: &str,
) -> TirEvalProbeCounts {
    let before_counts = probe_counts(before, name);
    let after_counts = probe_counts(after, name);
    TirEvalProbeCounts {
        expr_evals: after_counts
            .expr_evals
            .saturating_sub(before_counts.expr_evals),
        named_op_evals: after_counts
            .named_op_evals
            .saturating_sub(before_counts.named_op_evals),
    }
}

pub fn check_multi_action_except(tir_eval: Option<&str>) -> CheckResult {
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();
    let module = parse_module(MULTI_ACTION_EXCEPT_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let _ = tir_eval; // env var controls TIR activation
    checker.check()
}

pub fn constraint_terminal_config() -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["Bound".to_string()],
        action_constraints: vec!["ActionOk".to_string()],
        terminal: Some(tla_check::TerminalSpec::Operator("Done".to_string())),
        ..Default::default()
    }
}
