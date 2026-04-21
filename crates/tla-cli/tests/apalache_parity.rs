// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Apalache feature parity regression test suite.
//!
//! Exercises Apalache-specific features supported by TLA2:
//! - BMC mode (bounded model checking via z4)
//! - BMC incremental solving
//! - k-induction symbolic safety proving
//! - Inductive invariant convenience mode
//! - Config-free CLI flags (--no-config --init --next --inv)
//! - Trace invariants (--trace-inv)
//! - Apalache operators: ApaFoldSet, ApaFoldSeqLeft, MkSeq, Repeat, Guess, SetAsFun
//! - Apalache annotation operators: Skolem, Expand, ConstCardinality
//! - Variants module: Variant, VariantTag, VariantGetUnsafe, VariantGetOrElse
//! - Lambda support for higher-order Apalache operators
//! - Type checking basics: typed variables (Nat, BOOLEAN, sets)
//! - Set operations: Union, Intersect, SetMinus, subset, Cardinality
//! - Function operations: construction, application, DOMAIN, EXCEPT
//! - Record operations: construction, field access, EXCEPT, DOMAIN
//! - Sequence operations: Head, Tail, Len, Append, SubSeq
//! - Quantifiers: \A, \E with bounded sets, nested quantifiers
//! - CHOOSE: bounded CHOOSE from finite sets
//! - Integer arithmetic: add, sub, mul, div, mod, negation, comparison, range
//! - ITF output: Informal Trace Format JSON output mode
//!
//! Part of #3828.

mod common;

use std::time::Duration;

const TIMEOUT: Duration = Duration::from_secs(30);

// ---------------------------------------------------------------------------
// Helper: write spec + cfg into a temp dir, returning path strings.
// ---------------------------------------------------------------------------

fn setup_spec(prefix: &str, spec_src: &str, cfg_src: &str) -> (common::TempDir, String, String) {
    let dir = common::TempDir::new(prefix);
    let (spec_path, cfg_path) = common::write_spec_and_config(&dir, prefix, spec_src, cfg_src);
    (
        dir,
        spec_path.to_str().unwrap().to_string(),
        cfg_path.to_str().unwrap().to_string(),
    )
}

fn run(args: &[&str]) -> (i32, String, String) {
    common::run_tla_parsed_with_timeout(args, TIMEOUT)
}

// ===========================================================================
// BMC mode tests (require z4 feature)
// ===========================================================================

/// BMC: safety holds within bounded depth (no bug found).
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bmc_safe_counter() {
    let (_dir, spec, cfg) = setup_spec(
        "BmcSafeCounter",
        r#"---- MODULE BmcSafeCounter ----
VARIABLE x
Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE x
Safety == x >= 0 /\ x <= 3
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let (code, stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--bmc",
        "5",
        "--soundness",
        "heuristic",
    ]);
    assert_eq!(
        code, 0,
        "BMC safe counter should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("NO BUG FOUND"),
        "Expected 'NO BUG FOUND' in output.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// BMC: safety violated within bounded depth (counterexample found).
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bmc_unsafe_counter() {
    let (_dir, spec, cfg) = setup_spec(
        "BmcUnsafeCounter",
        r#"---- MODULE BmcUnsafeCounter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 2
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let (code, _stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--bmc",
        "5",
        "--soundness",
        "heuristic",
    ]);
    assert_ne!(
        code, 0,
        "BMC unsafe counter should report violation.\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("VIOLATION"),
        "Expected 'VIOLATION' in stderr.\nstderr:\n{stderr}"
    );
}

/// BMC incremental solving: reuses solver state across depths.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bmc_incremental_safe() {
    let (_dir, spec, cfg) = setup_spec(
        "BmcIncrementalSafe",
        r#"---- MODULE BmcIncrementalSafe ----
VARIABLE y
Init == y \in {0, 1}
Next == y' = 1 - y
Safety == y \in {0, 1}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let (code, stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--bmc",
        "10",
        "--bmc-incremental",
        "--soundness",
        "heuristic",
    ]);
    assert_eq!(
        code, 0,
        "BMC incremental safe should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("NO BUG FOUND"),
        "Expected 'NO BUG FOUND' for incremental BMC.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// BMC with multiple state variables (integer + boolean).
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bmc_multi_variable() {
    let (_dir, spec, cfg) = setup_spec(
        "BmcMultiVar",
        r#"---- MODULE BmcMultiVar ----
VARIABLES x, flag
Init == x = 0 /\ flag = FALSE
Next == /\ x' = IF x < 5 THEN x + 1 ELSE x
        /\ flag' = (x' >= 3)
Safety == (flag = TRUE) => (x >= 3)
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let (code, stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--bmc",
        "8",
        "--soundness",
        "heuristic",
    ]);
    assert_eq!(
        code, 0,
        "BMC multi-var should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("NO BUG FOUND"),
        "Expected 'NO BUG FOUND'.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// k-Induction tests (require z4 feature)
// ===========================================================================

/// k-induction proves safety for a trivially inductive invariant.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_trivial_inductive() {
    let (_dir, spec, cfg) = setup_spec(
        "KindTrivial",
        r#"---- MODULE KindTrivial ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
Safety == x \in {0, 1}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let (code, stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--kinduction",
        "--soundness",
        "heuristic",
    ]);
    // k-induction should either prove or report no bug found
    let combined = format!("{stdout}\n{stderr}");
    assert!(
        code == 0 || combined.contains("PROVED") || combined.contains("k-inductive"),
        "k-induction should succeed for trivially inductive spec.\ncode: {code}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// k-induction finds counterexample at base case.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_base_case_violation() {
    let (_dir, spec, cfg) = setup_spec(
        "KindBaseViol",
        r#"---- MODULE KindBaseViol ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 5
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let (code, _stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--kinduction",
        "--kinduction-max-k",
        "10",
        "--soundness",
        "heuristic",
    ]);
    // Should find a counterexample in the base case (BMC phase)
    assert_ne!(
        code, 0,
        "k-induction should find base case violation.\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Inductive invariant convenience mode (require z4 feature)
// ===========================================================================

/// Inductive check: both initiation and consecution hold.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_inductive_check_pass() {
    let (_dir, spec, cfg) = setup_spec(
        "IndCheckPass",
        r#"---- MODULE IndCheckPass ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = 1 - x
IndInv == x \in {0, 1}
===="#,
        "INIT Init\nNEXT Next\n",
    );

    let (code, stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--inductive-check",
        "IndInv",
        "--soundness",
        "heuristic",
    ]);
    let combined = format!("{stdout}\n{stderr}");
    // Should report that the invariant is inductive (both phases pass)
    assert!(
        code == 0 || combined.contains("inductive") || combined.contains("PROVED"),
        "Inductive check should pass.\ncode: {code}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Config-free CLI flags (--no-config --init --next --inv)
// ===========================================================================

/// Apalache-style config-free checking: --no-config with --init/--next/--inv.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_no_config_cli_flags() {
    let dir = common::TempDir::new("NoConfigCli");
    let spec_path = dir.path.join("NoConfigCliFlags.tla");
    std::fs::write(
        &spec_path,
        r#"---- MODULE NoConfigCliFlags ----
VARIABLE counter
MyInit == counter = 0
MyNext == counter' = IF counter < 2 THEN counter + 1 ELSE counter
TypeOK == counter \in {0, 1, 2}
===="#,
    )
    .unwrap();
    let spec_str = spec_path.to_str().unwrap();

    let (code, stdout, stderr) = run(&[
        "check",
        spec_str,
        "--no-config",
        "--init",
        "MyInit",
        "--next",
        "MyNext",
        "--inv",
        "TypeOK",
    ]);
    assert_eq!(
        code, 0,
        "Config-free CLI flags should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Convention defaults: --no-config without --init/--next uses "Init" and "Next".
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_no_config_convention_defaults() {
    let dir = common::TempDir::new("NoConfigDefault");
    let spec_path = dir.path.join("NoConfigDefault.tla");
    std::fs::write(
        &spec_path,
        r#"---- MODULE NoConfigDefault ----
VARIABLE x
Init == x = 0
Next == x' = IF x < 2 THEN x + 1 ELSE x
TypeOK == x \in {0, 1, 2}
===="#,
    )
    .unwrap();
    let spec_str = spec_path.to_str().unwrap();

    let (code, stdout, stderr) = run(&["check", spec_str, "--no-config", "--inv", "TypeOK"]);
    assert_eq!(
        code, 0,
        "Convention defaults Init/Next should be used.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Trace invariant tests
// ===========================================================================

/// Trace invariant passes: monotonically increasing x.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_trace_invariant_monotonic_pass() {
    let (_dir, spec, cfg) = setup_spec(
        "TraceInvPass",
        r#"---- MODULE TraceInvPass ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
MonotonicTrace(hist) ==
    \A i \in 1..(Len(hist) - 1) :
        hist[i + 1].x >= hist[i].x
===="#,
        "INIT Init\nNEXT Next\n",
    );

    let (code, stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--trace-inv",
        "MonotonicTrace",
        "--no-deadlock",
    ]);
    assert_eq!(
        code, 0,
        "Trace invariant should pass for monotonic x.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Trace invariant violation: x increases but trace inv requires decrease.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_trace_invariant_violation() {
    let (_dir, spec, cfg) = setup_spec(
        "TraceInvFail",
        r#"---- MODULE TraceInvFail ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
DecreasingTrace(hist) ==
    \A i \in 1..(Len(hist) - 1) :
        hist[i + 1].x < hist[i].x
===="#,
        "INIT Init\nNEXT Next\n",
    );

    let (code, _stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--trace-inv",
        "DecreasingTrace",
        "--no-deadlock",
    ]);
    assert_ne!(
        code, 0,
        "Trace invariant should report violation.\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Apalache operator tests (BFS mode)
// ===========================================================================

/// ApaFoldSet: fold binary operator over a set.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_apa_fold_set() {
    let (_dir, spec, cfg) = setup_spec(
        "FoldSetSum",
        r#"---- MODULE FoldSetSum ----
EXTENDS Apalache, Naturals
VARIABLE total
Add(a, b) == a + b
Init == total = ApaFoldSet(Add, 0, {1, 2, 3})
Next == UNCHANGED total
Correct == total = 6
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Correct\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "ApaFoldSet should compute correct sum.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// ApaFoldSeqLeft: fold binary operator left over a sequence.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_apa_fold_seq_left() {
    let (_dir, spec, cfg) = setup_spec(
        "FoldSeqConcat",
        r#"---- MODULE FoldSeqConcat ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE result
Acc(a, b) == a + b
Init == result = ApaFoldSeqLeft(Acc, 0, <<10, 20, 30>>)
Next == UNCHANGED result
Correct == result = 60
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Correct\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "ApaFoldSeqLeft should compute correct sum.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// MkSeq: build a sequence from an operator.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_mkseq() {
    let (_dir, spec, cfg) = setup_spec(
        "MkSeqDoubles",
        r#"---- MODULE MkSeqDoubles ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE seq
Double(i) == i * 2
Init == seq = MkSeq(4, Double)
Next == UNCHANGED seq
Correct == /\ Len(seq) = 4
           /\ seq[1] = 2 /\ seq[2] = 4
           /\ seq[3] = 6 /\ seq[4] = 8
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Correct\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "MkSeq should produce correct sequence.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Repeat: iterated application of operator.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_repeat() {
    let (_dir, spec, cfg) = setup_spec(
        "RepeatAccum",
        r#"---- MODULE RepeatAccum ----
EXTENDS Apalache, Naturals
VARIABLE val
F(x, i) == x + i
Init == val = Repeat(F, 3, 0)
Next == UNCHANGED val
Correct == val = 6
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Correct\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Repeat should compute correct result.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Guess: nondeterministic choice from set.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_guess() {
    let (_dir, spec, cfg) = setup_spec(
        "GuessNondet",
        r#"---- MODULE GuessNondet ----
EXTENDS Apalache, Naturals
VARIABLE chosen
Init == chosen = Guess({1, 2, 3})
Next == UNCHANGED chosen
InRange == chosen \in {1, 2, 3}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT InRange\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Guess should pick from set.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// SetAsFun: convert set of pairs to function.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_set_as_fun() {
    let (_dir, spec, cfg) = setup_spec(
        "SetAsFunPairs",
        r#"---- MODULE SetAsFunPairs ----
EXTENDS Apalache, Naturals
VARIABLE f
Init == f = SetAsFun({<<1, 10>>, <<2, 20>>})
Next == UNCHANGED f
Correct == f[1] = 10 /\ f[2] = 20
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Correct\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "SetAsFun should produce correct function.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Skolem, Expand, ConstCardinality: identity annotation operators.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_annotation_operators() {
    let (_dir, spec, cfg) = setup_spec(
        "SkolemIdentity",
        r#"---- MODULE SkolemIdentity ----
EXTENDS Apalache, Naturals, FiniteSets
VARIABLE x
Init == x \in {1, 2, 3}
Next == UNCHANGED x
SkolemOK == Skolem(\E y \in {1, 2, 3} : y = x)
ExpandOK == x \in Expand({1, 2, 3})
CardOK == ConstCardinality(Cardinality({1, 2, 3})) = 3
===="#,
        "INIT Init\nNEXT Next\nINVARIANT SkolemOK\nINVARIANT ExpandOK\nINVARIANT CardOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Annotation operators should be identity.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Lambda with ApaFoldSet: anonymous operator in fold.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_lambda_fold() {
    let (_dir, spec, cfg) = setup_spec(
        "LambdaFold",
        r#"---- MODULE LambdaFold ----
EXTENDS Apalache, Naturals
VARIABLE total
Init == total = ApaFoldSet(LAMBDA a, b: a + b, 0, {10, 20, 30})
Next == UNCHANGED total
Correct == total = 60
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Correct\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Lambda fold should compute correct sum.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Variants module tests
// ===========================================================================

/// Variants: Variant, VariantTag, VariantGetUnsafe, VariantGetOrElse.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_variant_operations() {
    let (_dir, spec, cfg) = setup_spec(
        "VariantOps",
        r#"---- MODULE VariantOps ----
EXTENDS Variants, Naturals
VARIABLE v
Init == v = Variant("Some", 42)
Next == UNCHANGED v
TagOK == VariantTag(v) = "Some"
ValueOK == VariantGetUnsafe("Some", v) = 42
FallbackOK == VariantGetOrElse("None", v, -1) = -1
===="#,
        "INIT Init\nNEXT Next\nINVARIANT TagOK\nINVARIANT ValueOK\nINVARIANT FallbackOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Variant operations should work correctly.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// VariantFilter: filter set of variants by tag.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_variant_filter() {
    let (_dir, spec, cfg) = setup_spec(
        "VariantFilter",
        r#"---- MODULE VariantFilter ----
EXTENDS Variants, Naturals, FiniteSets
VARIABLE s
Init == s = {Variant("Ok", 1), Variant("Err", 2), Variant("Ok", 3)}
Next == UNCHANGED s
FilterOK == Cardinality(VariantFilter("Ok", s)) = 2
===="#,
        "INIT Init\nNEXT Next\nINVARIANT FilterOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "VariantFilter should filter by tag.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Combined Apalache features
// ===========================================================================

/// Combined: MkSeq + ApaFoldSeqLeft (pipe MkSeq output into fold).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_mkseq_then_fold() {
    let (_dir, spec, cfg) = setup_spec(
        "MkSeqThenFold",
        r#"---- MODULE MkSeqThenFold ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE result
Id(i) == i
Sum(acc, x) == acc + x
Init == result = ApaFoldSeqLeft(Sum, 0, MkSeq(4, Id))
Next == UNCHANGED result
Correct == result = 10
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Correct\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "MkSeq then fold should compute 1+2+3+4=10.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Combined: --no-config + --inv + ApaFoldSet (config-free + Apalache ops).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_no_config_with_apalache_ops() {
    let dir = common::TempDir::new("NoConfigApa");
    let spec_path = dir.path.join("NoConfigApa.tla");
    std::fs::write(
        &spec_path,
        r#"---- MODULE NoConfigApa ----
EXTENDS Apalache, Naturals
VARIABLE total
Add(a, b) == a + b
Init == total = ApaFoldSet(Add, 0, {5, 10, 15})
Next == UNCHANGED total
Correct == total = 30
===="#,
    )
    .unwrap();
    let spec_str = spec_path.to_str().unwrap();

    let (code, stdout, stderr) = run(&[
        "check",
        spec_str,
        "--no-config",
        "--init",
        "Init",
        "--next",
        "Next",
        "--inv",
        "Correct",
    ]);
    assert_eq!(
        code, 0,
        "Config-free + Apalache operators should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Type checking basics (BFS mode)
// ===========================================================================

/// Type checking basics: typed variables (Nat, BOOLEAN, set of Nat).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_type_check_basics() {
    let (_dir, spec, cfg) = setup_spec(
        "TypeCheckBasics",
        r#"---- MODULE TypeCheckBasics ----
EXTENDS Naturals, FiniteSets
VARIABLES count, flag, items

Init == /\ count = 0
        /\ flag = FALSE
        /\ items = {}

Next == /\ count' = IF count < 3 THEN count + 1 ELSE count
        /\ flag' = (count' >= 2)
        /\ items' = items \union {count'}

CountTypeOK == count \in Nat
FlagTypeOK == flag \in BOOLEAN
ItemsTypeOK == \A i \in items : i \in Nat
SizeOK == Cardinality(items) <= 4
===="#,
        "INIT Init\nNEXT Next\nINVARIANT CountTypeOK\nINVARIANT FlagTypeOK\nINVARIANT ItemsTypeOK\nINVARIANT SizeOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Type check basics should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Set operations (BFS mode)
// ===========================================================================

/// Set operations: Union, Intersect, SetMinus, subset, Cardinality.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_set_operations() {
    let (_dir, spec, cfg) = setup_spec(
        "SetOperations",
        r#"---- MODULE SetOperations ----
EXTENDS Naturals, FiniteSets
VARIABLE s

A == {1, 2, 3}
B == {2, 3, 4}

Init == s = A \union B
Next == UNCHANGED s

UnionOK == s = {1, 2, 3, 4}
IntersectOK == A \intersect B = {2, 3}
DiffOK == A \ B = {1}
SubsetOK == {2, 3} \subseteq A
CardOK == Cardinality(s) = 4
===="#,
        "INIT Init\nNEXT Next\nINVARIANT UnionOK\nINVARIANT IntersectOK\nINVARIANT DiffOK\nINVARIANT SubsetOK\nINVARIANT CardOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Set operations should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Function operations (BFS mode)
// ===========================================================================

/// Function operations: construction, application, DOMAIN, EXCEPT, function set.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_function_operations() {
    let (_dir, spec, cfg) = setup_spec(
        "FunctionOperations",
        r#"---- MODULE FunctionOperations ----
EXTENDS Naturals, FiniteSets
VARIABLE f

Init == f = [i \in {1, 2, 3} |-> i * 10]
Next == f' = [f EXCEPT ![2] = 99]

DomainOK == DOMAIN f = {1, 2, 3}
AppOK == f[1] = 10
ExceptOK == f[2] \in {20, 99}
FuncSetOK == [{"a", "b"} -> {0, 1}] # {}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT DomainOK\nINVARIANT AppOK\nINVARIANT ExceptOK\nINVARIANT FuncSetOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Function operations should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Record operations (BFS mode)
// ===========================================================================

/// Record operations: construction, field access, EXCEPT, DOMAIN.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_record_operations() {
    let (_dir, spec, cfg) = setup_spec(
        "RecordOperations",
        r#"---- MODULE RecordOperations ----
EXTENDS Naturals
VARIABLE r

Init == r = [name |-> "alice", age |-> 30]
Next == IF r.age < 31 THEN r' = [r EXCEPT !.age = r.age + 1]
        ELSE UNCHANGED r

FieldOK == r.name = "alice"
AgeOK == r.age >= 30
ExceptOK == r.age <= 31
DomainOK == DOMAIN r = {"name", "age"}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT FieldOK\nINVARIANT AgeOK\nINVARIANT ExceptOK\nINVARIANT DomainOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Record operations should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Sequence operations (BFS mode)
// ===========================================================================

/// Sequence operations: Head, Tail, Len, Append, SubSeq.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_sequence_operations() {
    let (_dir, spec, cfg) = setup_spec(
        "SequenceOperations",
        r#"---- MODULE SequenceOperations ----
EXTENDS Naturals, Sequences
VARIABLE seq

Init == seq = <<10, 20, 30>>
Next == IF Len(seq) < 4 THEN seq' = Append(seq, 40)
        ELSE UNCHANGED seq

LenOK == Len(seq) \in {3, 4}
HeadOK == Head(seq) = 10
TailOK == Head(Tail(seq)) = 20
AppendOK == Len(seq) <= 4
SubSeqOK == SubSeq(seq, 1, 2) = <<10, 20>>
===="#,
        "INIT Init\nNEXT Next\nINVARIANT LenOK\nINVARIANT HeadOK\nINVARIANT TailOK\nINVARIANT AppendOK\nINVARIANT SubSeqOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Sequence operations should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Quantifier tests (BFS mode)
// ===========================================================================

/// Quantifiers: \A, \E with bounded sets, nested quantifiers.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_quantifiers() {
    let (_dir, spec, cfg) = setup_spec(
        "Quantifiers",
        r#"---- MODULE Quantifiers ----
EXTENDS Naturals
VARIABLE x

S == {1, 2, 3, 4, 5}

Init == x \in S
Next == x' = IF x < 5 THEN x + 1 ELSE 1

ForAllOK == \A i \in S : i >= 1
ExistsOK == \E i \in S : i = x
BoundedForAll == \A i \in {1, 2} : \A j \in {3, 4} : i < j
NestedExists == \E i \in S : \E j \in S : i + j = 6
InRangeOK == x \in S
===="#,
        "INIT Init\nNEXT Next\nINVARIANT ForAllOK\nINVARIANT ExistsOK\nINVARIANT BoundedForAll\nINVARIANT NestedExists\nINVARIANT InRangeOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Quantifiers should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// CHOOSE tests (BFS mode)
// ===========================================================================

/// CHOOSE: bounded CHOOSE from finite set.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_choose_bounded() {
    let (_dir, spec, cfg) = setup_spec(
        "ChooseBounded",
        r#"---- MODULE ChooseBounded ----
EXTENDS Naturals
VARIABLE picked

S == {10, 20, 30}

Init == picked = CHOOSE v \in S : v >= 20
Next == UNCHANGED picked

InSetOK == picked \in S
GeOK == picked >= 20
MinChoose == LET m == CHOOSE v \in {1, 2, 3} : \A w \in {1, 2, 3} : v <= w
             IN m = 1
===="#,
        "INIT Init\nNEXT Next\nINVARIANT InSetOK\nINVARIANT GeOK\nINVARIANT MinChoose\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "CHOOSE bounded should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Integer arithmetic tests (BFS mode)
// ===========================================================================

/// Integer arithmetic: add, sub, mul, div, mod, negation, comparison, range.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_integer_arithmetic() {
    let (_dir, spec, cfg) = setup_spec(
        "IntegerArithmetic",
        r#"---- MODULE IntegerArithmetic ----
EXTENDS Integers
VARIABLE x

Init == x = 0
Next == x' = IF x < 10 THEN x + 1 ELSE x

AddOK == 3 + 4 = 7
SubOK == 10 - 3 = 7
MulOK == 6 * 7 = 42
DivOK == 7 \div 2 = 3
ModOK == 7 % 2 = 1
NegOK == -5 + 5 = 0
CompareOK == /\ 3 < 5
             /\ 5 > 3
             /\ 3 <= 3
             /\ 3 >= 3
RangeOK == x \in 0..10
===="#,
        "INIT Init\nNEXT Next\nINVARIANT AddOK\nINVARIANT SubOK\nINVARIANT MulOK\nINVARIANT DivOK\nINVARIANT ModOK\nINVARIANT NegOK\nINVARIANT CompareOK\nINVARIANT RangeOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Integer arithmetic should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// ITF output tests (BFS mode)
// ===========================================================================

/// ITF output: successful check emits valid ITF JSON.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_itf_output_success() {
    let (_dir, spec, cfg) = setup_spec(
        "ItfSuccess",
        r#"---- MODULE ItfSuccess ----
EXTENDS Naturals
VARIABLE step

Init == step = 0
Next == step < 3 /\ step' = step + 1

TypeOK == step \in 0..3
===="#,
        "INIT Init\nNEXT Next\nINVARIANT TypeOK\n",
    );

    let (code, stdout, stderr) = run(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--output",
        "itf",
        "--no-deadlock",
    ]);
    assert_eq!(
        code, 0,
        "ITF output should succeed.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    // ITF output must be valid JSON on stdout
    assert!(
        stdout.contains("\"#meta\"") || stdout.contains("\"states\""),
        "ITF output should contain ITF JSON structure.\nstdout:\n{stdout}"
    );
    // Verify JSON parses successfully
    let parsed: Result<serde_json::Value, _> = serde_json::from_str(&stdout);
    assert!(
        parsed.is_ok(),
        "ITF output should be valid JSON.\nstdout:\n{stdout}\nparse error: {:?}",
        parsed.err()
    );
}

/// ITF output with trace-format: counterexample trace in ITF format.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_itf_trace_format_violation() {
    let (_dir, spec, cfg) = setup_spec(
        "ItfTraceFmt",
        r#"---- MODULE ItfTraceFmt ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = x + 1
Safety == x <= 2
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg, "--trace-format", "itf"]);
    assert_ne!(
        code, 0,
        "Should find violation.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    // When trace-format is itf, the counterexample trace should be ITF JSON on stdout
    if !stdout.is_empty() {
        let has_itf = stdout.contains("\"#meta\"")
            || stdout.contains("\"states\"")
            || stdout.contains("#meta");
        assert!(
            has_itf,
            "Trace format itf should emit ITF-structured output.\nstdout:\n{stdout}"
        );
    }
}

// ===========================================================================
// Safety violation tests (BFS mode) — expected failures
// ===========================================================================

/// Set operation violation: invariant fails due to incorrect set membership.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_set_membership_violation() {
    let (_dir, spec, cfg) = setup_spec(
        "SetMemViol",
        r#"---- MODULE SetMemViol ----
EXTENDS Naturals
VARIABLE x

Init == x \in {1, 2, 3}
Next == x' = x + 1
BadInv == x \in {1, 2, 3}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT BadInv\n",
    );

    let (code, _stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_ne!(
        code, 0,
        "Set membership violation should be detected.\nstderr:\n{stderr}"
    );
}

/// Quantifier violation: universal quantifier fails.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_quantifier_violation() {
    let (_dir, spec, cfg) = setup_spec(
        "QuantViol",
        r#"---- MODULE QuantViol ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = x + 1
AllPositive == \A i \in {x} : i > 0
===="#,
        "INIT Init\nNEXT Next\nINVARIANT AllPositive\n",
    );

    let (code, _stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_ne!(
        code, 0,
        "Quantifier violation should be detected.\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// := operator edge cases (Part of #3828)
// ===========================================================================

/// := operator in nested IF/THEN/ELSE and conjunctive lists.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_assign_op_nested() {
    let (_dir, spec, cfg) = setup_spec(
        "AssignOpNested",
        r#"---- MODULE AssignOpNested ----
EXTENDS Apalache, Naturals
VARIABLES x, y, z
Init ==
    /\ x := 0
    /\ y := 10
    /\ z := 0
Next ==
    /\ IF x < 3
       THEN x' := x + 1
       ELSE x' := x
    /\ IF y > 7
       THEN y' := y - 1
       ELSE y' := y
    /\ z' := x + y
XBounded == x \in 0..3
YBounded == y \in 7..10
ZBounded == z \in 0..13
===="#,
        "INIT Init\nNEXT Next\nINVARIANT XBounded\nINVARIANT YBounded\nINVARIANT ZBounded\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Nested := operator should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// := operator inside CASE expressions.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_assign_op_case() {
    let (_dir, spec, cfg) = setup_spec(
        "AssignOpCase",
        r#"---- MODULE AssignOpCase ----
EXTENDS Apalache, Naturals
VARIABLE phase
Init == phase := 0
Next ==
    CASE phase = 0 -> phase' := 1
      [] phase = 1 -> phase' := 2
      [] phase = 2 -> phase' := 3
      [] OTHER -> phase' := 0
InRange == phase \in 0..3
===="#,
        "INIT Init\nNEXT Next\nINVARIANT InRange\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "CASE with := operator should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// EXCEPT == edge cases (Part of #3828)
// ===========================================================================

/// EXCEPT with == (Apalache extension) and multiple field updates.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_except_double_eq() {
    let (_dir, spec, cfg) = setup_spec(
        "ExceptDoubleEq",
        r#"---- MODULE ExceptDoubleEq ----
EXTENDS Naturals
VARIABLE counters
Init == counters = [i \in {1, 2, 3} |-> 0]
Next ==
    \/ /\ counters[1] < 2
       /\ counters' = [counters EXCEPT ![1] == counters[1] + 1]
    \/ /\ counters[2] < 2 /\ counters[3] < 2
       /\ counters' = [counters EXCEPT ![2] == counters[2] + 1,
                                       ![3] == counters[3] + 1]
    \/ UNCHANGED counters
DomainOK == DOMAIN counters = {1, 2, 3}
NonNeg == \A i \in {1, 2, 3} : counters[i] >= 0
Bounded == \A i \in {1, 2, 3} : counters[i] <= 2
===="#,
        "INIT Init\nNEXT Next\nINVARIANT DomainOK\nINVARIANT NonNeg\nINVARIANT Bounded\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "EXCEPT with == should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// EXCEPT with multiple nested record field updates.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_except_multi_field() {
    let (_dir, spec, cfg) = setup_spec(
        "ExceptMultiField",
        r#"---- MODULE ExceptMultiField ----
EXTENDS Naturals
VARIABLE db
Init == db = [
    user |-> [name |-> "alice", age |-> 25, active |-> TRUE],
    count |-> 0
]
Next ==
    \/ /\ db.user.age < 27
       /\ db' = [db EXCEPT !.user.age = db.user.age + 1,
                            !.count = db.count + 1]
    \/ /\ db.count < 2
       /\ db' = [db EXCEPT !.user.name = "bob",
                            !.user.active = FALSE,
                            !.count = db.count + 1]
    \/ UNCHANGED db
NameOK == db.user.name \in {"alice", "bob"}
AgeOK == db.user.age >= 25 /\ db.user.age <= 27
CountOK == db.count >= 0 /\ db.count <= 4
ActiveOK == db.user.active \in BOOLEAN
StructureOK == DOMAIN db = {"user", "count"}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT NameOK\nINVARIANT AgeOK\nINVARIANT CountOK\nINVARIANT ActiveOK\nINVARIANT StructureOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Multi-field EXCEPT should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Type annotation <: operator (Part of #3828)
// ===========================================================================

/// <: type annotation operator used as identity.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_type_annotation() {
    let (_dir, spec, cfg) = setup_spec(
        "TypeAnnotation",
        r#"---- MODULE TypeAnnotation ----
EXTENDS Naturals, FiniteSets
a <: b == a
VARIABLE state
Init ==
    /\ state = [
        nums |-> {} <: {"set_of_int"},
        flag |-> FALSE,
        count |-> 0
       ]
Next ==
    \/ /\ state.count < 3
       /\ state' = [state EXCEPT
            !.nums = state.nums \union {state.count},
            !.count = state.count + 1]
    \/ UNCHANGED state
EmptyAnnotated == ({} <: {"type_hint"}) = {}
SetAnnotated == ({1, 2} <: {"type_hint"}) = {1, 2}
IntAnnotated == (42 <: "type_hint") = 42
BoolAnnotated == (TRUE <: "type_hint") = TRUE
SeqAnnotated == (<<1, 2>> <: "type_hint") = <<1, 2>>
CountOK == state.count \in 0..3
NumsOK == state.nums \subseteq 0..2
FlagOK == state.flag \in BOOLEAN
===="#,
        "INIT Init\nNEXT Next\nINVARIANT EmptyAnnotated\nINVARIANT SetAnnotated\nINVARIANT IntAnnotated\nINVARIANT BoolAnnotated\nINVARIANT SeqAnnotated\nINVARIANT CountOK\nINVARIANT NumsOK\nINVARIANT FlagOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Type annotation <: should work as identity.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// FunAsSeq with sequence operations (Part of #3828)
// ===========================================================================

/// FunAsSeq converting function to sequence, then using Append, Len, Head, etc.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_fun_as_seq_ops() {
    let (_dir, spec, cfg) = setup_spec(
        "FunAsSeqOps",
        r#"---- MODULE FunAsSeqOps ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE seq
f == [i \in {1, 2, 3} |-> i * 10]
asSeq == FunAsSeq(f, 3, 3)
Init == seq = asSeq
Next ==
    \/ /\ Len(seq) < 5
       /\ seq' = Append(seq, 40)
    \/ /\ Len(seq) > 1
       /\ seq' = Tail(seq)
    \/ UNCHANGED seq
AsSeqLenOK == Len(asSeq) = 3
AsSeqElem1 == asSeq[1] = 10
AsSeqElem2 == asSeq[2] = 20
AsSeqElem3 == asSeq[3] = 30
HeadOK == Head(asSeq) = 10
SubSeqOK == SubSeq(asSeq, 1, 2) = <<10, 20>>
===="#,
        "INIT Init\nNEXT Next\nINVARIANT AsSeqLenOK\nINVARIANT AsSeqElem1\nINVARIANT AsSeqElem2\nINVARIANT AsSeqElem3\nINVARIANT HeadOK\nINVARIANT SubSeqOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "FunAsSeq with sequence ops should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Variant state machine (Part of #3828)
// ===========================================================================

/// Variants used as a message-passing protocol state machine.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_variant_state_machine() {
    let (_dir, spec, cfg) = setup_spec(
        "VariantStateMachine",
        r#"---- MODULE VariantStateMachine ----
EXTENDS Variants, Naturals
VARIABLE msg
MkRequest(id) == Variant("Request", id)
MkResponse(val) == Variant("Response", val)
MkError(code) == Variant("Error", code)
Init == msg = MkRequest(1)
Next ==
    \/ /\ VariantTag(msg) = "Request"
       /\ msg' = MkResponse(VariantGetUnsafe("Request", msg) * 10)
    \/ /\ VariantTag(msg) = "Response"
       /\ LET val == VariantGetUnsafe("Response", msg)
          IN IF val > 50
             THEN msg' = MkError(500)
             ELSE msg' = MkRequest(val + 1)
    \/ /\ VariantTag(msg) = "Error"
       /\ msg' = MkRequest(0)
ValidTag == VariantTag(msg) \in {"Request", "Response", "Error"}
RequestVal == VariantTag(msg) = "Request" =>
    VariantGetUnsafe("Request", msg) \in 0..100
ResponseVal == VariantTag(msg) = "Response" =>
    VariantGetUnsafe("Response", msg) \in 0..1000
ErrorVal == VariantTag(msg) = "Error" =>
    VariantGetUnsafe("Error", msg) = 500
FallbackOK == VariantGetOrElse("Missing", msg, -1) = -1
===="#,
        "INIT Init\nNEXT Next\nINVARIANT ValidTag\nINVARIANT RequestVal\nINVARIANT ResponseVal\nINVARIANT ErrorVal\nINVARIANT FallbackOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Variant state machine should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Fold edge cases (Part of #3828)
// ===========================================================================

/// Nested fold: fold-of-fold and fold with record accumulator.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_fold_nested() {
    let (_dir, spec, cfg) = setup_spec(
        "FoldNested",
        r#"---- MODULE FoldNested ----
EXTENDS Apalache, Naturals, Sequences, FiniteSets
VARIABLE result
Add(a, b) == a + b
Mul(a, b) == a * b
SetA == {2, 3}
SetB == {4, 5}
ProdA == ApaFoldSet(Mul, 1, SetA)
ProdB == ApaFoldSet(Mul, 1, SetB)
SumOfProducts == ApaFoldSet(Add, 0, {ProdA, ProdB})
MergeCount(acc, x) ==
    [sum |-> acc.sum + x, count |-> acc.count + 1]
Stats == ApaFoldSet(MergeCount, [sum |-> 0, count |-> 0], {10, 20, 30})
Triple(i) == i * 3
TripleSeq == MkSeq(4, Triple)
SeqSum == ApaFoldSeqLeft(Add, 0, TripleSeq)
Init == result = SumOfProducts
Next == UNCHANGED result
SumOfProductsOK == SumOfProducts = 26
StatsOK == Stats.sum = 60 /\ Stats.count = 3
SeqSumOK == SeqSum = 30
TripleSeqOK == Len(TripleSeq) = 4
===="#,
        "INIT Init\nNEXT Next\nINVARIANT SumOfProductsOK\nINVARIANT StatsOK\nINVARIANT SeqSumOK\nINVARIANT TripleSeqOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Nested fold operations should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Fold edge cases: empty set, empty sequence, single-element inputs.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_fold_empty() {
    let (_dir, spec, cfg) = setup_spec(
        "FoldEmpty",
        r#"---- MODULE FoldEmpty ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE x
Add(a, b) == a + b
Init == x = 0
Next == IF x < 1 THEN x' = x + 1 ELSE UNCHANGED x
EmptySetFold == ApaFoldSet(Add, 42, {}) = 42
EmptySeqFold == ApaFoldSeqLeft(Add, 99, <<>>) = 99
SingleSetFold == ApaFoldSet(Add, 0, {7}) = 7
SingleSeqFold == ApaFoldSeqLeft(Add, 0, <<7>>) = 7
Max(a, b) == IF a >= b THEN a ELSE b
MaxOfSet == ApaFoldSet(Max, 0, {3, 7, 2, 9, 1}) = 9
===="#,
        "INIT Init\nNEXT Next\nINVARIANT EmptySetFold\nINVARIANT EmptySeqFold\nINVARIANT SingleSetFold\nINVARIANT SingleSeqFold\nINVARIANT MaxOfSet\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Fold with empty/single-element inputs should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// LAMBDA higher-order patterns (Part of #3828)
// ===========================================================================

/// LAMBDA expressions in various higher-order contexts.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_lambda_higher_order() {
    let (_dir, spec, cfg) = setup_spec(
        "LambdaHigherOrder",
        r#"---- MODULE LambdaHigherOrder ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE n
Init == n = 0
Next == IF n < 1 THEN n' = n + 1 ELSE UNCHANGED n
SumWithLambda == ApaFoldSet(LAMBDA a, b: a + b, 0, {1, 2, 3, 4, 5})
SumOK == SumWithLambda = 15
ProductWithLambda == ApaFoldSeqLeft(LAMBDA acc, x: acc * x, 1, <<2, 3, 4>>)
ProductOK == ProductWithLambda = 24
SquareSeq == MkSeq(4, LAMBDA i: i * i)
SquareOK == SquareSeq = <<1, 4, 9, 16>>
RepeatWithLambda == Repeat(LAMBDA x, i: x + i * 10, 3, 0)
RepeatOK == RepeatWithLambda = 60
ConditionalLambda == ApaFoldSet(
    LAMBDA a, b: IF b > 3 THEN a + b ELSE a,
    0,
    {1, 2, 3, 4, 5}
)
ConditionalOK == ConditionalLambda = 9
===="#,
        "INIT Init\nNEXT Next\nINVARIANT SumOK\nINVARIANT ProductOK\nINVARIANT SquareOK\nINVARIANT RepeatOK\nINVARIANT ConditionalOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Lambda higher-order patterns should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Option module state machine (Part of #3828)
// ===========================================================================

/// Option module operators in a state machine with full lifecycle.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_option_state_machine() {
    let (_dir, spec, cfg) = setup_spec(
        "OptionStateMachine",
        r#"---- MODULE OptionStateMachine ----
EXTENDS Integers, Sequences, Variants, FiniteSets
UNIT_VAL == "U_OF_UNIT"
Some(val) == Variant("Some", val)
NoneVal == Variant("None", UNIT_VAL)
IsSome(opt) == VariantTag(opt) = "Some"
IsNone(opt) == VariantTag(opt) = "None"
OptionGetOrElse(opt, default) == VariantGetOrElse("Some", opt, default)
OptionToSeq(opt) ==
    IF IsSome(opt) THEN <<VariantGetUnsafe("Some", opt)>> ELSE <<>>
OptionToSet(opt) ==
    IF IsSome(opt) THEN {VariantGetUnsafe("Some", opt)} ELSE {}
VARIABLE result
Init == result = NoneVal
Next ==
    \/ /\ IsNone(result)
       /\ result' = Some(1)
    \/ /\ IsSome(result)
       /\ LET val == OptionGetOrElse(result, 0)
          IN IF val < 5
             THEN result' = Some(val + 1)
             ELSE result' = NoneVal
ValidOption == IsSome(result) \/ IsNone(result)
NoneExclusive == IsNone(result) => ~IsSome(result)
SomeExclusive == IsSome(result) => ~IsNone(result)
GetOrElseOK == IsNone(result) => OptionGetOrElse(result, -1) = -1
ToSetOK == IsNone(result) => OptionToSet(result) = {}
ToSeqOK == IsNone(result) => OptionToSeq(result) = <<>>
SomeToSetOK == IsSome(result) =>
    Cardinality(OptionToSet(result)) = 1
SomeToSeqOK == IsSome(result) =>
    Len(OptionToSeq(result)) = 1
ValueBound == IsSome(result) =>
    OptionGetOrElse(result, 0) \in 1..5
===="#,
        "INIT Init\nNEXT Next\nINVARIANT ValidOption\nINVARIANT NoneExclusive\nINVARIANT SomeExclusive\nINVARIANT GetOrElseOK\nINVARIANT ToSetOK\nINVARIANT ToSeqOK\nINVARIANT SomeToSetOK\nINVARIANT SomeToSeqOK\nINVARIANT ValueBound\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Option state machine should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Mutual recursion (Part of #3828)
// ===========================================================================

/// Mutually recursive IsEven/IsOdd operators.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_recursive_mutual() {
    let (_dir, spec, cfg) = setup_spec(
        "RecursiveMutual",
        r#"---- MODULE RecursiveMutual ----
EXTENDS Naturals
VARIABLE k
RECURSIVE IsEven(_)
RECURSIVE IsOdd(_)
IsEven(n) == IF n = 0 THEN TRUE ELSE IsOdd(n - 1)
IsOdd(n) == IF n = 0 THEN FALSE ELSE IsEven(n - 1)
Init == k \in 0..6
Next == IF k < 6 THEN k' = k + 1 ELSE UNCHANGED k
EvenZero == IsEven(0) = TRUE
OddZero == IsOdd(0) = FALSE
EvenTwo == IsEven(2) = TRUE
OddThree == IsOdd(3) = TRUE
EvenFive == IsEven(5) = FALSE
OddFour == IsOdd(4) = FALSE
KBounded == k \in 0..6
===="#,
        "INIT Init\nNEXT Next\nINVARIANT EvenZero\nINVARIANT OddZero\nINVARIANT EvenTwo\nINVARIANT OddThree\nINVARIANT EvenFive\nINVARIANT OddFour\nINVARIANT KBounded\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Mutual recursion should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// RECURSIVE inside LET/IN blocks.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_recursive_let_in() {
    let (_dir, spec, cfg) = setup_spec(
        "RecursiveLetIn",
        r#"---- MODULE RecursiveLetIn ----
EXTENDS Naturals
VARIABLE n
Init == n = 0
Next == IF n < 1 THEN n' = n + 1 ELSE UNCHANGED n
FactLet(x) ==
    LET RECURSIVE fact(_)
        fact(m) == IF m <= 1 THEN 1 ELSE m * fact(m - 1)
    IN fact(x)
SumTo(x) ==
    LET RECURSIVE sum(_)
        sum(m) == IF m = 0 THEN 0 ELSE m + sum(m - 1)
    IN LET result == sum(x)
    IN result
Power(base, exp) ==
    LET RECURSIVE pow(_, _)
        pow(b, e) == IF e = 0 THEN 1 ELSE b * pow(b, e - 1)
    IN pow(base, exp)
FactOK == FactLet(5) = 120
SumOK == SumTo(10) = 55
PowerOK == Power(2, 8) = 256
Power0OK == Power(5, 0) = 1
===="#,
        "INIT Init\nNEXT Next\nINVARIANT FactOK\nINVARIANT SumOK\nINVARIANT PowerOK\nINVARIANT Power0OK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "RECURSIVE in LET/IN should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Cartesian product operations (Part of #3828)
// ===========================================================================

/// Cartesian product with quantifiers, tuple indexing, and cardinality.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_cartesian_ops() {
    let (_dir, spec, cfg) = setup_spec(
        "CartesianOps",
        r#"---- MODULE CartesianOps ----
EXTENDS Naturals, FiniteSets
VARIABLE pair
Colors == {"R", "G", "B"}
Sizes == {1, 2, 3}
Init == pair \in Colors \X Sizes
Next ==
    \E c \in Colors, s \in Sizes :
        pair' = <<c, s>>
PairInProduct == pair \in Colors \X Sizes
Color == pair[1] \in Colors
Size == pair[2] \in Sizes
ProductCard == Cardinality(Colors \X Sizes) = 9
ForAllPairs == \A p \in Colors \X Sizes : p[2] >= 1
ExistsPair == \E p \in Colors \X Sizes : p[1] = "R" /\ p[2] = 3
===="#,
        "INIT Init\nNEXT Next\nINVARIANT PairInProduct\nINVARIANT Color\nINVARIANT Size\nINVARIANT ProductCard\nINVARIANT ForAllPairs\nINVARIANT ExistsPair\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Cartesian product operations should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Set comprehension patterns (Part of #3828)
// ===========================================================================

/// Set comprehensions: map, filter, nested, and empty.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_set_comprehension() {
    let (_dir, spec, cfg) = setup_spec(
        "SetComprehension",
        r#"---- MODULE SetComprehension ----
EXTENDS Naturals, FiniteSets
VARIABLE items
Init == items = {1, 2, 3, 4, 5}
Next == UNCHANGED items
Doubled == {x * 2 : x \in items}
DoubledOK == Doubled = {2, 4, 6, 8, 10}
Evens == {x \in items : x % 2 = 0}
EvensOK == Evens = {2, 4}
Pairs == {<<x, y>> : x \in {1, 2}, y \in {3, 4}}
PairsOK == Cardinality(Pairs) = 4
Sums == {x + y : x \in {1, 2}, y \in {10, 20}}
SumsOK == Sums = {11, 12, 21, 22}
BigDoubled == {x * 2 : x \in {y \in items : y > 3}}
BigDoubledOK == BigDoubled = {8, 10}
EmptyFilter == {x \in items : x > 100} = {}
===="#,
        "INIT Init\nNEXT Next\nINVARIANT DoubledOK\nINVARIANT EvensOK\nINVARIANT PairsOK\nINVARIANT SumsOK\nINVARIANT BigDoubledOK\nINVARIANT EmptyFilter\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Set comprehension patterns should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// CONSTANT substitution (Part of #3828)
// ===========================================================================

/// CONSTANT declarations with config substitution.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_constants_config() {
    let (_dir, spec, cfg) = setup_spec(
        "ConstantsAndSymmetry",
        r#"---- MODULE ConstantsAndSymmetry ----
EXTENDS Naturals, FiniteSets
CONSTANT N, Vals
VARIABLE state
Init == state = [i \in 1..N |-> CHOOSE v \in Vals : TRUE]
Next ==
    \E i \in 1..N, v \in Vals :
        state' = [state EXCEPT ![i] = v]
DomainOK == DOMAIN state = 1..N
ValsOK == \A i \in 1..N : state[i] \in Vals
CardOK == Cardinality(Vals) >= 1
===="#,
        "CONSTANT N = 3\nCONSTANT Vals = {10, 20, 30}\nINIT Init\nNEXT Next\nINVARIANT DomainOK\nINVARIANT ValsOK\nINVARIANT CardOK\n",
    );

    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "CONSTANT substitution should work.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ===========================================================================
// Batch runner: discovers and checks all specs in tests/apalache_parity/
// ===========================================================================

/// Batch test: find all .tla/.cfg pairs in tests/apalache_parity/ and check them.
/// This ensures no regressions in the full Apalache parity suite.
#[cfg_attr(test, ntest::timeout(300000))]
#[test]
fn test_apalache_parity_batch() {
    // Find the apalache_parity directory relative to the workspace root
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let workspace_root = std::path::Path::new(manifest_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let specs_dir = workspace_root.join("tests/apalache_parity/specs");
    let configs_dir = workspace_root.join("tests/apalache_parity/configs");

    if !specs_dir.exists() {
        panic!("Apalache parity specs directory not found: {}", specs_dir.display());
    }

    let mut spec_files: Vec<_> = std::fs::read_dir(&specs_dir)
        .expect("read specs dir")
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "tla"))
        .map(|e| e.path())
        .collect();
    spec_files.sort();

    assert!(
        !spec_files.is_empty(),
        "No .tla files found in {}",
        specs_dir.display()
    );

    let mut pass = 0u32;
    let mut fail = 0u32;
    let mut failures: Vec<String> = Vec::new();

    // Specs known to have expected violations (non-zero exit is correct)
    let violation_specs: std::collections::HashSet<&str> = [
        "BmcUnsafeCounter",
    ].iter().copied().collect();

    // Specs that require special CLI flags and are tested individually.
    // BMC specs need --bmc flag; trace inv specs need --trace-inv flag;
    // NoConfigCliFlags has no .cfg file (uses --no-config).
    let skip_specs: std::collections::HashSet<&str> = [
        "BmcSafeCounter",
        "BmcIncrementalSafe",
        "BmcMultiVar",
        "TraceInvMonotonic",
        "TraceInvViolation",
        "NoConfigCliFlags",
    ].iter().copied().collect();

    for spec_path in &spec_files {
        let stem = spec_path.file_stem().unwrap().to_str().unwrap();
        let cfg_path = configs_dir.join(format!("{stem}.cfg"));

        if skip_specs.contains(stem) {
            continue;
        }

        if !cfg_path.exists() {
            failures.push(format!("{stem}: missing config file {}", cfg_path.display()));
            fail += 1;
            continue;
        }

        let spec_str = spec_path.to_str().unwrap();
        let cfg_str = cfg_path.to_str().unwrap();

        let (code, stdout, stderr) =
            common::run_tla_parsed_with_timeout(
                &["check", spec_str, "--config", cfg_str, "--no-deadlock"],
                Duration::from_secs(60),
            );

        let expects_violation = violation_specs.contains(stem);

        if expects_violation {
            // This spec should report a violation (non-zero exit)
            if code != 0 {
                pass += 1;
            } else {
                failures.push(format!(
                    "{stem}: expected violation but got exit 0\nstdout:\n{stdout}\nstderr:\n{stderr}"
                ));
                fail += 1;
            }
        } else {
            // Normal spec should pass (exit 0)
            if code == 0 {
                pass += 1;
            } else {
                failures.push(format!(
                    "{stem}: exit code {code}\nstdout:\n{stdout}\nstderr:\n{stderr}"
                ));
                fail += 1;
            }
        }
    }

    if !failures.is_empty() {
        panic!(
            "Apalache parity batch: {pass} passed, {fail} failed out of {} specs.\n\nFailures:\n{}",
            spec_files.len(),
            failures.join("\n\n---\n\n")
        );
    }

    // Verify we tested a reasonable number of specs (49 as of 2026-04-12)
    assert!(
        pass >= 45,
        "Expected at least 45 passing specs, got {pass}"
    );

    eprintln!(
        "Apalache parity batch: {pass}/{} specs passed.",
        spec_files.len()
    );
}

// ===========================================================================
// Individual tests for specs previously only covered by batch runner.
// Each test below exercises a specific Apalache parity feature category.
// Part of #3828.
// ===========================================================================

// ---------------------------------------------------------------------------
// Helper: load spec + config from tests/apalache_parity/ directory.
// ---------------------------------------------------------------------------

fn apalache_spec_path(name: &str) -> (String, String) {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let workspace_root = std::path::Path::new(manifest_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let spec = workspace_root
        .join(format!("tests/apalache_parity/specs/{name}.tla"))
        .to_str()
        .unwrap()
        .to_string();
    let cfg = workspace_root
        .join(format!("tests/apalache_parity/configs/{name}.cfg"))
        .to_str()
        .unwrap()
        .to_string();
    (spec, cfg)
}

/// CASE expressions: arms, OTHER clause, and nested CASE.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_case_expressions() {
    let (spec, cfg) = apalache_spec_path("CaseExpressions");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "CASE expressions should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// CONSTANTS with config file parameter overrides (model values, proc set).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_constants_config_model_values() {
    let (spec, cfg) = apalache_spec_path("ConstantsConfig");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "CONSTANTS config with model values should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Disjunctive actions: multi-action Next with named sub-actions.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_disjunctive_actions() {
    let (spec, cfg) = apalache_spec_path("DisjunctiveActions");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Disjunctive actions should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Function composition: nested application, function sets, equality.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_function_composition() {
    let (spec, cfg) = apalache_spec_path("FunctionComposition");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Function composition should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// LET-IN with parametric (non-nullary) local operators and nested bindings.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_let_in_parametric() {
    let (spec, cfg) = apalache_spec_path("LetInParametric");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Parametric LET-IN should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// LET-without-IN: Apalache extension for nested LET (Gap 13 feature).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_let_without_in() {
    let (spec, cfg) = apalache_spec_path("LetWithoutIn");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "LET-without-IN should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Nested EXCEPT: deep path updates on functions and records.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_nested_except() {
    let (spec, cfg) = apalache_spec_path("NestedExcept");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Nested EXCEPT should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Option module: Some, None, IsSome, IsNone, OptionGetOrElse, OptionToSet, OptionToSeq.
/// Gap 12 feature: Option module operators via Variants.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_option_ops() {
    let (spec, cfg) = apalache_spec_path("OptionOps");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Option module operators should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// RECURSIVE factorial: basic recursive operator.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_recursive_factorial() {
    let (spec, cfg) = apalache_spec_path("RecursiveFactorial");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Recursive factorial should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// RECURSIVE Fibonacci: branching recursion (not just linear).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_recursive_fibonacci() {
    let (spec, cfg) = apalache_spec_path("RecursiveFibonacci");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Recursive Fibonacci should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// String operations: equality, set membership, record field names.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_string_operations() {
    let (spec, cfg) = apalache_spec_path("StringOperations");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "String operations should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// SUBSET (powerset): enumeration, filtering by cardinality.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_subset_powerset() {
    let (spec, cfg) = apalache_spec_path("SubsetPowerset");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "SUBSET powerset should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Tuple quantifiers: \E t \in S \X T, \A t \in S \X T with indexing.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_tuple_quantifiers() {
    let (spec, cfg) = apalache_spec_path("TupleQuantifiers");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "Tuple quantifiers should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// := assignment operator: basic assignment semantics in BFS mode (Gap 12 feature).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_assign_op_basic() {
    let (spec, cfg) = apalache_spec_path("AssignOp");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg]);
    assert_eq!(
        code, 0,
        "AssignOp should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// ITF trace output: spec that produces a short deterministic trace for ITF testing.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_itf_trace_spec() {
    let (spec, cfg) = apalache_spec_path("ItfTrace");
    let (code, stdout, stderr) = run(&["check", &spec, "--config", &cfg, "--no-deadlock"]);
    assert_eq!(
        code, 0,
        "ItfTrace should pass.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
