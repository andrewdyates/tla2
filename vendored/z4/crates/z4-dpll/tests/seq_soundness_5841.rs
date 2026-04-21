// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sequence theory soundness and regression tests (#5841, #5998, #6024, #6026, #6029, #6040).
//!
//! Split from seq_theory_5841.rs — these test axiom reduction soundness,
//! ground evaluation edge cases, and regression fixes.

mod common;

// ========== Soundness tests for new axiom reductions (#5841) ==========
// These tests verify the axioms produce UNSAT for contradictory formulas,
// not just SAT for everything.

#[test]
fn test_seq_contains_length_unsat_5841() {
    // contains(s, t) implies len(s) >= len(t).
    // If s = empty and t = unit(42), contains must be false.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= s (as seq.empty (Seq Int))))
         (assert (= t (seq.unit 42)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_prefixof_length_unsat_5841() {
    // prefixof(s, t) implies len(s) <= len(t).
    // If s has 2 elements and t has 1, prefix is impossible.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (assert (seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) t))
         (assert (= t (seq.unit 99)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_suffixof_length_unsat_5841() {
    // suffixof(s, t) implies len(s) <= len(t).
    // If s has 2 elements and t has 1, suffix is impossible.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (assert (seq.suffixof (seq.++ (seq.unit 1) (seq.unit 2)) t))
         (assert (= t (seq.unit 99)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_extract_oob_empty_5841() {
    // extract(s, 5, 1) from a 1-element sequence is out-of-bounds => empty.
    // Asserting len(extract) = 1 contradicts the OOB axiom.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 10)))
         (assert (= (seq.len (seq.extract s 5 1)) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_not_found_5841() {
    // indexof(s, t, 0) = -1 when !contains(s, t).
    // Asserting indexof >= 0 AND !contains should be unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (seq.contains s t)))
         (assert (>= (seq.indexof s t 0) 0))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_empty_source_unsat_5998() {
    // Regression for #5998: indexof synthesized contains(s, t) lacked axioms.
    // With len(s)=0 and len(t)=1, contains(s,t) requires len(s) >= len(t),
    // so indexof(s,t,0) >= 0 is impossible.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (>= (seq.indexof s t 0) 0))
         (assert (= (seq.len s) 0))
         (assert (= (seq.len t) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_implies_contains_5998() {
    // Regression for #5998: indexof > 0 must imply contains(s, t).
    // Asserting indexof = 1 AND !contains should be unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.indexof s t 0) 1))
         (assert (= (seq.len t) 1))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_basic_5998() {
    // Non-zero offset: offset < 0 => r = -1. Offset = -2 forces r = -1.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (= (seq.indexof s t (- 2)) (- 1))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_suffix_too_short_5998() {
    // Non-zero offset: indexof(s, t, 1) >= 0 with len(s) = 1, len(t) = 1.
    // offset = len(s) = 1 and t != "" (len(t) = 1), so axiom
    // "offset >= len(s) & t != '' => r = -1" should fire, giving r = -1.
    // This contradicts r >= 0.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (>= (seq.indexof s t 1) 0))
         (assert (= (seq.len s) 1))
         (assert (= (seq.len t) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Regression tests for #5998 Bug 2: tightest prefix ==========

#[test]
fn test_seq_indexof_not_found_returns_neg1_5998() {
    // !contains(s, t) => indexof(s, t, 0) = -1.
    // Asserting !contains AND indexof != -1 should be unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (seq.contains s t)))
         (assert (not (= (seq.indexof s t 0) (- 1))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_empty_needle_returns_zero_5998() {
    // indexof(s, "", 0) = 0 for any s.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (not (= (seq.indexof s (as seq.empty (Seq Int)) 0) 0)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Regression tests for #5998 Bug 3: non-zero offset ==========

#[test]
fn test_seq_indexof_negative_offset_returns_neg1_5998() {
    // indexof(s, t, -1) = -1 always.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (= (seq.indexof s t (- 1)) (- 1))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== seq.replace axiom tests (#5841) ==========

#[test]
fn test_seq_replace_empty_src_prepends_5841() {
    // replace(u, "", dst) = dst ++ u (Z3 semantics: empty src prepends dst).
    // Assert the result is not equal to dst ++ u — should be unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const dst (Seq Int))
         (declare-const src (Seq Int))
         (assert (= src (as seq.empty (Seq Int))))
         (assert (not (= (seq.replace u src dst) (seq.++ dst u))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_replace_not_found_unchanged_5841() {
    // When u does not contain src, replace returns u unchanged.
    // len(u) = 1, len(src) = 2 => u can't contain src => replace(u, src, dst) = u.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const src (Seq Int))
         (declare-const dst (Seq Int))
         (assert (= (seq.len u) 1))
         (assert (= (seq.len src) 2))
         (assert (not (= (seq.replace u src dst) u)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_replace_decomposition_5841() {
    // When contains(u, src) & src != "" & u != "":
    //   u = x ++ src ++ y  AND  r = x ++ dst ++ y
    // So if we assert seq.contains(u, src) and force constraints, the
    // decomposition should hold. Here: assert replace gives different result
    // than u when contains is true and dst != src. Should be SAT (the result
    // differs from u when src != dst and u contains src).
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const src (Seq Int))
         (declare-const dst (Seq Int))
         (declare-const r (Seq Int))
         (assert (= r (seq.replace u src dst)))
         (assert (seq.contains u src))
         (assert (not (= src (as seq.empty (Seq Int)))))
         (assert (not (= u (as seq.empty (Seq Int)))))
         (assert (not (= src dst)))
         (assert (not (= r u)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_replace_sat_basic_5841() {
    // Basic SAT: replace(u, src, dst) = some_value is satisfiable.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const src (Seq Int))
         (declare-const dst (Seq Int))
         (declare-const r (Seq Int))
         (assert (= r (seq.replace u src dst)))
         (assert (>= (seq.len u) 0))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// ========== Regression tests for #5998 R1 findings: cnt_earlier + idx_sfx ==========

#[test]
fn test_seq_indexof_nonzero_offset_value_bounds_5998() {
    // Regression for #5998 R1 Finding 1: non-zero offset idx_sfx decomposition.
    // When indexof(s, t, offset) >= 0, the result must be >= offset.
    // Without decomposition axioms, idx_sfx is unconstrained and the solver
    // could set r = 0 even with offset = 2.
    // Assert: indexof(s, t, 2) = 0 with contains(s, t), len(s) = 5, len(t) = 1.
    // Result 0 < offset 2 is impossible because r = offset + idx_sfx with idx_sfx >= 0.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 5))
         (assert (= (seq.len t) 1))
         (assert (= (seq.indexof s t 2) 0))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_result_ge_offset_5998() {
    // Regression for #5998 R1 Finding 1: idx_sfx decomposition gives idx_sfx >= 0
    // so r = offset + idx_sfx >= offset when found.
    // Assert: contains(s, t), len(s) = 5, len(t) = 1, offset = 3,
    //         indexof(s, t, 3) = 1 — should be UNSAT because r >= offset = 3.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 5))
         (assert (= (seq.len t) 1))
         (assert (= (seq.indexof s t 3) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_decomposition_sat_5998() {
    // SAT test for non-zero offset with decomposition.
    // Assert: contains(s, t), len(s) = 5, len(t) = 1, offset = 2.
    // indexof(s, t, 2) >= 2 should be SAT.
    // Verifies the decomposition axioms produce a consistent assignment.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 5))
         (assert (= (seq.len t) 1))
         (assert (>= (seq.indexof s t 2) 2))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_indexof_nonzero_offset_upper_bound_5998() {
    // The result of indexof(s, t, offset) must be < len(s) when found.
    // With decomposition: r = offset + len(sk_left2), and
    // sfx = sk_left2 ++ t ++ sk_right2, so len(sk_left2) + len(t) <= len(sfx).
    // len(sfx) = len(s) - offset, so r = offset + len(sk_left2) <= len(s) - len(t).
    // Assert: len(s) = 4, len(t) = 2, offset = 1, indexof(s, t, 1) = 4.
    // r = 4 requires len(sk_left2) = 3 but len(sfx) = 3, and
    // len(sk_left2) + len(t) = 3 + 2 = 5 > 3 = len(sfx), which is impossible.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 4))
         (assert (= (seq.len t) 2))
         (assert (= (seq.indexof s t 1) 4))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Negative contains soundness tests ==========
// The negative !contains axiom is currently incomplete (MVP): only the
// skolem decomposition is absent when contains=false, but no explicit
// negative axiom forces inconsistency. These tests check whether
// the solver is still sound on basic !contains scenarios.

#[test]
fn test_seq_not_contains_length_sat() {
    // !contains(s, t) when len(t) > len(s) — trivially SAT.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (seq.contains s t)))
         (assert (= (seq.len s) 1))
         (assert (= (seq.len t) 3))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_concrete_unsat() {
    // s = (seq.unit 1 ++ seq.unit 2 ++ seq.unit 3) clearly contains (seq.unit 2).
    // Asserting !contains is UNSAT. Fixed via contains-indexof bridge (#6024):
    // contains(s,t) <=> indexof(s,t,0) >= 0 forces indexof decomposition to
    // derive contradiction on concrete sequences.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= t (seq.unit 2)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// === Ground evaluation edge cases (#6024) ===

#[test]
fn test_seq_contains_empty_in_empty_sat_6024() {
    // Empty sequence contains empty sequence. ground_seq_contains returns true
    // for empty needle.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (as seq.empty (Seq Int))))
         (assert (seq.contains s (as seq.empty (Seq Int))))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_empty_in_nonempty_unsat_6024() {
    // Every sequence contains the empty sequence. Asserting !contains(s, empty)
    // should be UNSAT when s is concrete non-empty.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (not (seq.contains s (as seq.empty (Seq Int)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_not_contains_nonempty_in_empty_sat_6024() {
    // Empty sequence does not contain a non-empty sequence.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (as seq.empty (Seq Int))))
         (assert (not (seq.contains s (seq.unit 1))))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_partial_match_sat_6024() {
    // s = [1, 3, 2], t = [1, 2]. The elements 1 and 2 both appear but NOT
    // contiguously. !contains should be SAT (no contiguous subsequence).
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 3) (seq.unit 2)))))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_contains_self_sat_6024() {
    // A concrete sequence always contains itself.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (seq.contains s t))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_self_unsat_6024() {
    // Asserting a sequence does NOT contain itself is UNSAT.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 5) (seq.unit 6))))
         (assert (not (seq.contains s s)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// === seq.at tests (#6029) ===

#[test]
fn test_seq_at_sat_basic_6029() {
    // seq.at(s, 1) on s = [1, 2, 3] should return (seq.unit 2)
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.at s 1) (seq.unit 2)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_at_consistency_6029() {
    // seq.at(s, i) is lowered to seq.extract(s, i, 1).
    // The result should have length 1 for valid indices.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const r (Seq Int))
         (assert (= s (seq.++ (seq.unit 10) (seq.++ (seq.unit 20) (seq.unit 30)))))
         (assert (= r (seq.at s 0)))
         (assert (= (seq.len r) 1))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_at_no_parse_error_6029() {
    // Verify that seq.at is recognized (no UndefinedSymbol error)
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 5)))
         (assert (= (seq.len (seq.at s 0)) 1))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// === Unsupported seq op allowlist guard (#6026) ===

#[test]
fn test_seq_replace_all_returns_unknown_6026() {
    // seq.replace_all is parsed but has no axiom support.
    // The allowlist guard must return unknown (not false-SAT).
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= t (seq.replace_all s (seq.unit 1) (seq.unit 2))))
         (assert (= (seq.len s) 3))
         (check-sat)",
    );
    assert_eq!(result, "unknown");
}

// === Soundness regression: prefixof + extract axiom interaction (#6033) ===

#[test]
fn test_seq_prefixof_extract_interaction_sat_6033() {
    // False-UNSAT regression: prefixof and extract axiom decompositions
    // on a concrete 3-element sequence produce conflicting skolem constraints.
    // Z3 correctly returns sat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (= (seq.extract s 1 1) (seq.unit 2)))
         (check-sat)",
    );
    // Fixed (#6033): removed broken completeness axiom that created
    // overlapping skolem decompositions. Z3 and z4 both return sat.
    assert_eq!(result, "sat");
}

// === Soundness: prefixof completeness (#6035) ===

#[test]
fn test_seq_not_prefixof_concrete_prefix_unsat_6035() {
    // [1] IS a prefix of [1,2]. NOT prefixof must be unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_not_prefixof_non_prefix_sat_6035() {
    // [5] is NOT a prefix of [1,2]. NOT prefixof must be sat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 5)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_prefixof_longer_prefix_sat_6035() {
    // [1,2,3] is NOT a prefix of [1,2] (too long). NOT prefixof must be sat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// ========== #6028: nth-constrained !contains false-SAT ==========

#[test]
fn test_seq_nth_constrained_not_contains_unsat_6028() {
    // Sequence defined element-by-element via seq.nth + seq.len constraints.
    // s = [1, 2, 3], t = [2]. contains(s, t) must be true,
    // so !contains(s, t) is unsatisfiable.
    // Before #6028 fix: z4 returned false-SAT because build_ground_seq_map
    // only recognized seq.unit/seq.++/seq.empty patterns, missing nth-defined seqs.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (= t (seq.unit 2)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_constrained_not_contains_sat_6028() {
    // s = [1, 2, 3], t = [5]. Element 5 not in s, so !contains is satisfiable.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (= t (seq.unit 5)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_nth_constrained_empty_contains_unsat_6028() {
    // Empty sequence is always contained. !contains(s, empty) is unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 2))
         (assert (= (seq.nth s 0) 10))
         (assert (= (seq.nth s 1) 20))
         (assert (= t (as seq.empty (Seq Int))))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_incomplete_no_forced_eval_6028() {
    // Incomplete nth constraints (missing index 1 of 3). The ground
    // reconstruction should NOT happen since not all elements are known.
    // Result is sat because the solver can freely choose nth(s,1).
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 2) 3))
         (assert (= t (seq.unit 2)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_nth_constrained_not_prefixof_unsat_6036() {
    // s = [1, 2, 3] via nth. [1] IS a prefix of s, so !prefixof is unsat.
    // Requires nth ground equality injection (#6036) so prefixof axioms
    // can reason about the sequence structure.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (not (seq.prefixof (seq.unit 1) s)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== last_indexof rightmost guarantee tests (#6030) ==========
// W4 implemented last_indexof axioms but didn't test the key semantic:
// returning the LAST (rightmost) position, not just any position.

#[test]
fn test_seq_last_indexof_rightmost_value_6030() {
    // t = [1, 2, 1], s = [1]. last_indexof(t, s) should be 2 (last occurrence).
    // Assert i != 2 to verify the rightmost axiom forces the correct value.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (declare-const i Int)
         (assert (= t (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 1)))))
         (assert (= i (seq.last_indexof t (seq.unit 1))))
         (assert (not (= i 2)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "last_indexof([1,2,1], [1]) must be 2 (rightmost), not 0"
    );
}

#[test]
fn test_seq_last_indexof_rightmost_not_first_6030() {
    // t = [1, 2, 1], s = [1]. last_indexof(t, s) should NOT be 0 (first occurrence).
    // This is the dual: asserting i = 0 should be unsat because the axioms
    // enforce the rightmost guarantee via !contains(tail(s) ++ sk_right, s).
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (declare-const i Int)
         (assert (= t (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 1)))))
         (assert (= i (seq.last_indexof t (seq.unit 1))))
         (assert (= i 0))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "last_indexof([1,2,1], [1]) cannot be 0 — rightmost guarantee requires i=2"
    );
}

#[test]
fn test_seq_last_indexof_single_occurrence_6030() {
    // t = [1, 2, 3], s = [2]. last_indexof = indexof = 1 (only one occurrence).
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (declare-const i Int)
         (assert (= t (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= i (seq.last_indexof t (seq.unit 2))))
         (assert (not (= i 1)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "last_indexof([1,2,3], [2]) must be 1 (only occurrence)"
    );
}

// === Soundness: prefixof+extract interaction with nth-defined sequences ===

#[test]
fn test_seq_nth_prefixof_extract_interaction_sat_6033() {
    // Regression: nth-defined seq with BOTH prefixof and extract.
    // s = [1,2,3] via nth. prefixof([1], s) is true and extract(s,1,1) = [2].
    // Z3 returns sat. Z4 must NOT return false-UNSAT.
    // This is the #6033 variant with nth-defined (not concat-defined) sequences.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (= (seq.extract s 1 1) (seq.unit 2)))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "#6033 variant: nth-defined seq with prefixof+extract must be sat"
    );
}

// === Soundness: seq.extract ground evaluation (#6040) ===

#[test]
fn test_seq_extract_ground_false_sat_6040() {
    // Reproduction from #6040: extract(s, 0, 1) on s = [1,2,3] must equal [1].
    // Asserting it equals [5] must be unsat.
    // Previously returned sat because skolem decomposition couldn't force the result.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.extract s 0 1) (seq.unit 5)))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3], 0, 1) = [1], not [5]");
}

#[test]
fn test_seq_extract_ground_middle_6040() {
    // Extract middle element: extract([1,2,3], 1, 1) = [2].
    // Asserting it equals [9] must be unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.extract s 1 1) (seq.unit 9)))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3], 1, 1) = [2], not [9]");
}

#[test]
fn test_seq_extract_ground_multi_elem_6040() {
    // Extract 2 elements: extract([1,2,3], 0, 2) = [1,2].
    // Asserting len = 1 must be unsat (it should be 2).
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.len (seq.extract s 0 2)) 1))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "extract([1,2,3], 0, 2) has length 2, not 1"
    );
}

#[test]
fn test_seq_extract_ground_oob_6040() {
    // Extract beyond bounds: extract([1,2], 5, 1) = empty.
    // Asserting len > 0 must be unsat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (> (seq.len (seq.extract s 5 1)) 0))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "extract([1,2], 5, 1) = empty (out of bounds)"
    );
}

#[test]
fn test_seq_extract_ground_clamped_6040() {
    // Extract clamped: extract([1,2,3], 1, 10) = [2,3] (n exceeds remaining).
    // The result should have length 2.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.len (seq.extract s 1 10)) 3))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "extract([1,2,3], 1, 10) has length 2, not 3"
    );
}

#[test]
fn test_seq_extract_ground_correct_sat_6040() {
    // Positive test: extract([1,2,3], 0, 1) = [1] should be sat.
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.extract s 0 1) (seq.unit 1)))
         (check-sat)",
    );
    assert_eq!(result, "sat", "extract([1,2,3], 0, 1) = [1] is correct");
}

// ========== Multi-element extract ground eval (#6040) ==========

/// extract([1,2,3], 0, 2) should be [1,2]; claiming it's [1,99] is UNSAT.
#[test]
fn test_seq_extract_multi_elem_wrong_second_unsat_6040() {
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 2)))
         (assert (= e (seq.++ (seq.unit 1) (seq.unit 99))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],0,2) != [1,99]");
}

/// extract([1,2,3], 0, 2) should be [1,2]; claiming it's [99,2] is UNSAT.
#[test]
fn test_seq_extract_multi_elem_wrong_first_unsat_6040() {
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 2)))
         (assert (= e (seq.++ (seq.unit 99) (seq.unit 2))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],0,2) != [99,2]");
}

/// Positive test: extract([1,2,3], 0, 2) = [1,2] should be SAT.
#[test]
fn test_seq_extract_multi_elem_correct_sat_6040() {
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 2)))
         (assert (= e (seq.++ (seq.unit 1) (seq.unit 2))))
         (check-sat)",
    );
    assert_eq!(result, "sat", "extract([1,2,3],0,2) = [1,2] is correct");
}

/// 3-element extract: extract([1,2,3], 0, 3) != [1,2,99] is UNSAT.
#[test]
fn test_seq_extract_three_elem_wrong_unsat_6040() {
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 3)))
         (assert (= e (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 99)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],0,3) != [1,2,99]");
}

/// Middle extraction: extract([1,2,3], 1, 2) != [2,99] is UNSAT.
#[test]
fn test_seq_extract_middle_multi_elem_unsat_6040() {
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 1 2)))
         (assert (= e (seq.++ (seq.unit 2) (seq.unit 99))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],1,2) != [2,99]");
}

/// Positive middle extraction: extract([1,2,3], 1, 2) = [2,3] should be SAT.
#[test]
fn test_seq_extract_middle_multi_elem_sat_6040() {
    let result = common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 1 2)))
         (assert (= e (seq.++ (seq.unit 2) (seq.unit 3))))
         (check-sat)",
    );
    assert_eq!(result, "sat", "extract([1,2,3],1,2) = [2,3] is correct");
}
