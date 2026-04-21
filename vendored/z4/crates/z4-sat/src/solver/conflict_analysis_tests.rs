// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for 1UIP conflict analysis and clause learning.

use super::*;
use crate::literal::Variable;
use crate::ClauseTrace;
use crate::ProofOutput;

/// Add `n` original clauses to satisfy ProofManager's embedded ForwardChecker
/// and LRAT hint validation. Uses binary clauses on variables `base..base+n`
/// so they don't interfere with test variables 0..base. Also adds `[+x0]`
/// as the first clause to make any derived clause containing +x0 trivially
/// RUP-valid (the checker propagates x0=true, so +x0 is satisfied).
fn add_padding_original_clauses(solver: &mut Solver, n: usize) {
    // First clause: [+x0] — its negation under RUP causes conflict.
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    // Remaining clauses: [+x0, +x_i] — each becomes a unit clause under
    // the RUP assumption (x0=false), propagating a fresh variable. This
    // makes all padding clauses valid LRAT hints (unit or conflict),
    // satisfying the non-unit hint rejection check (#5236 Gap 3).
    for i in 1..n {
        let v = (i * 2) as u32;
        solver.add_clause(vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(v)),
        ]);
    }
}

#[test]
fn test_add_learned_clause_reorders_second_literal_to_highest_level() {
    let mut solver: Solver = Solver::new(4);
    solver.var_data[0].level = 7; // UIP level (ignored for reorder)
    solver.var_data[1].level = 1;
    solver.var_data[2].level = 5; // highest non-UIP level
    solver.var_data[3].level = 3;

    let uip = Literal::positive(Variable(0));
    let low = Literal::positive(Variable(1));
    let high = Literal::positive(Variable(2));
    let mid = Literal::positive(Variable(3));

    let learned = solver.add_learned_clause(vec![uip, low, high, mid], 3, &[]);
    let idx = learned.0 as usize;

    assert_eq!(solver.arena.literal(idx, 0), uip);
    assert_eq!(solver.arena.literal(idx, 1), high);
}

#[test]
fn test_add_learned_clause_keeps_binary_order() {
    let mut solver: Solver = Solver::new(2);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let first = Literal::positive(Variable(0));
    let second = Literal::negative(Variable(1));
    let learned = solver.add_learned_clause(vec![first, second], 1, &[]);
    let idx = learned.0 as usize;

    assert_eq!(solver.arena.literal(idx, 0), first);
    assert_eq!(solver.arena.literal(idx, 1), second);
}

#[test]
fn test_add_learned_clause_reverses_lrat_hint_order() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    // Add 8 original clauses so LRAT hint IDs 1-8 are registered
    add_padding_original_clauses(&mut solver, 8);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    // Include clause 1 ([+x0]) in hints — required for RUP derivation
    // of [+x0, -x1]: negating gives x0=false, then hint 1 ({+x0}) is
    // falsified → contradiction.
    let _ = solver.add_learned_clause(vec![a, b], 1, &[1, 6, 3, 2, 8, 7]);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");

    // Derived clause ID = 9 (8 originals + 1), hints reversed
    assert_eq!(proof_text, "9 1 -2 0 7 8 2 3 6 1 0\n");
}

#[test]
fn test_add_conflict_learned_clause_returns_owned_buffers_to_analyzer() {
    let mut solver: Solver = Solver::new(4);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    solver
        .conflict
        .set_asserting_literal(Literal::positive(Variable(0)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));
    solver.conflict.add_to_chain(5);
    solver.conflict.add_to_chain(9);

    let result = solver.conflict.get_result(1, 1);
    let learned_cap = result.learned_clause.capacity();
    let chain_cap = result.resolution_chain.capacity();

    let learned_ref =
        solver.add_conflict_learned_clause(result.learned_clause, 1, result.resolution_chain);

    assert_eq!(
        solver.arena.literal(learned_ref.0 as usize, 0),
        Literal::positive(Variable(0))
    );
    assert_eq!(solver.conflict.learned_capacity(), learned_cap);
    assert_eq!(solver.conflict.resolution_chain_capacity(), chain_cap);
}

#[test]
fn test_bump_analyzed_variables_uses_persistent_sort_buf() {
    let mut solver: Solver = Solver::new(4);
    solver.stable_mode = false;
    solver.bump_sort_buf = Vec::with_capacity(8);
    solver.conflict.mark_seen(0, &mut solver.var_data);
    solver.conflict.mark_seen(2, &mut solver.var_data);
    solver.conflict.mark_seen(1, &mut solver.var_data);

    solver.bump_analyzed_variables();

    assert_eq!(solver.bump_sort_buf, vec![2, 1, 0]);
    assert!(solver.bump_sort_buf.capacity() >= 8);
}

/// Verify lrat_reverse_hints reverses and filters zeros.
/// Dedup is NOT done here — it's handled at construction time by
/// `ConflictAnalyzer::add_to_chain` (#5248). Post-hoc dedup here would
/// break multi-stage ordering (#5194).
#[test]
fn test_lrat_reverse_dedup_handles_large_chains() {
    let mut hints: Vec<u64> = Vec::new();
    for i in 1..=100 {
        hints.push(i);
        hints.push(i); // duplicate — preserved by lrat_reverse_hints
    }
    for i in (1..=50).rev() {
        hints.push(i);
    }

    let result = Solver::lrat_reverse_hints(&hints);

    // All 250 non-zero entries preserved (no dedup at this level), zeros filtered.
    assert_eq!(result.len(), 250, "should preserve all non-zero hints");
    assert!(!result.contains(&0), "sentinel 0 must not appear in hints");
    assert_eq!(result[0], 1, "first hint after reversal should be 1");
}

/// Verify LRAT chain helpers and reusable work arrays exist and are sized
/// correctly. The LRAT bits (LRAT_A, LRAT_B in minimize_flags, plus lrat_to_clear)
/// replaced per-conflict vec![false; num_vars] allocations (#4579).
#[test]
fn test_lrat_chain_functions_exist_and_are_callable() {
    // Verify the LRAT chain helper functions compile and don't panic on empty input.
    // This is a minimal smoke test; correctness is validated by LRAT proof checking.
    let solver: Solver = Solver::new(10);

    // lrat_reverse_hints: static method, no allocation concern
    let empty_result = Solver::lrat_reverse_hints(&[]);
    assert!(empty_result.is_empty());

    // Verify the solver has packed minimize_flags array (#5089)
    assert_eq!(solver.min.minimize_flags.len(), 10);

    // Verify LRAT bits are packed into minimize_flags (#5089, #4579)
    assert_eq!(solver.min.minimize_flags.len(), 10);
    assert!(solver.min.lrat_to_clear.is_empty());
}

#[test]
fn test_add_learned_clause_deduplicates_reversed_lrat_hints() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    // lrat_reverse_hints reverses and filters zeros.
    // ProofManager::emit_add deduplicates hint IDs at the output boundary
    // (#5248) so external LRAT checkers do not reject duplicate hints.
    let _ = solver.add_learned_clause(vec![a, b], 1, &[1, 6, 3, 6, 2, 3, 8, 7, 8]);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");

    // Derived clause ID = 9 (8 originals + 1), reversed and deduped:
    // Input [1,6,3,6,2,3,8,7,8] → reverse [8,7,8,3,2,6,3,6,1]
    // → dedup (first-occurrence order) [8,7,3,2,6,1]
    assert_eq!(proof_text, "9 1 -2 0 8 7 3 2 6 1 0\n");
}

#[test]
fn test_add_learned_clause_truncates_trail_to_recent_suffix() {
    const TRAIL_CAPACITY: usize = 1024;
    const RETAINED_AFTER_TRUNCATION: usize = TRAIL_CAPACITY / 2;
    const EAGER_SUBSUME_LIMIT: usize = 20;
    const TOTAL_LEARNED: usize = TRAIL_CAPACITY + 1;

    let mut solver: Solver = Solver::new(TOTAL_LEARNED + 1);
    let uip = Literal::positive(Variable(0));
    let mut learned_offsets = Vec::with_capacity(TOTAL_LEARNED);

    for i in 0..TOTAL_LEARNED {
        let other = Literal::positive(Variable((i + 1) as u32));
        let learned = solver.add_learned_clause(vec![uip, other], 1, &[]);
        learned_offsets.push(learned.0 as usize);
    }

    let retained_start = TOTAL_LEARNED - RETAINED_AFTER_TRUNCATION;
    assert_eq!(
        solver.cold.learned_clause_trail.len(),
        RETAINED_AFTER_TRUNCATION
    );
    assert_eq!(
        solver.cold.learned_clause_trail.as_slice(),
        &learned_offsets[retained_start..],
        "trail truncation should keep the newest learned clauses"
    );
    assert_eq!(
        &solver.cold.learned_clause_trail
            [solver.cold.learned_clause_trail.len() - EAGER_SUBSUME_LIMIT..],
        &learned_offsets[TOTAL_LEARNED - EAGER_SUBSUME_LIMIT..],
        "truncation must preserve the full eager-subsumption window"
    );
}

/// Verify that clause trace receives raw (non-reversed) resolution hints.
///
/// LRAT proof output receives reversed+deduped hints (for sequential RUP
/// checking), but the clause trace receives raw hints in analysis order.
/// The SatProofManager consumes the raw order and resolves iteratively,
/// finding pivots dynamically. This test documents that the two outputs
/// receive DIFFERENT hint orderings from the same add_learned_clause call.
#[test]
fn test_add_learned_clause_trace_receives_raw_hints() {
    use crate::ClauseTrace;

    // 10 original clauses so hints [1..8] are in valid range [1, 11)
    let proof = ProofOutput::lrat_text(Vec::new(), 10);
    let mut solver: Solver = Solver::with_proof_output(24, proof);
    // Add 10 original clauses to register IDs 1-10 in ProofManager
    add_padding_original_clauses(&mut solver, 10);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    // Enable clause trace
    solver.cold.clause_trace = Some(ClauseTrace::new());

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    // Include clause 1 ([+x0]) — required for RUP derivation of [+x0, -x1]
    let chain = &[1, 6, 3, 2, 8, 7];
    let clause_ref = solver.add_learned_clause(vec![a, b], 1, chain);

    // Verify LRAT gets reversed order (clause ID 11 = 10 original + 1)
    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert_eq!(proof_text, "11 1 -2 0 7 8 2 3 6 1 0\n");

    // Verify clause trace gets raw (non-reversed) order
    let trace = solver.clause_trace().expect("clause trace should exist");
    let clause_id = solver.clause_id(clause_ref);
    let entry = trace
        .entries()
        .iter()
        .find(|e| e.id == clause_id)
        .expect("trace should contain the learned clause");
    assert_eq!(
        entry.resolution_hints,
        vec![1, 6, 3, 2, 8, 7],
        "clause trace should receive raw (non-reversed) hints"
    );
}

/// Verify that clause IDs are always assigned even without LRAT, but
/// clause trace entries are only recorded when lrat_enabled is true.
///
/// After #8069 (Phase 2a), clause IDs are assigned unconditionally.
/// However, when `lrat_enabled` is false, `add_clause_db_checked` still
/// skips `clause_trace.add_clause_with_hints()` — callers that depend
/// on the trace must enable LRAT.
#[test]
fn test_add_learned_clause_has_id_but_no_trace_without_lrat() {
    use crate::ClauseTrace;

    // No proof output -> lrat_enabled is false, but clause_ids ARE populated
    let mut solver: Solver = Solver::new(2);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    solver.cold.clause_trace = Some(ClauseTrace::new());

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let clause_ref = solver.add_learned_clause(vec![a, b], 1, &[6, 3, 2]);

    // Clause ID is always assigned now (#8069: Phase 2a)
    let id = solver.clause_id(clause_ref);
    assert_ne!(id, 0, "clause IDs are always assigned after #8069");

    // When LRAT is disabled, add_clause_db_checked does not record trace
    // entries at all — the trace must be empty.
    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    assert!(
        trace.is_empty(),
        "clause trace must have no entries when LRAT is disabled (was: {} entries)",
        trace.len(),
    );
}

#[test]
fn test_append_lrat_unit_chain_uses_unit_proof_id_for_dynamic_var() {
    let mut solver: Solver = Solver::new(1);
    solver.enable_lrat(); // enables LRAT hint construction (unit_proof_id always allocated since #8069)
    let fresh = solver.new_var();
    let fresh_idx = fresh.index();
    let fresh_lit = Literal::positive(fresh);

    solver.var_data[fresh_idx].level = 0;
    solver.var_data[fresh_idx].reason = NO_REASON;
    solver.trail = vec![fresh_lit];
    solver.unit_proof_id[fresh_idx] = 77;

    solver.append_lrat_unit_chain(&[fresh_idx], &det_hash_set_new());
    // get_result requires asserting_literal to be set (debug invariant).
    solver.conflict.set_asserting_literal(fresh_lit);
    let result = solver.conflict.get_result(0, 0);

    assert_eq!(result.resolution_chain, vec![77]);
}

/// Verify that `append_lrat_unit_chain` collects proof IDs via the
/// `level0_proof_id` fallback when ClearLevel0 has cleared reason[v].
///
/// Scenario: two level-0 variables a and b. Variable b's reason was
/// cleared by ClearLevel0 (BVE deleted the clause) but its proof ID
/// is preserved in `level0_proof_id[b]`. Variable a's reason clause
/// contains b, so Phase 1 BFS reaches b and hits the `continue` at
/// line 1079 (no clause to traverse). Phase 2 must still collect b's
/// proof ID via the 3-tier fallback (#4617).
#[test]
fn test_append_lrat_unit_chain_clearlevel0_uses_level0_proof_id() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    // c0 = {a, b}: binary clause, a's reason clause (contains both a and b)
    solver.add_clause(vec![a, b]);
    let c0_ref = ClauseRef(0);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "c0 must have a non-zero LRAT ID");

    // c1 = {b}: visible proof ID preserved across ClearLevel0.
    let b_unit_idx = solver.add_clause_db(&[b], false);
    let b_unit_ref = ClauseRef(b_unit_idx as u32);
    let b_unit_id = solver.clause_id(b_unit_ref);
    assert_ne!(b_unit_id, 0, "b unit must have a non-zero LRAT ID");

    // Set up trail: b propagated first, then a
    solver.trail = vec![b, a];
    solver.trail_lim = vec![]; // all at level 0 (no decisions)
    solver.var_data[0].level = 0;
    solver.var_data[1].level = 0;

    // a's reason is c0 (a normal reason clause)
    solver.var_data[0].reason = c0_ref.0;

    // b's reason cleared by ClearLevel0: reason=None, level0_proof_id set
    solver.var_data[1].reason = NO_REASON;
    solver.unit_proof_id[1] = 0; // ensure unit_proof_id doesn't mask level0
    solver.cold.level0_proof_id[1] = b_unit_id; // ClearLevel0 saved this visible ID

    // Seed with var 0 (a). Phase 1 BFS reaches var 1 (b) through c0,
    // but b has reason=None → ClearLevel0 `continue` path.
    solver.materialize_level0_unit_proofs();
    solver.append_lrat_unit_chain(&[0], &det_hash_set_new());

    solver.conflict.set_asserting_literal(a);
    let result = solver.conflict.get_result(0, 0);

    // In LRAT mode, level0_var_proof_id skips multi-literal reason clause
    // IDs (#7108 — they cause RUP failures). Materializing level-0 unit
    // proofs first derives a visible unit proof for var 0 (a) from c0 and
    // b's preserved ClearLevel0 proof ID.
    //
    // Var 1 (b) has reason=None (ClearLevel0) but level0_proof_id[1]=b_unit_id,
    // which is picked up by the 3-tier fallback.
    //
    // Trail order is [b, a] (indices [1, 0]), reversed scan yields a first.
    // So the chain is [derived_visible_proof_id_for_a, 42].
    assert_eq!(
        result.resolution_chain.len(),
        2,
        "chain must include proof IDs for both var 0 (a) and var 1 (b)"
    );
    assert!(
        result.resolution_chain.contains(&b_unit_id),
        "chain must include b's ClearLevel0 proof ID"
    );
}

#[test]
fn test_compute_lrat_chain_for_removed_literals_uses_unit_proof_id_for_level0_reason() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let uip = Literal::positive(Variable(0));
    let removed = Literal::positive(Variable(1));
    let level0 = Literal::positive(Variable(2));

    // c0 = {level0}: explicit unit proof for the level-0 antecedent.
    let c0_idx = solver.add_clause_db(&[level0], false);
    let c0_ref = ClauseRef(c0_idx as u32);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "level-0 unit clause must have a proof ID");

    // c1 = {removed, level0}: removed literal's reason clause.
    let c1_idx = solver.add_clause_db(&[removed, level0], false);
    let c1_ref = ClauseRef(c1_idx as u32);
    let c1_id = solver.clause_id(c1_ref);
    assert_ne!(
        c1_id, 0,
        "removed literal reason clause must have a proof ID"
    );

    // c2 = {uip, removed}: original learned clause before minimize removes `removed`.
    let c2_idx = solver.add_clause_db(&[uip, removed], false);
    let c2_ref = ClauseRef(c2_idx as u32);
    let c2_id = solver.clause_id(c2_ref);
    assert_ne!(c2_id, 0, "original learned clause must have a proof ID");

    solver.conflict.set_asserting_literal(uip);
    solver.var_data[removed.variable().index()].level = 1;
    solver.var_data[removed.variable().index()].reason = c1_ref.0;
    solver.var_data[level0.variable().index()].level = 0;
    solver.var_data[level0.variable().index()].reason = c0_ref.0;
    solver.unit_proof_id[level0.variable().index()] = c0_id;

    // Final learned clause keeps only the UIP; `removed` was eliminated by minimize.
    let minimize_level0 = solver.compute_lrat_chain_for_removed_literals(&[uip, removed]);

    let result = solver.conflict.get_result(0, 0);

    // After #7108 fix: level-0 units are routed to the returned Vec, not
    // the resolution chain. The chain should only contain non-level-0
    // reason clause IDs (c1_id for the removed literal's reason).
    assert_eq!(
        result.resolution_chain,
        vec![c1_id],
        "removed-literal minimize chain must contain only non-level-0 reason IDs"
    );
    assert_eq!(
        minimize_level0,
        vec![level0.variable().index()],
        "level-0 variable from minimize DFS must be returned for unit chain routing"
    );

    // Sanity: the removed literal's original clause is not part of the minimize chain.
    assert!(
        !result.resolution_chain.contains(&c2_id),
        "minimize chain should only contain the removed literal's reason graph"
    );
}

#[test]
fn test_level0_var_proof_id_uses_unit_reason_clause_in_lrat_mode() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);

    let unit = Literal::positive(Variable(0));
    let unit_idx = solver.add_clause_db(&[unit], false);
    let unit_ref = ClauseRef(unit_idx as u32);
    let unit_id = solver.clause_id(unit_ref);
    assert_ne!(unit_id, 0, "unit reason clause must have a proof ID");

    solver.var_data[unit.variable().index()].level = 0;
    solver.var_data[unit.variable().index()].reason = unit_ref.0;
    solver.unit_proof_id[unit.variable().index()] = 0;
    solver.cold.level0_proof_id[unit.variable().index()] = 0;

    assert_eq!(
        solver.level0_var_proof_id(unit.variable().index()),
        Some(unit_id),
        "LRAT mode must accept a unit reason clause when no materialized unit proof exists yet"
    );
}

#[test]
fn test_compute_lrat_chain_for_removed_literals_materializes_nested_level0_units() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(4, proof);

    let uip = Literal::positive(Variable(0));
    let removed = Literal::positive(Variable(1));
    let mid = Literal::positive(Variable(2));
    let leaf = Literal::positive(Variable(3));

    // c0 = {leaf}: explicit unit proof for the deepest level-0 antecedent.
    let c0_idx = solver.add_clause_db(&[leaf], false);
    let c0_ref = ClauseRef(c0_idx as u32);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "deepest level-0 unit must have a proof ID");

    // c1 = {mid, ¬leaf}: leaf=true forces mid=true at level 0.
    let c1_idx = solver.add_clause_db(&[mid, leaf.negated()], false);
    let c1_ref = ClauseRef(c1_idx as u32);
    let c1_id = solver.clause_id(c1_ref);
    assert_ne!(
        c1_id, 0,
        "nested level-0 reason clause must have a proof ID"
    );

    // c2 = {removed, ¬mid}: mid=true forces removed=true.
    let c2_idx = solver.add_clause_db(&[removed, mid.negated()], false);
    let c2_ref = ClauseRef(c2_idx as u32);
    let c2_id = solver.clause_id(c2_ref);
    assert_ne!(
        c2_id, 0,
        "removed literal reason clause must have a proof ID"
    );

    solver.conflict.set_asserting_literal(uip);
    solver.trail = vec![leaf, mid];
    solver.trail_lim = vec![];
    solver.var_data[leaf.variable().index()].level = 0;
    solver.var_data[leaf.variable().index()].trail_pos = 0;
    solver.var_data[leaf.variable().index()].reason = c0_ref.0;
    solver.var_data[mid.variable().index()].level = 0;
    solver.var_data[mid.variable().index()].trail_pos = 1;
    solver.var_data[mid.variable().index()].reason = c1_ref.0;
    solver.var_data[removed.variable().index()].level = 1;
    solver.var_data[removed.variable().index()].reason = c2_ref.0;
    solver.unit_proof_id[leaf.variable().index()] = c0_id;

    // Final learned clause keeps only the UIP; `removed` was eliminated by minimize.
    let minimize_level0 = solver.compute_lrat_chain_for_removed_literals(&[uip, removed]);

    let mid_unit_id = solver.cold.level0_proof_id[mid.variable().index()];
    assert_ne!(
        mid_unit_id, 0,
        "nested level-0 antecedent must be materialized as a derived unit proof"
    );
    assert_ne!(
        mid_unit_id, c1_id,
        "minimize chain must not reuse the raw multi-literal level-0 reason clause"
    );

    let result = solver.conflict.get_result(0, 0);
    // After #7108 fix: level-0 units are routed to the returned Vec, not
    // the resolution chain. Only the non-level-0 reason (c2_id) remains.
    assert_eq!(
        result.resolution_chain,
        vec![c2_id],
        "removed-literal minimize chain must contain only non-level-0 reason IDs"
    );
    assert_eq!(
        minimize_level0,
        vec![mid.variable().index()],
        "nested level-0 variable from minimize DFS must be returned for unit chain routing"
    );
}

#[test]
fn test_materialize_level0_unit_proofs_rederives_hidden_trusted_unit_as_visible() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let support = Literal::positive(Variable(1));
    let target = Literal::positive(Variable(2));

    let support_idx = solver.add_clause_db(&[support], false);
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    assert_ne!(support_id, 0, "support unit must have a proof ID");

    let reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);
    let reason_id = solver.clause_id(reason_ref);
    assert_ne!(reason_id, 0, "target reason must have a proof ID");

    solver.trail = vec![support, target];
    solver.trail_lim = vec![];

    solver.var_data[support.variable().index()].level = 0;
    solver.var_data[support.variable().index()].trail_pos = 0;
    solver.var_data[support.variable().index()].reason = support_ref.0;

    solver.var_data[target.variable().index()].level = 0;
    solver.var_data[target.variable().index()].trail_pos = 1;
    solver.var_data[target.variable().index()].reason = reason_ref.0;

    solver.unit_proof_id[support.variable().index()] = support_id;

    let hidden_id = solver.proof_emit_unit(target, &[], ProofAddKind::TrustedTransform);
    assert_ne!(
        hidden_id, 0,
        "trusted-transform unit must reserve an LRAT ID"
    );
    assert!(
        !solver.lrat_hint_id_visible(hidden_id),
        "trusted-transform unit must stay hidden from the external LRAT file"
    );
    solver.unit_proof_id[target.variable().index()] = hidden_id;

    solver.materialize_level0_unit_proofs();

    let visible_id = solver.cold.level0_proof_id[target.variable().index()];
    assert_ne!(
        visible_id, 0,
        "target must be rederived as a visible LRAT unit"
    );
    assert_ne!(
        visible_id, hidden_id,
        "materialization must not reuse the hidden trusted-transform proof ID"
    );
    assert!(
        solver.lrat_hint_id_visible(visible_id),
        "materialized level-0 unit must be eligible for external LRAT hints"
    );
    assert_eq!(
        solver.level0_var_proof_id(target.variable().index()),
        Some(visible_id),
        "LRAT hint lookup must prefer the visible rederived unit"
    );
}

#[test]
fn test_collect_empty_clause_hints_for_unit_contradiction_skips_hidden_unit_id() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);

    let existing = Literal::positive(Variable(0));
    let existing_idx = solver.add_clause_db(&[existing], false);
    let existing_ref = ClauseRef(existing_idx as u32);
    let existing_id = solver.clause_id(existing_ref);
    assert_ne!(existing_id, 0, "existing unit must have a proof ID");

    solver.trail = vec![existing];
    solver.trail_lim = vec![];
    solver.var_data[existing.variable().index()].level = 0;
    solver.var_data[existing.variable().index()].trail_pos = 0;
    solver.var_data[existing.variable().index()].reason = existing_ref.0;
    solver.unit_proof_id[existing.variable().index()] = existing_id;

    let hidden_id = solver.proof_emit_unit(existing.negated(), &[], ProofAddKind::TrustedTransform);
    assert_ne!(
        hidden_id, 0,
        "trusted-transform unit must reserve an LRAT ID"
    );
    assert!(
        !solver.lrat_hint_id_visible(hidden_id),
        "trusted-transform unit must stay hidden from external LRAT output"
    );

    let hints = solver
        .collect_empty_clause_hints_for_unit_contradiction(hidden_id, existing.variable().index());
    assert!(
        hints.is_empty(),
        "hidden contradictory unit must not produce an external LRAT empty-clause hint chain"
    );
}

#[test]
fn test_compute_lrat_chain_for_removed_literals_falls_back_to_raw_level0_reason() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(5, proof);

    let uip = Literal::positive(Variable(0));
    let removed = Literal::positive(Variable(1));
    let level0_mid = Literal::positive(Variable(2));
    let leaf_a = Literal::positive(Variable(3));
    let leaf_b = Literal::positive(Variable(4));

    // c0 = {level0_mid, ¬leaf_a, ¬leaf_b}: root-level implication whose own
    // unit proof cannot be materialized because its antecedents have no proof IDs.
    let c0_idx = solver.add_clause_db(&[level0_mid, leaf_a.negated(), leaf_b.negated()], false);
    let c0_ref = ClauseRef(c0_idx as u32);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "level-0 fallback reason must have a proof ID");

    // c1 = {removed, ¬level0_mid}: removed literal depends on that level-0 node.
    let c1_idx = solver.add_clause_db(&[removed, level0_mid.negated()], false);
    let c1_ref = ClauseRef(c1_idx as u32);
    let c1_id = solver.clause_id(c1_ref);
    assert_ne!(c1_id, 0, "removed literal reason must have a proof ID");

    solver.conflict.set_asserting_literal(uip);
    solver.trail = vec![leaf_a, leaf_b, level0_mid];
    solver.trail_lim = vec![];

    solver.var_data[level0_mid.variable().index()].level = 0;
    solver.var_data[level0_mid.variable().index()].trail_pos = 2;
    solver.var_data[level0_mid.variable().index()].reason = c0_ref.0;

    solver.var_data[leaf_a.variable().index()].level = 0;
    solver.var_data[leaf_a.variable().index()].trail_pos = 0;
    solver.var_data[leaf_a.variable().index()].reason = NO_REASON;

    solver.var_data[leaf_b.variable().index()].level = 0;
    solver.var_data[leaf_b.variable().index()].trail_pos = 1;
    solver.var_data[leaf_b.variable().index()].reason = NO_REASON;

    solver.var_data[removed.variable().index()].level = 1;
    solver.var_data[removed.variable().index()].reason = c1_ref.0;

    let minimize_level0 = solver.compute_lrat_chain_for_removed_literals(&[uip, removed]);
    let result = solver.conflict.get_result(0, 0);

    assert!(
        minimize_level0.is_empty(),
        "fallback path must keep the raw level-0 reason in mini_chain when no unit proof exists"
    );
    assert_eq!(
        result.resolution_chain,
        vec![c1_id, c0_id],
        "removed-literal minimize chain must retain the raw level-0 reason when unit proof materialization is unavailable"
    );
}

fn setup_level0_conflict_chain_fixture() -> (Solver, ClauseRef) {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let c = Literal::positive(Variable(1));
    let idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), c], false);
    let idx_c3 = solver.add_clause_db(&[a.negated(), c.negated()], false);
    let ref_c1 = ClauseRef(idx_c1 as u32);
    let ref_c3 = ClauseRef(idx_c3 as u32);

    solver.trail = vec![a, c];
    solver.var_data[0].reason = ref_c1.0;
    solver.var_data[1].reason = idx_c2 as u32;
    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;
    (solver, ref_c3)
}

/// Verify that record_level0_conflict_chain populates resolution hints in clause trace.
///
/// At decision level 0, 1UIP conflict analysis cannot run (it assumes
/// decision_level > 0). Instead, record_level0_conflict_chain walks the trail
/// backward and collects all reason clause IDs. This test verifies that:
/// 1. The empty-clause trace entry gets the correct resolution chain
/// 2. set_resolution_hints succeeds (the debug_assert contract is satisfied)
#[test]
fn test_record_level0_conflict_chain_sets_resolution_hints() {
    // Scenario:
    // c1={a} propagates a=true, c2={¬a,c} propagates c=true, c3={¬a,¬c}
    // conflicts at level 0. Expected chain: c3(3) -> c2(2) -> c1(1).
    let (mut solver, ref_c3) = setup_level0_conflict_chain_fixture();
    solver.record_level0_conflict_chain(ref_c3);

    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    assert_eq!(trace.len(), 4);
    let empty_entry = trace.entries().last().expect("has entries");
    assert!(
        empty_entry.clause.is_empty(),
        "level-0 chain stores empty clause"
    );
    assert!(!empty_entry.is_original, "level-0 chain clause is learned");
    assert_eq!(
        empty_entry.resolution_hints,
        vec![3, 2, 1],
        "resolution chain: conflict + reason IDs in trail-reverse order"
    );
}

/// Regression test for #4617: ClearLevel0 must preserve LRAT chain provenance.
///
/// When a level-0 reason clause is deleted via ReasonPolicy::ClearLevel0,
/// reason[vi] is set to None. Without the level0_proof_id fallback, the
/// chain collector silently skips the variable and produces an incomplete
/// LRAT derivation chain.
#[test]
fn test_level0_conflict_chain_after_clearlevel0_includes_saved_proof_id() {
    use crate::ClauseTrace;

    // 3 variables: a=0, b=1, c=2; LRAT enabled for clause IDs.
    //
    // Scenario:
    //   c1: {a}         -> unit, propagates a=true (reason for var 0). ID=1
    //   c2: {¬a, b}     -> binary, ¬a=false → b=true (reason for var 1). ID=2
    //   c3: {¬b, c}     -> binary, ¬b=false → c=true (reason for var 2). ID=3
    //
    // After propagation, delete c2 via ClearLevel0:
    //   reason[1] = None, but level0_proof_id[1] = 2 (saved by fix).
    //
    // Then add conflict clause:
    //   c4: {¬a, ¬c}    -> conflict: ¬a=false, ¬c=false. ID=4
    //
    // Chain should include c2's ID (2) via the fallback.
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    let _idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), b], false);
    let _idx_c3 = solver.add_clause_db(&[b.negated(), c], false);
    let idx_c4 = solver.add_clause_db(&[a.negated(), c.negated()], false);

    let ref_c2 = ClauseRef(idx_c2 as u32);
    let ref_c4 = ClauseRef(idx_c4 as u32);

    // Simulate level-0 propagation: a, b, c
    solver.trail = vec![a, b, c];
    solver.var_data[0].reason = _idx_c1 as u32;
    solver.var_data[1].reason = ref_c2.0;
    solver.var_data[2].reason = _idx_c3 as u32;
    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.vals[b.index()] = 1;
    solver.vals[b.negated().index()] = -1;
    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;

    // Simulate ClearLevel0: the real delete_clause_checked calls
    // materialize_level0_unit_proofs() first, then emits a derived unit proof
    // for the variable whose reason is being cleared, then sets the reason to
    // NO_REASON. Simulate this sequence correctly (#7108).
    solver.materialize_level0_unit_proofs();
    // After materialization, var 1 should have a unit proof ID.
    let b_proof_id = solver.unit_proof_id_of_var_index(1).unwrap_or(0);
    assert_ne!(
        b_proof_id, 0,
        "var 1 (b) should have a materialized unit proof ID"
    );
    // Now clear the reason (simulating ClearLevel0 after materialization).
    solver.var_data[1].reason = NO_REASON;

    // Now trigger level-0 conflict chain collection.
    solver.record_level0_conflict_chain(ref_c4);

    // Verify: the chain includes the proof ID for var 1 (b). In the clause
    // trace, this is recorded via collect_resolution_chain which uses the
    // resolution chain format. The key requirement is that the empty clause
    // is properly derived.
    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    let empty_entry = trace.entries().last().expect("has entries");
    assert!(
        empty_entry.clause.is_empty(),
        "level-0 chain stores empty clause"
    );
    // The clause trace should contain a proof ID for var 1 (b) — either the
    // original c2_id (from collect_resolution_chain's level0_proof_id fallback)
    // or the materialized unit proof ID.
    let c2_id = solver.clause_id(ref_c2);
    let has_b_proof = empty_entry.resolution_hints.contains(&c2_id)
        || empty_entry.resolution_hints.contains(&b_proof_id);
    assert!(
        has_b_proof,
        "chain must include proof for var 1 (b): c2_id={c2_id}, b_proof_id={b_proof_id}, \
         but got: {:?}",
        empty_entry.resolution_hints,
    );
}

#[test]
fn test_record_level0_conflict_chain_uses_unit_proof_id_when_reason_absent() {
    use crate::ClauseTrace;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let c = Literal::positive(Variable(1));

    let idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), c], false);
    let idx_c3 = solver.add_clause_db(&[a.negated(), c.negated()], false);
    let c1_ref = ClauseRef(idx_c1 as u32);
    let c3_ref = ClauseRef(idx_c3 as u32);

    solver.trail = vec![a, c];
    solver.var_data[0].reason = NO_REASON;
    solver.var_data[1].reason = idx_c2 as u32;
    solver.unit_proof_id[0] = solver.clause_id(c1_ref);
    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;

    solver.record_level0_conflict_chain(c3_ref);

    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    let empty_entry = trace.entries().last().expect("empty clause entry");
    assert_eq!(
        empty_entry.resolution_hints,
        vec![3, 2, 1],
        "level-0 chain should include unit provenance when reason is absent"
    );
}

/// Regression guard: collect_resolution_chain reuses persistent work arrays
/// and clears only touched entries after each call.
///
/// References: #4172 (sat-debuggability tracking), CaDiCaL uses
/// reusable stamp arrays (reference/cadical/src/analyze.cpp).
#[test]
fn test_collect_resolution_chain_reuses_persistent_marks() {
    // Setup: 3 variables, LRAT enabled, level-0 propagation with conflict.
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    let idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), b], false);
    let _idx_c3 = solver.add_clause_db(&[b.negated(), c], false);

    solver.trail = vec![a, b, c];
    solver.var_data[0].reason = idx_c1 as u32;
    solver.var_data[1].reason = idx_c2 as u32;
    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.vals[b.index()] = 1;
    solver.vals[b.negated().index()] = -1;
    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;

    assert!(solver.min.lrat_to_clear.is_empty(), "worklist starts empty");
    assert!(
        solver.min.minimize_flags.iter().all(|&f| f & LRAT_A == 0),
        "LRAT_A bits start clear"
    );

    // collect_resolution_chain must reuse persistent marks and clean up.
    let chain =
        solver.collect_resolution_chain(ClauseRef(idx_c2 as u32), None, &det_hash_set_new());
    assert!(!chain.is_empty(), "chain should contain reason clause IDs");
    assert_eq!(
        solver.min.minimize_flags.len(),
        3,
        "packed flags array is sized by num_vars"
    );
    assert!(
        solver.min.lrat_to_clear.is_empty(),
        "sparse cleanup list must be empty after collection"
    );
    assert!(
        solver.min.minimize_flags.iter().all(|&f| f & LRAT_A == 0),
        "all touched LRAT_A marks must be cleared after collection"
    );
}

/// Verify lrat_reverse_hints reverses, filters zeros, and preserves
/// duplicates at scale. Dedup is at construction time (#5248), not here.
#[test]
fn test_lrat_hint_dedup_correctness_at_scale() {
    // Build: 500 entries + 200 duplicates + 2 zeros = 702 total
    let mut hints: Vec<u64> = Vec::new();
    for cycle in 0..5 {
        for i in 1..=100u64 {
            hints.push(i + cycle * 100);
        }
    }
    let dup = hints[..200].to_vec();
    hints.extend(dup);
    hints.push(0);
    hints.push(0);

    let result = Solver::lrat_reverse_hints(&hints);

    // All 700 non-zero entries preserved (no dedup at this level), zeros filtered
    assert_eq!(result.len(), 700, "700 non-zero hint entries expected");
    assert!(!result.contains(&0), "sentinel 0 must not appear");
    assert_eq!(
        result[0], 200,
        "first after reversal should be last dup entry"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_valid_level1_conflict() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![probe];
    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
    assert_eq!(
        hints,
        vec![1],
        "single conflict clause should produce one hint"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_uses_unit_proof_id_when_reason_absent() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let implied = Literal::positive(Variable(1));
    let unit_idx = solver.add_clause_db(&[implied], false);
    let conflict_idx = solver.add_clause_db(&[probe.negated(), implied.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![implied, probe];
    solver.var_data[implied.variable().index()].reason = NO_REASON;
    solver.unit_proof_id[implied.variable().index()] = solver.clause_id(ClauseRef(unit_idx as u32));
    solver.vals[implied.index()] = 1;
    solver.vals[implied.negated().index()] = -1;
    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
    // collect_resolution_chain builds [conflict_id, unit_id] = [2, 1],
    // then lrat_reverse_hints reverses to [1, 2].
    assert_eq!(
        hints,
        vec![1, 2],
        "probe hints after reversal: unit provenance then conflict clause"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_uses_cached_conflict_clause_id() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));

    // Real active conflict clause with a valid proof ID.
    let real_conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let real_conflict_id = solver.clause_id(ClauseRef(real_conflict_idx as u32));
    assert_ne!(
        real_conflict_id, 0,
        "test setup requires a real conflict ID"
    );

    // Simulate an internal/shortened conflict_ref without a direct proof ID.
    // In production this cache is populated by propagate_bcp::conflict_finalize
    // before LRAT hint collection runs.
    let internal_conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    solver.cold.clause_ids[internal_conflict_idx] = 0;
    let conflict_ref = ClauseRef(internal_conflict_idx as u32);
    solver.last_conflict_clause_ref = Some(conflict_ref);
    solver.last_conflict_clause_id = real_conflict_id;

    solver.trail = vec![probe];
    solver.trail_lim = vec![0];
    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
    assert_eq!(
        hints,
        vec![real_conflict_id],
        "probe hint collection must reuse the cached conflict clause ID \
         when conflict_ref has no direct mapping (#7262)"
    );
}

#[test]
fn test_reset_search_state_rebuild_preserves_original_clause_ids_in_lrat_mode() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    assert!(solver.add_clause(vec![x0, x1]));
    assert!(solver.add_clause(vec![x0.negated()]));

    let original_offsets: Vec<usize> = solver.arena.active_indices().collect();
    assert_eq!(original_offsets.len(), 2, "test setup requires 2 originals");

    let original_ids: Vec<u64> = original_offsets
        .iter()
        .map(|&idx| solver.clause_id(ClauseRef(idx as u32)))
        .collect();
    assert!(
        original_ids.iter().all(|&id| id != 0),
        "original clauses must start with LRAT IDs"
    );

    solver.arena.delete(original_offsets[0]);
    solver.reset_search_state();

    let rebuilt_offsets: Vec<usize> = solver.arena.active_indices().collect();
    assert_eq!(
        rebuilt_offsets.len(),
        2,
        "rebuild must restore both originals"
    );

    let rebuilt_ids: Vec<u64> = rebuilt_offsets
        .iter()
        .map(|&idx| solver.clause_id(ClauseRef(idx as u32)))
        .collect();
    assert_eq!(
        rebuilt_ids, original_ids,
        "reset_search_state rebuild must preserve original LRAT clause IDs"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_filters_forced_unit_rup_literal() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let forced_unit = Literal::negative(Variable(1));
    let implied = Literal::positive(Variable(2));

    // Reason clause contains forced_unit.negated() and would be satisfied
    // under the RUP assumption for the derived unit [forced_unit].
    let reason_idx = solver.add_clause_db(&[forced_unit.negated(), implied], false);
    let conflict_idx = solver.add_clause_db(&[probe.negated(), implied.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![probe, implied];
    solver.trail_lim = vec![0];
    solver.var_data[implied.variable().index()].reason = reason_idx as u32;
    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;
    solver.vals[implied.index()] = 1;
    solver.vals[implied.negated().index()] = -1;

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, Some(forced_unit));
    assert_eq!(
        hints,
        vec![2],
        "reason clause satisfied by forced-unit RUP assumption must be filtered"
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "must be called at decision level 1")]
fn test_collect_probe_conflict_lrat_hints_panics_when_level_not_one() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 0;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    let _ = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "probe literal")]
fn test_collect_probe_conflict_lrat_hints_panics_when_probe_unassigned() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    let _ = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "probe conflict clause")]
fn test_collect_probe_conflict_lrat_hints_panics_when_conflict_clause_not_false() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;

    let _ = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
}

/// Verify that CHB score updates are skipped in LegacyCoupled mode (#8091).
///
/// In the default single-thread configuration (EVSIDS+VMTF only), CHB
/// score updates on every conflict are pure overhead. The fix gates CHB
/// updates behind a check on `branch_selector_mode`.
#[test]
fn test_chb_scores_not_updated_in_legacy_coupled_mode() {
    use crate::mab::BranchSelectorMode;

    let mut solver: Solver = Solver::new(4);
    // Default should already be LegacyCoupled
    assert_eq!(
        solver.cold.branch_selector_mode,
        BranchSelectorMode::LegacyCoupled,
        "default branch_selector_mode must be LegacyCoupled"
    );

    // Mark some variables as analyzed (simulating a conflict)
    solver.conflict.mark_seen(0, &mut solver.var_data);
    solver.conflict.mark_seen(2, &mut solver.var_data);

    let alpha_before = solver.vsids.chb_alpha;
    let conflicts_before = solver.vsids.chb_conflicts;

    solver.bump_analyzed_variables();

    // CHB alpha and conflict counter must NOT have changed
    assert_eq!(
        solver.vsids.chb_alpha, alpha_before,
        "CHB alpha must not change in LegacyCoupled mode"
    );
    assert_eq!(
        solver.vsids.chb_conflicts, conflicts_before,
        "CHB conflict counter must not advance in LegacyCoupled mode"
    );
}

/// Verify that CHB score updates DO run when MAB UCB1 mode is active (#8091).
#[test]
fn test_chb_scores_updated_in_mab_ucb1_mode() {
    use crate::mab::BranchSelectorMode;

    let mut solver: Solver = Solver::new(4);
    solver.cold.branch_selector_mode = BranchSelectorMode::MabUcb1;

    solver.conflict.mark_seen(0, &mut solver.var_data);
    solver.conflict.mark_seen(2, &mut solver.var_data);

    let alpha_before = solver.vsids.chb_alpha;
    let conflicts_before = solver.vsids.chb_conflicts;

    solver.bump_analyzed_variables();

    // CHB alpha and conflict counter MUST have changed
    assert!(
        solver.vsids.chb_alpha < alpha_before,
        "CHB alpha must decay in MabUcb1 mode"
    );
    assert_eq!(
        solver.vsids.chb_conflicts,
        conflicts_before + 1,
        "CHB conflict counter must advance in MabUcb1 mode"
    );
}

/// Verify that set_branch_heuristic(Chb) still works for programmatic callers.
///
/// When a caller explicitly requests CHB, the mode switches to Fixed(Chb)
/// and CHB score updates must run.
#[test]
fn test_set_branch_heuristic_chb_enables_chb_updates() {
    use crate::mab::{BranchHeuristic, BranchSelectorMode};

    let mut solver: Solver = Solver::new(4);
    solver.set_branch_heuristic(BranchHeuristic::Chb);

    assert_eq!(
        solver.cold.branch_selector_mode,
        BranchSelectorMode::Fixed(BranchHeuristic::Chb),
        "set_branch_heuristic(Chb) must set Fixed(Chb) mode"
    );
    assert_eq!(
        solver.active_branch_heuristic,
        BranchHeuristic::Chb,
        "active heuristic must be Chb after set_branch_heuristic"
    );

    // Simulate a conflict and verify CHB updates run
    solver.conflict.mark_seen(1, &mut solver.var_data);
    let conflicts_before = solver.vsids.chb_conflicts;

    solver.bump_analyzed_variables();

    assert_eq!(
        solver.vsids.chb_conflicts,
        conflicts_before + 1,
        "CHB conflict counter must advance when Fixed(Chb) is active"
    );
}
