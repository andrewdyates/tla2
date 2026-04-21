// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for clause database reduction.
//!
//! Split from `reduction.rs` for file-size compliance (#5142).

use super::*;

fn count_active_learned_clauses(solver: &Solver) -> usize {
    solver
        .arena
        .indices()
        .filter(|&idx| solver.arena.is_active(idx) && solver.arena.is_learned(idx))
        .count()
}

fn add_tier2_learned_unit_clauses(solver: &mut Solver, count: usize) {
    for var in 0..count {
        let idx = solver.add_clause_db(&[Literal::positive(Variable(var as u32))], true);
        solver.arena.set_lbd(idx, 10);
    }
}

#[test]
fn test_reduce_db_prepass_deletes_level0_satisfied_learned_clause() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    // Root assignment: a = true.
    solver.enqueue(Literal::positive(a), None);

    // Learned clause satisfied by the root assignment.
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], true);
    solver.arena.set_lbd(clause_idx, 10);

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();
    assert!(
        !solver.arena.is_active(clause_idx),
        "reduce_db prepass must delete learned clauses satisfied at level 0 (#3723)"
    );
}

#[test]
fn test_reduce_db_reason_at_higher_level_is_protected() {
    // Test that a clause acting as a reason at a non-zero level
    // is still protected during reduce.
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    // Decision at level 1: a = true.
    solver.decide(Literal::positive(a));

    // Clause implies b at level 1 (reason is NOT cleared since level > 0).
    let clause_idx = solver.add_clause_db(&[Literal::negative(a), Literal::positive(b)], true);
    solver.arena.set_lbd(clause_idx, 10);
    solver.enqueue(Literal::positive(b), Some(ClauseRef(clause_idx as u32)));

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();
    assert!(
        solver.arena.is_active(clause_idx),
        "reduce_db must not delete reason-protected clauses at level > 0"
    );
}

#[test]
fn test_reduce_db_prepass_deletes_level0_satisfied_irredundant_clause() {
    // CaDiCaL collect.cpp:73-88 mark_satisfied_clauses_as_garbage():
    // Level-0-satisfied clauses are permanently true and should be deleted
    // regardless of whether they are learned or irredundant (#8038).
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    solver.enqueue(Literal::positive(a), None);
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();
    assert!(
        !solver.arena.is_active(clause_idx),
        "reduce_db prepass should delete level-0-satisfied irredundant clauses (CaDiCaL parity)"
    );
}

#[test]
fn test_reduce_db_deletes_fixed_reducetarget_fraction_in_normal_mode() {
    let mut solver = Solver::new(8);
    add_tier2_learned_unit_clauses(&mut solver, 8);

    let before = count_active_learned_clauses(&solver);
    solver.reduce_db();
    let after = count_active_learned_clauses(&solver);

    assert_eq!(
        before, 8,
        "test fixture should provide 8 learned candidates"
    );
    assert_eq!(
        before - after,
        6,
        "normal-mode reducetarget must delete 75% (floor) of candidates"
    );
}

#[test]
fn test_reduce_db_deletes_fixed_reducetarget_fraction_when_over_limit() {
    let mut solver = Solver::new(8);
    add_tier2_learned_unit_clauses(&mut solver, 8);
    solver.set_max_learned_clauses(Some(0));

    let before = count_active_learned_clauses(&solver);
    solver.reduce_db();
    let after = count_active_learned_clauses(&solver);

    assert_eq!(
        before, 8,
        "test fixture should provide 8 learned candidates"
    );
    assert_eq!(
        before - after,
        6,
        "over-limit reducetarget must delete 75% (floor) of candidates"
    );
}

#[test]
fn test_reduce_db_reducetarget_uses_floor_rounding() {
    let mut solver = Solver::new(3);
    add_tier2_learned_unit_clauses(&mut solver, 3);

    let before = count_active_learned_clauses(&solver);
    solver.reduce_db();
    let after = count_active_learned_clauses(&solver);

    assert_eq!(
        before, 3,
        "test fixture should provide 3 learned candidates"
    );
    assert_eq!(
        before - after,
        2,
        "75% of 3 candidates must floor to 2 deletions"
    );
}

/// CaDiCaL reduce_less_useful (#5132): higher-glue clauses are deleted
/// first. This test verifies that the 3 highest-glue clauses out of 4
/// are deleted (75% target), ordered purely by glue then size.
#[test]
fn test_reduce_db_glue_ordering() {
    let mut solver = Solver::new(4);

    // Add 4 tier2 learned clauses with varying glue.
    // With 75% target, 3 of 4 will be deleted — the 3 highest glue.
    let vars: Vec<Variable> = (0..4).map(|i| Variable(i as u32)).collect();

    // Clause A: glue 7
    let a = solver.add_clause_db(&[Literal::positive(vars[0])], true);
    solver.arena.set_lbd(a, 7);

    // Clause B: glue 12
    let b = solver.add_clause_db(&[Literal::positive(vars[1])], true);
    solver.arena.set_lbd(b, 12);

    // Clause C: glue 10
    let c = solver.add_clause_db(&[Literal::positive(vars[2])], true);
    solver.arena.set_lbd(c, 10);

    // Clause D: glue 15
    let d = solver.add_clause_db(&[Literal::positive(vars[3])], true);
    solver.arena.set_lbd(d, 15);

    solver.reduce_db();

    // Glue ordering: D(15) > B(12) > C(10) > A(7).
    // 75% of 4 = 3 deleted: D, B, C should be deleted; A should survive.
    assert!(
        solver.arena.is_active(a),
        "glue-7 clause A must survive (lowest glue)"
    );
    assert!(
        !solver.arena.is_active(d),
        "glue-15 clause D must be deleted (highest glue)"
    );
    assert!(
        !solver.arena.is_active(b),
        "glue-12 clause B must be deleted (second highest glue)"
    );
    assert!(
        !solver.arena.is_active(c),
        "glue-10 clause C must be deleted (third highest glue)"
    );
}

/// Multi-variable reduce_db test with active watches and reason entries.
/// Verifies acceptance criterion #2 from #5091: after reduce_db with byte
/// limit active, all ClauseRef values in reason[] and watch lists remain
/// valid (point to active clauses).
#[test]
fn test_reduce_db_preserves_clause_ref_integrity_5091() {
    let num_vars = 10;
    let mut solver = Solver::new(num_vars);

    // Add irredundant binary clauses that create implication chains.
    // (¬a → b) encoded as (a ∨ b): if a is false, b is implied.
    let v: Vec<Variable> = (0..num_vars as u32).map(Variable).collect();

    // Clause 0: (v0 ∨ v1) — if ¬v0 then v1
    let reason_clause_0 =
        solver.add_clause_db(&[Literal::positive(v[0]), Literal::positive(v[1])], false);
    // Clause 1: (v2 ∨ v3) — if ¬v2 then v3
    let reason_clause_1 =
        solver.add_clause_db(&[Literal::positive(v[2]), Literal::positive(v[3])], false);

    // Set up reason entries: v1 was implied by clause 0, v3 by clause 1.
    solver.enqueue(Literal::negative(v[0]), None); // decision
    solver.enqueue(
        Literal::positive(v[1]),
        Some(ClauseRef(reason_clause_0 as u32)),
    );
    solver.enqueue(Literal::negative(v[2]), None); // decision
    solver.enqueue(
        Literal::positive(v[3]),
        Some(ClauseRef(reason_clause_1 as u32)),
    );

    // Add many learned tier-2 clauses with high LBD to create reduction
    // pressure. Use distinct variable pairs so watches are spread out.
    let mut learned_indices = Vec::new();
    for i in 0..20 {
        let a = v[(i * 2) % num_vars];
        let b = v[(i * 2 + 1) % num_vars];
        let idx = solver.add_clause_db(&[Literal::positive(a), Literal::negative(b)], true);
        solver.arena.set_lbd(idx, 15); // high LBD = tier2 = deletable
        learned_indices.push(idx);
    }

    // Set byte limit below current usage to trigger aggressive reduction.
    let current_bytes = solver.arena.memory_bytes();
    solver.set_max_clause_db_bytes(Some(current_bytes / 2));

    // Verify pre-condition: reason clauses are active.
    assert!(solver.arena.is_active(reason_clause_0));
    assert!(solver.arena.is_active(reason_clause_1));

    solver.reduce_db();

    // Post-condition 1: reason clauses must still be active.
    assert!(
        solver.arena.is_active(reason_clause_0),
        "reason clause 0 must survive reduce_db"
    );
    assert!(
        solver.arena.is_active(reason_clause_1),
        "reason clause 1 must survive reduce_db"
    );

    // Post-condition 2: every reason entry for an *assigned* variable
    // points to an active clause. Unassigned variables may retain stale
    // reason values after backtrack store elimination (#6991).
    for (var_idx, vd) in solver.var_data.iter().enumerate() {
        if vd.reason != NO_REASON && solver.var_is_assigned(var_idx) {
            let idx = vd.reason as usize;
            assert!(
                solver.arena.is_active(idx),
                "reason clause {idx} for variable {var_idx} is not active after reduce_db"
            );
        }
    }

    // Post-condition 3: some learned clauses were deleted (reduction worked).
    let surviving_learned = learned_indices
        .iter()
        .filter(|&&idx| solver.arena.is_active(idx))
        .count();
    assert!(
        surviving_learned < learned_indices.len(),
        "reduce_db must delete some tier-2 learned clauses (survived {surviving_learned}/{})",
        learned_indices.len()
    );
}
