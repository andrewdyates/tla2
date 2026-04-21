// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Restart and clause database management tests: Luby sequence, glucose restart,
//! geometric restart, LBD EMA tracking, and reduce-DB scheduling.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

// ========================================================================
// Clause Database Reduction Scheduling
// ========================================================================

#[test]
fn test_should_reduce_db_triggers_on_clause_db_byte_limit() {
    let mut solver = Solver::new(1);
    let initial_bytes = solver.arena.memory_bytes();

    // should_reduce_db uses a strict `>` check, so matching the current bytes
    // should not trigger reduction.
    solver.set_max_clause_db_bytes(Some(initial_bytes));
    assert!(!solver.should_reduce_db());

    // Force the arena capacity to grow so memory_bytes() increases past the limit.
    let v0 = Variable(0);
    for _ in 0..32 {
        let idx = solver.add_clause_db(&[Literal::positive(v0)], true);
        solver.arena.set_lbd(idx, 10);
    }

    assert!(
        solver.arena.memory_bytes() > initial_bytes,
        "test setup failed: clause DB bytes did not grow"
    );
    assert!(solver.should_reduce_db());
}

#[test]
fn test_reduce_db_deletes_over_byte_limit_no_compact() {
    let mut solver = Solver::new(1);
    let v0 = Variable(0);

    for _ in 0..100 {
        let idx = solver.add_clause_db(&[Literal::positive(v0)], true);
        solver.arena.set_lbd(idx, 10);
    }

    let bytes_before = solver.arena.memory_bytes();
    solver.set_max_clause_db_bytes(Some(bytes_before.saturating_sub(1)));

    let active_before = solver.arena.active_literals();

    let clause_changes_before = solver.cold.clause_db_changes;
    solver.reduce_db();

    let active_after = solver.arena.active_literals();

    // Reduce_db should delete tier-2 learned clauses aggressively when
    // over the byte limit, but does NOT compact the arena (compact would
    // renumber clause indices, invalidating ClauseRef values — see #5091).
    assert!(
        active_after < active_before,
        "reduce_db should delete clauses when over byte limit"
    );
    assert!(
        solver.cold.clause_db_changes > clause_changes_before,
        "reduce_db deletions must flow through unified mutation helpers"
    );
}

#[test]

// ========================================================================
// Luby Sequence + Restart Threshold
// ========================================================================

fn test_luby_sequence() {
    // The Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
    for (i, &exp) in expected.iter().enumerate() {
        let luby = Solver::get_luby((i + 1) as u32);
        assert_eq!(luby, exp, "Luby({}) should be {}, got {}", i + 1, exp, luby);
    }
}

#[test]
fn test_luby_first_values() {
    // Check first few values specifically
    assert_eq!(Solver::get_luby(1), 1);
    assert_eq!(Solver::get_luby(2), 1);
    assert_eq!(Solver::get_luby(3), 2);
    assert_eq!(Solver::get_luby(4), 1);
    assert_eq!(Solver::get_luby(5), 1);
    assert_eq!(Solver::get_luby(6), 2);
    assert_eq!(Solver::get_luby(7), 4);
}

#[test]
fn test_restart_threshold_increases() {
    // Verify restart thresholds follow Luby pattern
    let base = DEFAULT_RESTART_BASE;
    let mut thresholds = Vec::new();

    for i in 1..=7 {
        let luby = Solver::get_luby(i);
        thresholds.push(base * u64::from(luby));
    }

    // Expected: [base*1, base*1, base*2, base*1, base*1, base*2, base*4]
    assert_eq!(thresholds[0], base); // luby(1) = 1
    assert_eq!(thresholds[1], base); // luby(2) = 1
    assert_eq!(thresholds[2], base * 2); // luby(3) = 2
    assert_eq!(thresholds[6], base * 4); // luby(7) = 4
}

/// Luby sequence must not overflow for large restart counters.
/// Before the fix, `(1u32 << k) - 1` overflowed when k >= 32
/// (i.e., i > 2^31 - 1), causing a panic in debug mode.
#[test]
fn test_luby_no_overflow_large_values() {
    // 2^31 - 1 is the largest value where k=31 exactly matches
    // luby(2^k - 1) = 2^(k-1), so luby(2^31-1) = 2^30
    let val = Solver::get_luby((1u32 << 31) - 1);
    assert_eq!(val, 1u32 << 30, "luby(2^31-1) should be 2^30");
    // One past that boundary triggers k=32 in the old code (overflow).
    // luby(2^31) should recurse: luby(2^31 - (2^31 - 1)) = luby(1) = 1
    assert_eq!(Solver::get_luby(1u32 << 31), 1);
    // u32::MAX = 2^32 - 1, so luby(2^32-1) = 2^31
    assert_eq!(Solver::get_luby(u32::MAX), 1u32 << 31);
}

#[test]

// ========================================================================
// LBD EMA + Should-Restart Tests
// ========================================================================

fn test_update_lbd_ema_tracks_lbd_values() {
    let mut solver = Solver::new(4);
    // Initialize EMAs to 0 (default state after construction)
    assert_eq!(solver.cold.lbd_ema_fast, 0.0);
    assert_eq!(solver.cold.lbd_ema_slow, 0.0);

    // Feed a constant LBD value; both EMAs should converge toward it.
    for _ in 0..1000 {
        solver.update_lbd_ema(5);
    }
    // Fast EMA should be very close to 5.0 after 1000 updates
    assert!(
        (solver.cold.lbd_ema_fast - 5.0).abs() < 0.01,
        "fast EMA should converge to 5.0, got {}",
        solver.cold.lbd_ema_fast
    );
    // Slow EMA should also move toward 5.0, but more slowly
    assert!(
        solver.cold.lbd_ema_slow > 0.0,
        "slow EMA should be positive after updates"
    );

    // Now feed a sudden spike; fast EMA should react more than slow EMA
    let slow_before = solver.cold.lbd_ema_slow;
    let fast_before = solver.cold.lbd_ema_fast;
    solver.update_lbd_ema(50);
    let fast_delta = solver.cold.lbd_ema_fast - fast_before;
    let slow_delta = solver.cold.lbd_ema_slow - slow_before;
    assert!(
        fast_delta > slow_delta,
        "fast EMA should react more to spike than slow EMA: fast_delta={fast_delta}, slow_delta={slow_delta}"
    );
}

/// Test should_restart returns false before minimum conflict threshold.
#[test]
fn test_should_restart_respects_min_conflicts() {
    let mut solver = Solver::new(4);
    // Default restart_min_conflicts is 2 (matching CaDiCaL's restartint=2).
    // Set conflicts below threshold.
    solver.num_conflicts = 1;
    solver.conflicts_since_restart = 1;
    assert!(
        !solver.should_restart(),
        "should_restart must return false when num_conflicts < restart_min_conflicts"
    );
}

/// Test should_restart returns false when conflicts_since_restart is 0.
#[test]
fn test_should_restart_requires_conflicts_since_restart() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 0;
    assert!(
        !solver.should_restart(),
        "should_restart must return false when no conflicts since last restart"
    );
}

/// Test that Glucose-style restart fires when fast EMA exceeds margin * slow EMA.
#[test]
fn test_should_restart_glucose_fires_on_ema_spike() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.glucose_restarts = true;
    solver.stable_mode = false;
    // Set phase length very high to stay in focused mode
    solver.cold.stable_phase_length = 1_000_000;
    solver.cold.stable_mode_start_conflicts = 0;

    // Set EMAs so fast > RESTART_MARGIN(1.10) * slow
    solver.cold.lbd_ema_slow = 5.0;
    solver.cold.lbd_ema_fast = 6.0; // 6.0 > 1.10 * 5.0 = 5.5
    assert!(
        solver.should_restart(),
        "glucose restart should fire when lbd_ema_fast > RESTART_MARGIN * lbd_ema_slow"
    );
}

/// Test that Glucose-style restart does NOT fire when EMAs are close.
#[test]
fn test_should_restart_glucose_holds_on_stable_ema() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.glucose_restarts = true;
    solver.stable_mode = false;
    solver.cold.stable_phase_length = 1_000_000;
    solver.cold.stable_mode_start_conflicts = 0;

    // Set EMAs so fast < RESTART_MARGIN(1.10) * slow
    solver.cold.lbd_ema_slow = 5.0;
    solver.cold.lbd_ema_fast = 5.4; // 5.4 < 1.10 * 5.0 = 5.5
    assert!(
        !solver.should_restart(),
        "glucose restart should NOT fire when lbd_ema_fast < RESTART_MARGIN * lbd_ema_slow"
    );
}

/// Test that stable-mode restarts follow Knuth's reluctant doubling (Luby sequence).
/// The Luby sequence is: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
/// Each value is multiplied by RELUCTANT_INIT (1024) to get the interval.
#[test]
fn test_should_restart_reluctant_luby_sequence() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.stable_mode = true;
    solver.cold.stable_phase_length = 1_000_000;
    solver.cold.stable_mode_start_conflicts = 0;

    // Start at (u=1, v=1, countdown=1) so first tick fires immediately.
    // Set ticked_at = num_conflicts - 1 so 1 new conflict triggers the tick.
    solver.cold.reluctant_u = 1;
    solver.cold.reluctant_v = 1;
    solver.cold.reluctant_countdown = 1;
    solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;

    // Expected Luby sequence values (v after each restart fires):
    //   u=1,v=1: (1&-1)==1 -> u=2,v=1 -> countdown=1*1024
    //   u=2,v=1: (2&-2)=2!=1 -> v=2 -> countdown=2*1024
    //   u=2,v=2: (2&-2)==2 -> u=3,v=1 -> countdown=1*1024
    //   u=3,v=1: (3&-3)=1==1 -> u=4,v=1 -> countdown=1*1024
    //   u=4,v=1: (4&-4)=4!=1 -> v=2 -> countdown=2*1024
    //   u=4,v=2: (4&-4)=4!=2 -> v=4 -> countdown=4*1024
    //   u=4,v=4: (4&-4)==4 -> u=5,v=1 -> countdown=1*1024
    let expected_v: [u64; 7] = [1, 2, 1, 1, 2, 4, 1];

    solver.conflicts_since_restart = 1;
    // First tick fires: delta = num_conflicts - ticked_at = 1, countdown 1->0
    assert!(
        solver.should_restart(),
        "first tick should fire (countdown=1)"
    );

    for (i, &exp_v) in expected_v.iter().enumerate() {
        assert_eq!(
            solver.cold.reluctant_v,
            exp_v,
            "after restart {}, v should be {} (Luby sequence)",
            i + 1,
            exp_v,
        );
        assert_eq!(
            solver.cold.reluctant_countdown,
            exp_v * RELUCTANT_INIT,
            "countdown should be v * RELUCTANT_INIT after restart {}",
            i + 1,
        );
        // Drain countdown to trigger next restart: simulate 1 new conflict
        solver.cold.reluctant_countdown = 1;
        solver.num_conflicts += 1;
        solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;
        solver.conflicts_since_restart = 1;
        assert!(
            solver.should_restart(),
            "should fire after drain (restart {})",
            i + 1
        );
    }
}

/// Test geometric restart schedule: next_restart = initial * factor^n.
/// Z3 uses this for QF_LRA with initial=100, factor=1.1.
#[test]
fn test_should_restart_geometric_schedule() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.set_geometric_restarts(100.0, 1.1);

    // Restart 0: threshold = 100 * 1.1^0 = 100
    solver.cold.restarts = 0;
    solver.conflicts_since_restart = 99;
    assert!(
        !solver.should_restart(),
        "geometric: 99 < 100, should not restart"
    );
    solver.conflicts_since_restart = 100;
    assert!(
        solver.should_restart(),
        "geometric: 100 >= 100, should restart"
    );

    // Restart 1: threshold = 100 * 1.1^1 = 110
    solver.cold.restarts = 1;
    solver.conflicts_since_restart = 109;
    assert!(
        !solver.should_restart(),
        "geometric: 109 < 110, should not restart"
    );
    solver.conflicts_since_restart = 110;
    assert!(
        solver.should_restart(),
        "geometric: 110 >= 110, should restart"
    );

    // Restart 5: threshold = 100 * 1.1^5 ≈ 161
    solver.cold.restarts = 5;
    solver.conflicts_since_restart = 160;
    assert!(
        !solver.should_restart(),
        "geometric: 160 < 161, should not restart"
    );
    solver.conflicts_since_restart = 162;
    assert!(
        solver.should_restart(),
        "geometric: 162 >= 161, should restart"
    );
}

#[test]
fn test_pick_phase_focused_mode_uses_saved_phase() {
    // Kissat-style phase cycling (decide.c:178-187): in focused mode,
    // (mode_switch_count >> 1) & 7 selects an 8-slot cycle.
    // Slots 1 and 3 force fixed polarity; other slots use saved phase.
    let mut solver = Solver::new(1);
    let var = Variable(0);

    solver.stable_mode = false;

    // Slot 1 forces positive regardless of saved phase
    solver.cold.mode_switch_count = 2; // (2 >> 1) & 7 = 1
    solver.phase[var.index()] = -1;
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "focused mode slot 1 should force positive (Kissat INITIAL_PHASE)",
    );

    // Slot 3 forces negative regardless of saved phase
    solver.cold.mode_switch_count = 6; // (6 >> 1) & 7 = 3
    solver.phase[var.index()] = 1;
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "focused mode slot 3 should force negative (Kissat inverted)",
    );

    // Slot 0 uses saved phase
    solver.cold.mode_switch_count = 0; // (0 >> 1) & 7 = 0
    solver.phase[var.index()] = -1;
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "focused mode slot 0 should use saved phase (negative)",
    );

    // No saved phase on non-override slot -> default positive
    solver.phase[var.index()] = 0;
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "focused mode with no saved phase should default to positive",
    );
}

#[test]
fn test_should_restart_mode_switch_increments_counter_and_starts_random_burst() {
    let mut solver = Solver::new(1);

    solver.num_conflicts = solver.cold.restart_min_conflicts;
    solver.conflicts_since_restart = 1;
    solver.stable_mode = false;
    solver.cold.stable_phase_length = 1;
    solver.cold.stable_mode_start_conflicts = 0;

    assert!(
        !solver.should_restart(),
        "mode switch alone should not force a restart",
    );
    assert!(solver.stable_mode, "first switch should enter stable mode");
    assert_eq!(solver.cold.mode_switch_count, 1);
    assert_eq!(solver.cold.random_decision_phases, 1);
    assert!(
        solver.cold.randomized_deciding > 0,
        "mode switch should start a non-empty random decision burst",
    );
    assert_eq!(
        solver.cold.next_random_decision, solver.num_conflicts,
        "first mode switch should reuse the shared random-sequence scheduler",
    );

    let first_burst = solver.cold.randomized_deciding;

    solver.num_conflicts += 1;
    solver.conflicts_since_restart = 1;
    solver.search_ticks[usize::from(solver.stable_mode)] = solver.cold.stabilize_tick_limit + 1;

    assert!(
        !solver.should_restart(),
        "switching back to focused mode should not imply an immediate restart",
    );
    assert!(
        !solver.stable_mode,
        "second switch should return to focused mode",
    );
    assert_eq!(solver.cold.mode_switch_count, 2);
    assert_eq!(solver.cold.random_decision_phases, 2);
    assert!(
        solver.cold.randomized_deciding > 0 && solver.cold.randomized_deciding != first_burst,
        "second mode switch should refresh the random burst state",
    );
}

/// Test that minimize_learned_clause removes a truly redundant literal.
///
/// Constructs a scenario where literal L is implied by the reason chain of
/// other literals in the learned clause. After minimization, L should be removed.
#[test]

// ========================================================================
// Restart-Inprocessing Interaction Tests
// ========================================================================

fn test_restart_inprocessing_is_noop_above_level_zero() {
    let mut solver: Solver = Solver::new(2);
    solver.decide(Literal::positive(Variable(0)));
    assert_eq!(solver.decision_level, 1);

    // Force all inprocessing schedules due.
    solver.num_conflicts = 0;
    solver.inproc_ctrl.vivify.next_conflict = 0;
    solver.inproc_ctrl.subsume.next_conflict = 0;
    solver.inproc_ctrl.probe.next_conflict = 0;
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.inproc_ctrl.bce.next_conflict = 0;
    solver.inproc_ctrl.transred.next_conflict = 0;
    solver.inproc_ctrl.htr.next_conflict = 0;
    solver.inproc_ctrl.sweep.next_conflict = 0;

    let qhead_before = solver.qhead;
    let trail_len_before = solver.trail.len();

    assert!(
        !solver.run_restart_inprocessing(),
        "inprocessing must not run above level 0"
    );
    assert_eq!(solver.decision_level, 1);
    assert_eq!(solver.qhead, qhead_before);
    assert_eq!(solver.trail.len(), trail_len_before);
}

#[test]
fn test_restart_inprocessing_does_not_derive_unsat_on_empty_solver() {
    let mut solver: Solver = Solver::new(4);

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on empty solver"
    );
}

// ========================================================================
// Focused-Mode Phase Cycling (Kissat decide.c:178-187)
// ========================================================================

/// Test that focused-mode phase cycling overrides phase selection on
/// specific mode_switch_count cycles. Kissat uses `(switched >> 1) & 7`
/// to produce an 8-step cycle where slots 1 and 3 force fixed polarities.
#[test]
fn test_phase_cycling_focused_mode_overrides() {
    let mut solver = Solver::new(4);
    solver.stable_mode = false;
    let var = Variable(0);

    // Slot 1 (mode_switch_count=2,3) forces positive regardless of saved phase
    solver.phase[0] = -1;
    solver.cold.mode_switch_count = 2; // (2 >> 1) & 7 = 1
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "slot 1: should force positive (Kissat INITIAL_PHASE)"
    );
    solver.cold.mode_switch_count = 3; // (3 >> 1) & 7 = 1
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "slot 1 (odd): should force positive"
    );

    // Slot 3 (mode_switch_count=6,7) forces negative regardless of saved phase
    solver.phase[0] = 1;
    solver.cold.mode_switch_count = 6; // (6 >> 1) & 7 = 3
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "slot 3: should force negative (Kissat inverted)"
    );
    solver.cold.mode_switch_count = 7; // (7 >> 1) & 7 = 3
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "slot 3 (odd): should force negative"
    );

    // Non-override slots use saved phase
    solver.phase[0] = -1;
    for count in [0u64, 1, 4, 5, 8, 9, 10, 11] {
        let slot = (count >> 1) & 7;
        if slot == 1 || slot == 3 {
            continue;
        }
        solver.cold.mode_switch_count = count;
        assert_eq!(
            solver.pick_phase(var),
            Literal::negative(var),
            "count={count} (slot {slot}): should use saved=negative"
        );
    }
}

/// Test that phase cycling does NOT apply in stable mode.
#[test]
fn test_phase_cycling_stable_mode_no_override() {
    let mut solver = Solver::new(4);
    solver.stable_mode = true;
    let var = Variable(0);
    solver.phase[0] = -1; // saved = negative

    // Even on cycle slots 1 and 3, stable mode should use target/saved phases
    solver.cold.mode_switch_count = 2; // (2 >> 1) & 7 = 1
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "stable mode: slot 1 should NOT override, uses saved phase"
    );

    solver.cold.mode_switch_count = 6; // (6 >> 1) & 7 = 3
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "stable mode: slot 3 should NOT override, uses saved phase"
    );
}

/// Test the full 8-slot cycle to verify wrap-around behavior.
/// Kissat `(switched >> 1) & 7` produces slots 0-7 from pairs of
/// consecutive switch counts. Slots 1 and 3 force fixed polarity;
/// the other 6 slots fall through to saved phase.
#[test]
fn test_phase_cycling_full_cycle() {
    let mut solver = Solver::new(4);
    let var = Variable(0);
    solver.phase[0] = -1; // saved = negative

    // Focused mode: slots 1 and 3 override, others use saved phase
    solver.stable_mode = false;
    for count in 0..16u64 {
        solver.cold.mode_switch_count = count;
        let slot = (count >> 1) & 7;
        let expected = match slot {
            1 => Literal::positive(var),
            3 => Literal::negative(var),
            _ => Literal::negative(var), // saved phase
        };
        assert_eq!(
            solver.pick_phase(var),
            expected,
            "focused mode, count={count} (slot {slot}): expected {expected:?}"
        );
    }

    // Stable mode: no cycling, uses target_phase if set, else saved phase
    solver.stable_mode = true;
    solver.target_phase[0] = 1;
    for count in 0..16u64 {
        solver.cold.mode_switch_count = count;
        assert_eq!(
            solver.pick_phase(var),
            Literal::positive(var),
            "stable mode, count={count}: should use target=positive"
        );
    }
}

// ========================================================================
// Mode-Switch Random Burst (Kissat mode.c:214)
// ========================================================================

/// Test that mode_switch_count is incremented when mode switches occur.
#[test]
fn test_mode_switch_count_incremented() {
    let mut solver = Solver::new(4);
    assert_eq!(solver.cold.mode_switch_count, 0);

    // Force a mode switch by setting up conditions:
    // Set high conflicts past min_conflicts, enable glucose restarts,
    // make the stabilization phase end.
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.stable_mode = false;
    solver.cold.glucose_restarts = true;
    solver.cold.stable_phase_length = 1; // Phase ends immediately
    solver.cold.stable_mode_start_conflicts = 0;

    // Call should_restart which triggers mode switch internally
    solver.should_restart();

    // After mode switch, counter should be incremented
    assert_eq!(
        solver.cold.mode_switch_count, 1,
        "mode_switch_count should be 1 after first switch"
    );
    assert!(solver.stable_mode, "should have switched to stable mode");
}

/// Test that consecutive mode switches increment the counter correctly.
#[test]
fn test_mode_switch_count_consecutive() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.glucose_restarts = true;

    // First switch: focused -> stable
    solver.stable_mode = false;
    solver.cold.stable_phase_length = 1;
    solver.cold.stable_mode_start_conflicts = 0;
    solver.should_restart();
    assert_eq!(solver.cold.mode_switch_count, 1);
    assert!(solver.stable_mode);

    // Second switch: stable -> focused
    // Set tick-based switch conditions
    solver.cold.stabilize_tick_inc = 1;
    solver.cold.stabilize_tick_limit = 0; // Already past limit
    solver.search_ticks[1] = 1; // stable mode ticks > limit
    solver.should_restart();
    assert_eq!(solver.cold.mode_switch_count, 2);
    assert!(!solver.stable_mode);
}

#[test]
fn test_stable_only_lock_survives_reset_search_state() {
    let mut solver = Solver::new(4);
    solver.set_stable_only(true);

    solver.reset_search_state();

    assert!(
        solver.stable_mode,
        "stable-only should survive search reset"
    );
}

#[test]
fn test_stable_only_lock_blocks_mode_switching() {
    let mut solver = Solver::new(4);
    solver.set_stable_only(true);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.stable_phase_length = 1;
    solver.cold.stable_mode_start_conflicts = 0;

    solver.should_restart();

    assert!(
        solver.stable_mode,
        "stable-only should prevent switching back to focused mode"
    );
    assert_eq!(
        solver.cold.mode_switch_count, 0,
        "mode switches must stay disabled under stable-only"
    );
}
