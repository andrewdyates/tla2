// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates
//! Tests for z4-jit: compile small formulas and verify propagation correctness.
//!
//! # Safety
//!
//! All `unsafe { propagate(...) }` calls in these tests satisfy the safety
//! contract documented on `z4_jit::propagate`:
//! - `TestContext` owns all backing arrays (vals, trail, reasons, levels, guards)
//! - Arrays are correctly sized: vals = num_vars * 2, trail = num_vars * 4,
//!   reasons/levels = num_vars, guards = 64 (covers all test clause IDs)
//! - `as_prop_ctx()` constructs a `PropagationContext` with valid pointers
//!   into these owned arrays
//! - Tests are single-threaded (no concurrent access)
//! - The `CompiledFormula` (and its ExecutableMemory) is alive for each call

use crate::{compile, propagate, ClauseGuards, PropagationContext};

/// Helper to create a test propagation context with owned backing arrays.
struct TestContext {
    vals: Vec<i8>,
    trail: Vec<u32>,
    trail_len: u32,
    conflict: u32,
    levels: Vec<u32>,
    reasons: Vec<u32>,
    guards: ClauseGuards,
}

impl TestContext {
    fn new(num_vars: usize) -> Self {
        Self {
            // vals is indexed by encoded literal (var*2 + polarity), so size = num_vars * 2
            vals: vec![0i8; num_vars * 2],
            trail: vec![0u32; num_vars * 4],
            trail_len: 0,
            conflict: 0,
            levels: vec![0u32; num_vars],
            reasons: vec![0u32; num_vars],
            guards: ClauseGuards::new(64),
        }
    }

    fn as_prop_ctx(&mut self) -> PropagationContext {
        PropagationContext {
            vals: self.vals.as_mut_ptr(),
            trail: self.trail.as_mut_ptr(),
            trail_len: &mut self.trail_len as *mut u32,
            conflict: &mut self.conflict as *mut u32,
            levels: self.levels.as_ptr(),
            reasons: self.reasons.as_mut_ptr(),
            decision_level: 1,
            _pad0: 0,
            guards: self.guards.as_ptr(),
        }
    }

    /// Set variable `var` to true.
    /// pos(var) = var*2 is satisfied (1), neg(var) = var*2+1 is falsified (-1).
    fn set_true(&mut self, var: usize) {
        self.vals[var * 2] = 1;
        self.vals[var * 2 + 1] = -1;
    }

    /// Set variable `var` to false.
    /// pos(var) = var*2 is falsified (-1), neg(var) = var*2+1 is satisfied (1).
    fn set_false(&mut self, var: usize) {
        self.vals[var * 2] = -1;
        self.vals[var * 2 + 1] = 1;
    }

    fn propagated_lits(&self) -> &[u32] {
        &self.trail[..self.trail_len as usize]
    }
}

/// Encode a positive literal for variable `var`.
fn pos(var: u32) -> u32 {
    var * 2
}

/// Encode a negative literal for variable `var`.
fn neg(var: u32) -> u32 {
    var * 2 + 1
}


// ---------- Binary clause tests ----------

#[test]
fn test_binary_clause_propagation() {
    // Clause: (x0 | x1)
    let lits = [pos(0), pos(1)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(2, &clauses).unwrap();

    // Set x0 = false => should propagate x1=true
    let mut tc = TestContext::new(2);
    tc.set_false(0);
    let mut ctx = tc.as_prop_ctx();

    // polarity=1 => propagate_neg(x0): x0 false, pos(x0)=lit0 false
    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict, "should not conflict");
    assert_eq!(tc.trail_len, 1, "should have propagated one literal");
    assert_eq!(tc.trail[0], pos(1), "should propagate x1=true");
    assert_eq!(tc.reasons[1], 0, "reason should be clause 0");
}

#[test]
fn test_binary_clause_conflict() {
    let lits = [pos(0), pos(1)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(2, &clauses).unwrap();

    let mut tc = TestContext::new(2);
    tc.set_false(0);
    tc.set_false(1);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(conflict, "should detect conflict");
    assert_eq!(tc.conflict, 0, "conflict clause should be 0");
}

#[test]
fn test_binary_clause_satisfied() {
    let lits = [pos(0), pos(1)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(2, &clauses).unwrap();

    let mut tc = TestContext::new(2);
    tc.set_false(0);
    tc.set_true(1);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0, "no propagation needed");
}

// ---------- Negative literal tests ----------

#[test]
fn test_binary_negative_literals() {
    // Clause: (neg(0) | pos(1))
    let lits = [neg(0), pos(1)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(2, &clauses).unwrap();

    // Set x0 = true => neg(0) is false => should propagate pos(1)
    let mut tc = TestContext::new(2);
    tc.set_true(0);
    let mut ctx = tc.as_prop_ctx();

    // polarity=0 => propagate_pos(x0): x0 true, neg(x0)=lit1 false
    let conflict = unsafe { propagate(&formula, 0, 0, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1);
    assert_eq!(tc.trail[0], pos(1));
}

// ---------- Ternary clause tests ----------

#[test]
fn test_ternary_clause_propagation() {
    let lits = [pos(0), pos(1), pos(2)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(3, &clauses).unwrap();

    // Set x0 = false, x1 = false => should propagate x2
    let mut tc = TestContext::new(3);
    tc.set_false(0);
    tc.set_false(1);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1);
    assert_eq!(tc.trail[0], pos(2));
}

#[test]
fn test_ternary_clause_two_unassigned() {
    let lits = [pos(0), pos(1), pos(2)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(3, &clauses).unwrap();

    // Set x0 = false, x1 and x2 unassigned => no propagation
    let mut tc = TestContext::new(3);
    tc.set_false(0);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0);
}

#[test]
fn test_ternary_clause_conflict() {
    let lits = [pos(0), pos(1), pos(2)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(3, &clauses).unwrap();

    let mut tc = TestContext::new(3);
    tc.set_false(0);
    tc.set_false(1);
    tc.set_false(2);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(conflict);
    assert_eq!(tc.conflict, 0);
}

// ---------- Short clause tests (4 lits) ----------

#[test]
fn test_short_clause_propagation() {
    let lits = [pos(0), pos(1), pos(2), pos(3)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(4, &clauses).unwrap();

    // Set x0, x1, x2 = false => propagate x3
    let mut tc = TestContext::new(4);
    tc.set_false(0);
    tc.set_false(1);
    tc.set_false(2);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1);
    assert_eq!(tc.trail[0], pos(3));
}

#[test]
fn test_short_clause_satisfied_early_exit() {
    let lits = [pos(0), pos(1), pos(2), pos(3)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(4, &clauses).unwrap();

    let mut tc = TestContext::new(4);
    tc.set_false(0);
    tc.set_true(2);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0);
}

// ---------- Multiple clauses per variable ----------

#[test]
fn test_multiple_clauses_per_variable() {
    // Clause 0: (x0 | x1), Clause 1: (x0 | x2)
    let lits0 = [pos(0), pos(1)];
    let lits1 = [pos(0), pos(2)];
    let clauses = vec![
        (0u32, lits0.as_slice()),
        (1u32, lits1.as_slice()),
    ];
    let formula = compile(3, &clauses).unwrap();

    let mut tc = TestContext::new(3);
    tc.set_false(0);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 2);
    let propagated: Vec<u32> = tc.propagated_lits().to_vec();
    assert!(propagated.contains(&pos(1)));
    assert!(propagated.contains(&pos(2)));
}

#[test]
fn test_multiple_clauses_conflict_on_second() {
    // Clause 0: (x0 | x1) => x1 unassigned, propagates
    // Clause 1: (x0 | x2) => x2 false, should conflict
    let lits0 = [pos(0), pos(1)];
    let lits1 = [pos(0), pos(2)];
    let clauses = vec![
        (0u32, lits0.as_slice()),
        (1u32, lits1.as_slice()),
    ];
    let formula = compile(3, &clauses).unwrap();

    let mut tc = TestContext::new(3);
    tc.set_false(0);
    tc.set_false(2);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(conflict);
    assert_eq!(tc.conflict, 1);
    assert!(tc.trail_len >= 1);
}

// ---------- No-op for variables without clauses ----------

#[test]
fn test_no_clauses_for_variable() {
    let lits = [pos(0), pos(1)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(3, &clauses).unwrap();

    let mut tc = TestContext::new(3);
    tc.set_false(2);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 2, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0);
}

// ---------- Formula compilation error cases ----------

#[test]
fn test_empty_clause_rejected() {
    let lits: [u32; 0] = [];
    let clauses = vec![(0u32, lits.as_slice())];
    let result = compile(1, &clauses);
    assert!(result.is_err());
}

#[test]
fn test_unit_clause_rejected() {
    let lits = [pos(0)];
    let clauses = vec![(0u32, lits.as_slice())];
    let result = compile(1, &clauses);
    assert!(result.is_err());
}

// ---------- Metadata ----------

#[test]
fn test_clause_metadata() {
    let lits0 = [pos(0), pos(1)];
    let lits1 = [neg(1), pos(2), neg(0)];
    let clauses = vec![
        (0u32, lits0.as_slice()),
        (1u32, lits1.as_slice()),
    ];
    let formula = compile(3, &clauses).unwrap();

    assert_eq!(formula.num_clauses(), 2);
    assert_eq!(formula.num_vars(), 3);

    let meta0 = formula.clause(0).unwrap();
    assert_eq!(meta0.literals, vec![pos(0), pos(1)]);

    let meta1 = formula.clause(1).unwrap();
    assert_eq!(meta1.literals, vec![neg(1), pos(2), neg(0)]);
}

// ---------- Long clause test (>8 lits) ----------

#[test]
fn test_long_clause_propagation() {
    let lits: Vec<u32> = (0..10).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(10, &clauses).unwrap();

    // Set x0..x8 = false, x9 unassigned => propagate x9
    let mut tc = TestContext::new(10);
    for v in 0..9 {
        tc.set_false(v);
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1);
    assert_eq!(tc.trail[0], pos(9));
}

#[test]
fn test_long_clause_conflict() {
    let lits: Vec<u32> = (0..10).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(10, &clauses).unwrap();

    let mut tc = TestContext::new(10);
    for v in 0..10 {
        tc.set_false(v);
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(conflict);
    assert_eq!(tc.conflict, 0);
}

#[test]
fn test_long_clause_satisfied() {
    let lits: Vec<u32> = (0..10).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(10, &clauses).unwrap();

    let mut tc = TestContext::new(10);
    tc.set_false(0);
    tc.set_true(5);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0);
}

// ---------- Embedded blocker early-exit tests (#8016) ----------

#[test]
fn test_blocker_ternary_first_lit_satisfied_skips_clause() {
    // Clause: (x0 | x1 | x2). Trigger: x0 becomes false.
    // other_lits sorted by var index: [x1, x2]. Blocker = x1.
    // If x1 is true, the blocker check skips the clause entirely.
    let lits = [pos(0), pos(1), pos(2)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(3, &clauses).unwrap();

    let mut tc = TestContext::new(3);
    tc.set_false(0);
    tc.set_true(1); // blocker literal satisfied
    // x2 is false — but clause should be skipped before checking x2
    tc.set_false(2);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict, "blocker-satisfied clause should not conflict");
    assert_eq!(tc.trail_len, 0, "blocker-satisfied clause should not propagate");
}

#[test]
fn test_blocker_ternary_blocker_false_falls_through() {
    // Clause: (x0 | x1 | x2). Trigger: x0 false.
    // Blocker x1 is false => must fall through to full ternary check.
    // x2 is unassigned => should propagate x2.
    let lits = [pos(0), pos(1), pos(2)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(3, &clauses).unwrap();

    let mut tc = TestContext::new(3);
    tc.set_false(0);
    tc.set_false(1); // blocker not satisfied
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1, "should propagate x2 after blocker miss");
    assert_eq!(tc.trail[0], pos(2));
}

#[test]
fn test_blocker_short_clause_first_lit_satisfied() {
    // 5-lit clause: (x0 | x1 | x2 | x3 | x4). Trigger: x0 false.
    // other_lits sorted: [x1, x2, x3, x4]. Blocker = x1.
    // x1 true => skip clause.
    let lits = [pos(0), pos(1), pos(2), pos(3), pos(4)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(5, &clauses).unwrap();

    let mut tc = TestContext::new(5);
    tc.set_false(0);
    tc.set_true(1); // blocker satisfied
    tc.set_false(2);
    tc.set_false(3);
    tc.set_false(4);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0, "blocker-satisfied short clause should not propagate");
}

#[test]
fn test_blocker_long_clause_first_lit_satisfied() {
    // 10-lit clause. Trigger: x0 false.
    // Blocker = x1 (lowest-index other lit). x1 true => skip.
    let lits: Vec<u32> = (0..10).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(10, &clauses).unwrap();

    let mut tc = TestContext::new(10);
    tc.set_false(0);
    tc.set_true(1); // blocker satisfied
    for v in 2..10 {
        tc.set_false(v);
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0, "blocker-satisfied long clause should not propagate");
}

#[test]
fn test_blocker_multiple_clauses_mixed() {
    // Clause 0: (x0 | x1 | x2) — blocker x1 is true => skip
    // Clause 1: (x0 | x3 | x4) — blocker x3 is false => fall through, propagate x4
    let lits0 = [pos(0), pos(1), pos(2)];
    let lits1 = [pos(0), pos(3), pos(4)];
    let clauses = vec![
        (0u32, lits0.as_slice()),
        (1u32, lits1.as_slice()),
    ];
    let formula = compile(5, &clauses).unwrap();

    let mut tc = TestContext::new(5);
    tc.set_false(0);
    tc.set_true(1);  // blocker for clause 0 => skip
    tc.set_false(2);
    tc.set_false(3); // blocker for clause 1 => fall through
    // x4 unassigned => propagate
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1, "only clause 1 should propagate");
    assert_eq!(tc.trail[0], pos(4));
}

// ---------- Guard bit tests ----------

#[test]
fn test_guard_deleted_clause_skipped() {
    let lits = [pos(0), pos(1)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(2, &clauses).unwrap();

    let mut tc = TestContext::new(2);
    tc.guards.mark_deleted(0);
    tc.set_false(0);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict, "deleted clause should not cause conflict");
    assert_eq!(tc.trail_len, 0, "deleted clause should not propagate");
}

#[test]
fn test_guard_deleted_among_multiple_clauses() {
    // Clause 0: (x0 | x1), Clause 1: (x0 | x2)
    // Delete clause 0, keep clause 1 active
    let lits0 = [pos(0), pos(1)];
    let lits1 = [pos(0), pos(2)];
    let clauses = vec![(0u32, lits0.as_slice()), (1u32, lits1.as_slice())];
    let formula = compile(3, &clauses).unwrap();

    let mut tc = TestContext::new(3);
    tc.guards.mark_deleted(0);
    tc.set_false(0);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1, "only active clause should propagate");
    assert_eq!(tc.trail[0], pos(2), "clause 1 should propagate x2");
}

#[test]
fn test_guard_reactivated_clause_propagates() {
    let lits = [pos(0), pos(1)];
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(2, &clauses).unwrap();

    let mut tc = TestContext::new(2);
    tc.guards.mark_deleted(0);
    tc.guards.mark_active(0);
    tc.set_false(0);
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1, "reactivated clause should propagate");
    assert_eq!(tc.trail[0], pos(1));
}

// ---------- Extended long clause tests (6-12 lits, #7991) ----------

#[test]
fn test_6lit_clause_propagation() {
    // 6-literal clause: boundary of the new extended range.
    let lits: Vec<u32> = (0..6).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(6, &clauses).unwrap();

    // Set x0..x4 = false, x5 unassigned => propagate x5
    let mut tc = TestContext::new(6);
    for v in 0..5 {
        tc.set_false(v);
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1);
    assert_eq!(tc.trail[0], pos(5));
}

#[test]
fn test_12lit_clause_propagation() {
    // 12-literal clause: upper boundary of the extended range.
    let lits: Vec<u32> = (0..12).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(12, &clauses).unwrap();

    // Set x0..x10 = false, x11 unassigned => propagate x11
    let mut tc = TestContext::new(12);
    for v in 0..11 {
        tc.set_false(v);
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 1);
    assert_eq!(tc.trail[0], pos(11));
}

#[test]
fn test_12lit_clause_conflict() {
    let lits: Vec<u32> = (0..12).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(12, &clauses).unwrap();

    let mut tc = TestContext::new(12);
    for v in 0..12 {
        tc.set_false(v);
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(conflict);
    assert_eq!(tc.conflict, 0);
}

#[test]
fn test_12lit_clause_satisfied_early_exit() {
    let lits: Vec<u32> = (0..12).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(12, &clauses).unwrap();

    let mut tc = TestContext::new(12);
    tc.set_false(0);
    tc.set_true(6); // middle literal satisfied => early exit
    for v in 1..12 {
        if v != 6 {
            tc.set_false(v);
        }
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0, "satisfied clause should not propagate");
}

#[test]
fn test_8lit_clause_two_unassigned() {
    // 8-literal clause with two unassigned => no propagation.
    let lits: Vec<u32> = (0..8).map(pos).collect();
    let clauses = vec![(0u32, lits.as_slice())];
    let formula = compile(8, &clauses).unwrap();

    let mut tc = TestContext::new(8);
    for v in 0..6 {
        tc.set_false(v);
    }
    // x6 and x7 unassigned => 2 unassigned, no unit propagation
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 0, "two unassigned should not propagate");
}

#[test]
fn test_mixed_short_and_long_clauses() {
    // Clause 0 (ternary): (x0 | x1 | x2)
    // Clause 1 (8-lit): (x0 | x3 | x4 | x5 | x6 | x7 | x8 | x9)
    // Both triggered by x0=false.
    let lits0 = [pos(0), pos(1), pos(2)];
    let lits1: Vec<u32> = [0, 3, 4, 5, 6, 7, 8, 9].iter().map(|&v| pos(v)).collect();
    let clauses = vec![
        (0u32, lits0.as_slice()),
        (1u32, lits1.as_slice()),
    ];
    let formula = compile(10, &clauses).unwrap();

    let mut tc = TestContext::new(10);
    tc.set_false(0);
    tc.set_false(1); // clause 0: x1 false, x2 unassigned => propagate x2
    // clause 1: x3..x8 false, x9 unassigned => propagate x9
    for v in 3..9 {
        tc.set_false(v);
    }
    let mut ctx = tc.as_prop_ctx();

    let conflict = unsafe { propagate(&formula, 0, 1, &mut ctx) };
    assert!(!conflict);
    assert_eq!(tc.trail_len, 2, "both clauses should propagate");
    let propagated: Vec<u32> = tc.propagated_lits().to_vec();
    assert!(propagated.contains(&pos(2)), "clause 0 should propagate x2");
    assert!(propagated.contains(&pos(9)), "clause 1 should propagate x9");
}
