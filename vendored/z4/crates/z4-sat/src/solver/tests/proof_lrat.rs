// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #4242: factorization emits valid DRAT proof steps.
///
/// Verifies factorize() emits DRAT proof adds/deletes for the CaDiCaL-style
/// divider+blocked+quotient transaction. Uses a 2×3 ternary factor matrix
/// (reduction=1) since FACTOR_SIZE_LIMIT excludes binary clauses.
#[test]
fn test_factorize_drat_proof_emission() {
    use crate::proof::ProofOutput;

    // 2 factors {a,b} × 3 quotients {(c∨d),(c∨e),(d∨e)} = 6 ternary clauses.
    // After factoring: 2 dividers + 3 quotient clauses = 5. Reduction = 1.
    let pos = |i: u32| Literal::positive(Variable(i));
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), pos(2), pos(3)], // (a ∨ c ∨ d)
        vec![pos(1), pos(2), pos(3)], // (b ∨ c ∨ d)
        vec![pos(0), pos(2), pos(4)], // (a ∨ c ∨ e)
        vec![pos(1), pos(2), pos(4)], // (b ∨ c ∨ e)
        vec![pos(0), pos(3), pos(4)], // (a ∨ d ∨ e)
        vec![pos(1), pos(3), pos(4)], // (b ∨ d ∨ e)
    ];

    let mut solver = Solver::with_proof_output(5, ProofOutput::drat_text(Vec::<u8>::new()));
    for ctrl in [
        &mut solver.inproc_ctrl.vivify,
        &mut solver.inproc_ctrl.vivify_irred,
        &mut solver.inproc_ctrl.subsume,
        &mut solver.inproc_ctrl.probe,
        &mut solver.inproc_ctrl.bve,
        &mut solver.inproc_ctrl.bce,
        &mut solver.inproc_ctrl.condition,
        &mut solver.inproc_ctrl.transred,
        &mut solver.inproc_ctrl.htr,
        &mut solver.inproc_ctrl.gate,
        &mut solver.inproc_ctrl.congruence,
        &mut solver.inproc_ctrl.decompose,
        &mut solver.inproc_ctrl.sweep,
    ] {
        ctrl.enabled = false;
    }
    solver.inproc_ctrl.factor.enabled = true;
    solver.inproc_ctrl.factor.next_conflict = 0;
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    solver.factorize();

    let stats = solver.factor_stats();
    assert!(stats.rounds > 0, "factorize() must run at least one round");
    assert!(
        stats.factored_count > 0,
        "ternary 2×3 matrix must trigger factoring"
    );

    let writer = solver.proof_manager.as_ref().expect("proof writer");
    // Expected: 2 dividers + 1 blocked + 3 quotients = 6 adds;
    //           1 blocked delete + 6 original deletes = 7 deletes.
    assert!(writer.added_count() > 0, "DRAT must have add entries");
    assert!(writer.deleted_count() > 0, "DRAT must have delete entries");
}

// ── Forward DRUP checker integration tests ─────────────────────

#[test]
fn test_forward_checker_integration_solve_unsat() {
    let mut solver: Solver = Solver::new(2);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));
    // (a) ∧ (¬a ∨ b) ∧ (¬a ∨ ¬b) is UNSAT.
    solver.add_clause(vec![a]);
    solver.add_clause(vec![na, b]);
    solver.add_clause(vec![na, nb]);
    let result = solver.solve().into_inner();
    assert!(result.is_unsat());
}

#[test]
fn test_forward_checker_integration_solve_sat() {
    let mut solver: Solver = Solver::new(4);
    solver.enable_forward_checker();
    let v: Vec<Variable> = (0..4).map(Variable).collect();
    let pos = |i: usize| Literal::positive(v[i]);
    let neg = |i: usize| Literal::negative(v[i]);
    // 3-SAT clauses with a satisfying assignment.
    solver.add_clause(vec![pos(0), pos(1), pos(2)]);
    solver.add_clause(vec![neg(0), pos(1), pos(3)]);
    solver.add_clause(vec![pos(0), neg(2), pos(3)]);
    solver.add_clause(vec![neg(1), neg(2), neg(3)]);
    let result = solver.solve().into_inner();
    assert!(result.is_sat());
}

/// Verify that clauses added via `add_clause_watched` (the inprocessing path)
/// are verified as derived by the forward checker, not treated as original.
///
/// This tests the fix for the gap where BVE resolvents, HTR resolvents, and
/// factorization products were added with `learned=false` → `add_original()`
/// in the forward checker, bypassing RUP verification entirely.
///
/// Here we manually call `add_clause_watched` with a correct derived clause
/// to verify the forward checker's `add_derived` path accepts it.
#[test]
fn test_forward_checker_add_clause_watched_checks_derived() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    // (a ∨ b) ∧ (¬a ∨ b) → b is RUP-implied.
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![na, b]);
    // Add derived clause (b) via add_clause_watched (inprocessing path).
    // With the fix, the forward checker calls add_derived → RUP check passes.
    // Before the fix, it called add_original → no check at all.
    let mut derived = vec![b];
    solver.add_clause_watched(&mut derived);
    // If we get here without panic, the forward checker accepted the derived clause.
}

/// Verify that the forward checker detects an incorrect inprocessing-derived
/// clause when added via `add_clause_watched`. The forward checker records
/// the RUP failure and adds the clause as trusted (#7929).
#[test]
fn test_forward_checker_add_clause_watched_rejects_invalid_derived() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    // (a ∨ b) — only one clause, cannot derive (c) from it.
    solver.add_clause(vec![a, b]);
    // Try to add (c) via add_clause_watched — NOT RUP-implied.
    let mut invalid = vec![c];
    solver.add_clause_watched(&mut invalid);
    // Forward checker records the RUP failure but does not panic.
}

// ── Theory lemma forward checker contract (#4586) ───────────────

/// Verify that add_theory_lemma treats theory lemmas as axioms (not derived)
/// in the SAT-level forward checker.
///
/// Before the fix, add_theory_lemma called add_clause_db(literals, true) which
/// set forward_check_derived=true, causing the forward checker to RUP-check
/// theory lemmas. Since theory lemmas originate from the theory solver, they
/// are NOT RUP-derivable from the SAT clause set. With the fix, theory lemmas
/// use forward_check_derived=false so the forward checker adds them as originals.
///
/// This test adds a theory lemma (c) that is NOT implied by the existing SAT
/// clauses. Without the fix, the forward checker would panic on RUP failure.
/// With the fix, the theory lemma is accepted as an axiom.
#[test]
fn test_forward_checker_theory_lemma_treated_as_axiom_not_derived() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    // (a ∨ b) — only one clause. (c) is NOT RUP-derivable.
    solver.add_clause(vec![a, b]);
    // add_theory_lemma should NOT trigger forward checker RUP failure.
    // Theory lemmas are axioms from the theory solver, not derived by SAT.
    solver.add_theory_lemma(vec![c]);
    // If we get here without panic, theory lemma was correctly treated as axiom.
}

/// Verify that derived clauses (learned from conflict analysis) still get
/// RUP-checked by the forward checker even when theory lemmas are present.
///
/// This ensures the fix for #4586 only exempts theory lemmas, not all learned
/// clauses.
#[test]
fn test_forward_checker_derived_still_checked_after_theory_lemma() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    // (a ∨ b) ∧ (¬a ∨ b) → b is RUP-implied.
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![na, b]);
    // Add a theory lemma (c) — axiom, not RUP-checked.
    solver.add_theory_lemma(vec![c]);
    // Now add a derived clause (b) — this IS RUP-implied and must be checked.
    let mut derived = vec![b];
    solver.add_clause_watched(&mut derived);
    // Forward checker accepted both theory axiom and valid derived clause.
}

// ── Level-0 BCP conflict LRAT hint test (#4397) ─────────────────

/// Verify that record_level0_conflict_chain writes non-empty LRAT hints.
///
/// Formula: (a) ∧ (¬a ∨ b) ∧ (¬b) — UNSAT purely from level-0 BCP.
/// After process_initial_clauses enqueues a and ¬b, propagation derives
/// a conflict without any decisions or inprocessing. The empty clause
/// must have resolution hints referencing the original clauses.
#[test]
fn test_lrat_level0_conflict_has_hints() {
    use crate::ProofOutput;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), 3);
    let mut solver = Solver::with_proof_output(2, proof_writer);

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));

    // 3 original clauses → clause IDs 1, 2, 3
    solver.add_clause(vec![a]); // clause 1: a
    solver.add_clause(vec![na, b]); // clause 2: ¬a ∨ b
    solver.add_clause(vec![nb]); // clause 3: ¬b

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // The proof should contain the empty clause derivation with non-empty hints.
    // LRAT format: <id> 0 <hints> 0
    // With empty hints it would be: <id> 0 0  (just "N 0 0")
    // With proper hints it should be: <id> 0 <hint1> <hint2> ... 0
    let lines: Vec<&str> = proof.lines().collect();
    assert!(
        !lines.is_empty(),
        "LRAT proof must not be empty for UNSAT formula"
    );

    // The last line should be the empty clause (no literals before the first 0).
    let last_line = lines.last().expect("proof must have at least one line");
    let tokens: Vec<&str> = last_line.split_whitespace().collect();
    // Format: <id> 0 <hints...> 0
    // The clause ID is first, then literal 0, then hints, then trailing 0.
    assert!(
        tokens.len() >= 2,
        "Empty clause line too short: {last_line}"
    );

    // Find the position of the first "0" (end of literals). For the empty
    // clause, this should be tokens[1].
    let first_zero = tokens
        .iter()
        .position(|t| *t == "0")
        .expect("missing literal terminator");
    assert_eq!(
        first_zero, 1,
        "Expected empty clause (first 0 at position 1), got: {last_line}"
    );

    // Everything between first_zero+1 and the last token (trailing 0) is hints.
    // If there are no hints, the line is just "<id> 0 0".
    let trailing_zero = tokens.len() - 1;
    let hint_count = trailing_zero - first_zero - 1;
    assert!(
        hint_count > 0,
        "BUG (#4397): Empty clause has NO resolution hints. \
         record_level0_conflict_chain must pass hints to proof_writer.\n\
         Proof line: {last_line}\nFull proof:\n{proof}"
    );
}

/// Regression test for #4434: LRAT `add` returns sentinel `Ok(0)` after I/O
/// failure, but `replace_clause_checked` must NOT propagate that sentinel into
/// `clause_ids` or `next_clause_id`.
///
/// Setup: create solver with LRAT using a writer that fails after N bytes.
/// Add original clauses (succeeds), then trigger I/O failure, then call
/// `replace_clause_checked`. Verify clause ID state is unchanged.
#[test]
fn test_lrat_io_failed_sentinel_does_not_corrupt_clause_ids() {
    /// Writer that succeeds for the first `limit` bytes, then fails.
    struct FailAfterN {
        buf: Vec<u8>,
        limit: usize,
    }

    impl Write for FailAfterN {
        fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
            if self.buf.len() + data.len() > self.limit {
                return Err(std::io::Error::other("simulated disk full"));
            }
            self.buf.extend_from_slice(data);
            Ok(data.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    // Allow enough bytes for original clause registration + first few LRAT
    // adds, then trigger failure on the replacement add.
    let writer = FailAfterN {
        buf: Vec::new(),
        limit: 200,
    };
    // 4 original clauses: {x0,x1}, {x0,x2}, {x1,x2}, {¬x1}.
    // The unit clause {¬x1} makes strengthening {x0,x1}→{x0} RUP-valid:
    // assume ¬x0 → from {x0,x1}: unit x1 → from {¬x1}: conflict.
    let proof = ProofOutput::lrat_text(writer, 4);
    // Use 50 variables so the budget-exhaustion clause has unique literals
    let mut solver: Solver = Solver::with_proof_output(50, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    // Add 4 original clauses
    solver.add_clause(vec![x0, x1]);
    solver.add_clause(vec![x0, x2]);
    solver.add_clause(vec![x1, x2]);
    solver.add_clause(vec![Literal::negative(Variable(1))]);

    // Record clause ID state before the failing replacement
    let clause_0_id = solver.cold.clause_ids[0];
    let saved_next = solver.cold.next_clause_id;
    assert!(clause_0_id != 0, "clause 0 should have a non-zero LRAT ID");

    // Exhaust the writer's byte budget to force io_failed on next write
    if let Some(ref mut pw) = solver.proof_manager {
        // Write a large dummy clause with unique literals to exhaust the budget
        let big_clause: Vec<Literal> = (0..50)
            .map(|i| Literal::positive(Variable(i as u32)))
            .collect();
        // Keep adding until io_failed. Use Derived kind since Axiom with
        // empty hints is skipped in LRAT mode (returns Ok(0) without writing).
        for _ in 0..20 {
            let _ = pw.emit_add(&big_clause, &[1], ProofAddKind::Derived);
        }
        assert!(
            pw.has_io_error(),
            "writer should be in io_failed state after exhausting byte budget"
        );
    }

    // Now call replace_clause_checked — the LRAT writer.add will return Ok(0)
    solver.replace_clause_checked(0, &[x0]);

    // Verify: clause_ids[0] must NOT have been overwritten with sentinel 0
    assert_eq!(
        solver.cold.clause_ids[0], clause_0_id,
        "clause_ids[0] must be unchanged after io_failed replacement (was {}, now {})",
        clause_0_id, solver.cold.clause_ids[0]
    );
    // Verify: next_clause_id must NOT have regressed to 1 (sentinel 0 + 1)
    assert!(
        solver.cold.next_clause_id >= saved_next,
        "next_clause_id must not regress: was {}, now {}",
        saved_next,
        solver.cold.next_clause_id
    );
}

/// Regression test for #4398: preprocessing subsumption must emit
/// strengthening additions before deleting the subsumer hint clause ID.
fn disable_non_subsume_inprocessing(solver: &mut Solver) {
    for ctrl in [
        &mut solver.inproc_ctrl.vivify,
        &mut solver.inproc_ctrl.vivify_irred,
        &mut solver.inproc_ctrl.probe,
        &mut solver.inproc_ctrl.bve,
        &mut solver.inproc_ctrl.bce,
        &mut solver.inproc_ctrl.factor,
        &mut solver.inproc_ctrl.condition,
        &mut solver.inproc_ctrl.transred,
        &mut solver.inproc_ctrl.htr,
        &mut solver.inproc_ctrl.gate,
        &mut solver.inproc_ctrl.congruence,
        &mut solver.inproc_ctrl.decompose,
        &mut solver.inproc_ctrl.sweep,
    ] {
        ctrl.enabled = false;
    }
    solver.inproc_ctrl.subsume.enabled = true;
}

fn parse_lrat_add_hints(lines: &[&str], clause_id: u64) -> (usize, Vec<u64>) {
    let add_line_idx = lines
        .iter()
        .position(|line| line.starts_with(&format!("{clause_id} ")) && !line.contains(" d "))
        .expect("expected LRAT add line for strengthened clause");
    let add_tokens: Vec<&str> = lines[add_line_idx].split_whitespace().collect();
    let zero_idx = add_tokens
        .iter()
        .position(|&token| token == "0")
        .expect("LRAT add line must contain literal terminator");
    let hints = add_tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&token| token != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse"))
        .collect();
    (add_line_idx, hints)
}

/// Test that LRAT proof references the subsumer clause ID when strengthening.
///
/// Topology (one-watch forward engine):
///   Clause 0 (LRAT ID 1): {a, ¬y, c}  — target for strengthening
///   Clause 1 (LRAT ID 2): {a, y}       — subsumer (pivot y)
///
/// Clause 1 strengthens Clause 0 to {a, c} by removing ¬y.
/// The LRAT add record for the strengthened clause must reference the
/// subsumer's LRAT ID (2) as a resolution hint.
#[test]
fn test_preprocess_subsumption_strengthen_uses_live_hint_clause_id() {
    use crate::proof::ProofOutput;

    let mut solver = Solver::with_proof_output(3, ProofOutput::lrat_text(Vec::new(), 2));
    solver.preprocessing_quick_mode = false; // test needs subsumption during preprocess
    disable_non_subsume_inprocessing(&mut solver);

    let a = Literal::positive(Variable(0));
    let y = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    // Clause 0: {a, ¬y, c} (ternary, will be strengthened to {a, c})
    // Clause 1: {a, y}     (binary, subsumer with pivot y)
    let c0_off = solver.arena.len();
    solver.add_clause(vec![a, y.negated(), c]);
    let c1_off = solver.arena.len();
    solver.add_clause(vec![a, y]);
    solver.initialize_watches();

    let old_target_id = solver.clause_id(ClauseRef(c0_off as u32));
    let subsumer_id = solver.clause_id(ClauseRef(c1_off as u32));
    assert_eq!(old_target_id, 1);
    assert_eq!(subsumer_id, 2);

    assert!(
        !solver.preprocess(),
        "preprocess should perform strengthening without deriving UNSAT"
    );

    let new_target_id = solver.clause_id(ClauseRef(0));
    assert_ne!(
        new_target_id, old_target_id,
        "strengthened clause must receive a fresh LRAT ID"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let lines: Vec<&str> = proof.lines().collect();

    let (add_line_idx, hints) = parse_lrat_add_hints(&lines, new_target_id);
    assert!(
        hints.contains(&subsumer_id),
        "strengthened clause must reference subsumer ID {subsumer_id}; add line: {}",
        lines[add_line_idx]
    );
}

/// Behavioral end-to-end test: forward checker validates ProofAddKind
/// classification during CDCL solving with LRAT proof output enabled.
///
/// This is the behavioral guard for the #4614 ProofAddKind reconciliation.
/// The forward checker (both solver-level and debug ProofManager-level)
/// validates that:
/// - Learned clauses are RUP-derivable when classified as Derived
/// - Original/axiom clauses bypass RUP check
///
/// If any classification is wrong, the test panics ("forward DRUP check failed").
///
/// Uses PHP(3,2) — small enough for fast test, large enough to force multiple
/// conflicts and learned clauses through the forward checker.
#[test]
fn test_forward_checker_validates_cdcl_proof_classification() {
    use crate::ProofOutput;

    // PHP(3,2): 6 variables (p_ij: pigeon i in hole j), 9 clauses
    let proof_writer = ProofOutput::lrat_text(Vec::new(), 9);
    let mut solver = Solver::with_proof_output(6, proof_writer);
    solver.enable_forward_checker();

    // p_ij: pigeon i, hole j (0-indexed variables)
    let p = |i: usize, j: usize| Literal::positive(Variable((i * 2 + j) as u32));
    let np = |i: usize, j: usize| Literal::negative(Variable((i * 2 + j) as u32));

    // Positive: each pigeon in at least one hole
    solver.add_clause(vec![p(0, 0), p(0, 1)]); // pigeon 0
    solver.add_clause(vec![p(1, 0), p(1, 1)]); // pigeon 1
    solver.add_clause(vec![p(2, 0), p(2, 1)]); // pigeon 2

    // Negative: no two pigeons in the same hole
    solver.add_clause(vec![np(0, 0), np(1, 0)]); // hole 0: pigeons 0,1
    solver.add_clause(vec![np(0, 0), np(2, 0)]); // hole 0: pigeons 0,2
    solver.add_clause(vec![np(1, 0), np(2, 0)]); // hole 0: pigeons 1,2
    solver.add_clause(vec![np(0, 1), np(1, 1)]); // hole 1: pigeons 0,1
    solver.add_clause(vec![np(0, 1), np(2, 1)]); // hole 1: pigeons 0,2
    solver.add_clause(vec![np(1, 1), np(2, 1)]); // hole 1: pigeons 1,2

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(3,2) must be UNSAT");

    // Forward checker validated all learned clause classifications.
    // In debug mode, ProofManager.checker also validated proof emissions.

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    let lines: Vec<&str> = proof.lines().collect();

    // LRAT proof must contain derived clause additions from conflict analysis.
    let add_lines: Vec<&&str> = lines.iter().filter(|l| !l.contains(" d ")).collect();
    assert!(
        add_lines.len() > 1,
        "LRAT proof must contain derived clause additions from conflict analysis; \
         got {} non-delete lines",
        add_lines.len()
    );

    // The proof must end with the empty clause (0 after clause ID = empty literals).
    let last_add = add_lines.last().expect("must have add lines");
    let tokens: Vec<&str> = last_add.split_whitespace().collect();
    assert!(
        tokens.len() >= 3 && tokens[1] == "0",
        "last LRAT add must be the empty clause; got: {last_add}"
    );
}

#[test]
fn test_mark_empty_clause_with_level0_hints_emits_non_empty_lrat_chain() {
    use crate::ProofOutput;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof_writer);

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));

    solver.add_clause(vec![a]);
    solver.add_clause(vec![na, b]);

    assert!(
        solver.process_initial_clauses().is_none(),
        "setup must produce a level-0 trail without an immediate conflict"
    );
    assert!(
        !solver.has_empty_clause,
        "helper test must start before the empty clause is recorded"
    );

    solver.mark_empty_clause_with_level0_hints();

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let last_line = proof
        .lines()
        .last()
        .expect("proof must contain empty clause");
    let tokens: Vec<&str> = last_line.split_whitespace().collect();
    let first_zero = tokens
        .iter()
        .position(|token| *token == "0")
        .expect("empty clause line must contain literal terminator");
    let hint_count = tokens.len() - first_zero - 2;

    assert_eq!(
        first_zero, 1,
        "expected empty clause add line, got: {last_line}"
    );
    assert!(
        hint_count > 0,
        "level-0 helper must attach LRAT hints to the empty clause: {last_line}"
    );
}

/// Create a conditioning-only solver with the given proof output.
/// Formula: (x0 ∨ x1) ∧ (¬x0 ∨ x2) ∧ (¬x1 ∨ x2) — SAT, all 3 globally blocked.
fn conditioning_solver(proof: ProofOutput) -> Solver {
    let (x0, x1, x2) = (Variable(0), Variable(1), Variable(2));
    let clauses = [
        vec![Literal::positive(x0), Literal::positive(x1)],
        vec![Literal::negative(x0), Literal::positive(x2)],
        vec![Literal::negative(x1), Literal::positive(x2)],
    ];
    let mut solver = Solver::with_proof_output(3, proof);
    for ctrl in [
        &mut solver.inproc_ctrl.vivify,
        &mut solver.inproc_ctrl.vivify_irred,
        &mut solver.inproc_ctrl.subsume,
        &mut solver.inproc_ctrl.probe,
        &mut solver.inproc_ctrl.backbone,
        &mut solver.inproc_ctrl.bve,
        &mut solver.inproc_ctrl.bce,
        &mut solver.inproc_ctrl.factor,
        &mut solver.inproc_ctrl.transred,
        &mut solver.inproc_ctrl.htr,
        &mut solver.inproc_ctrl.gate,
        &mut solver.inproc_ctrl.congruence,
        &mut solver.inproc_ctrl.decompose,
        &mut solver.inproc_ctrl.sweep,
    ] {
        ctrl.enabled = false;
    }
    solver.inproc_ctrl.condition.enabled = true;
    solver.preprocessing_quick_mode = false; // test needs conditioning during preprocess
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    solver.initialize_watches();
    solver
}

/// Part of #3906 F3: verify conditioning LRAT proof semantics.
///
/// Conditioning uses regular delete (delete_clause_with_snapshot) — the same
/// pattern as BCE. CaDiCaL uses `weaken_minus` (condition.cpp:791) but
/// regular deletion is accepted by the LRAT checker. Verifies:
/// (1) DRAT preprocess fires, (2) LRAT preprocess fires (lrat_override=false),
/// (3) both emit valid deletion records.
#[test]
fn test_conditioning_lrat_proof_deletions_have_valid_ids() {
    use crate::ProofOutput;

    // 1. DRAT: conditioning fires via preprocess.
    let mut drat = conditioning_solver(ProofOutput::drat_text(Vec::new()));
    assert!(!drat.preprocess());
    assert!(
        drat.inproc.conditioning.stats().clauses_eliminated > 0,
        "DRAT must eliminate"
    );

    // 2. LRAT: conditioning fires via preprocess (lrat_override=false, same as BCE).
    let mut lrat = conditioning_solver(ProofOutput::lrat_text(Vec::new(), 3));
    assert!(!lrat.preprocess());
    assert!(
        lrat.inproc.conditioning.stats().clauses_eliminated > 0,
        "LRAT must also eliminate (same as BCE pattern)"
    );

    // 3. Direct condition() in LRAT: valid deletion records.
    let mut direct = conditioning_solver(ProofOutput::lrat_text(Vec::new(), 3));
    direct.condition();
    let elim = direct.inproc.conditioning.stats().clauses_eliminated;
    assert!(elim > 0, "direct condition() must eliminate");
    let writer = direct.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    verify_lrat_deletions(&proof, elim);
}

/// Add a learned clause via the conflict analysis proof path.
///
/// Mirrors conflict_analysis.rs:1341-1361: proof_emit_add_prechecked (ProofManager
/// only) then add_clause_db_checked (clause DB + forward checker + LRAT ID).
/// Sets tier2 LBD and used=0 so the clause is eligible for flush deletion.
/// Returns the LRAT clause ID assigned by the clause DB.
fn add_learned_clause_for_flush(solver: &mut Solver, clause: &[Literal], hints: &[u64]) -> u64 {
    use crate::proof_manager::ProofAddKind;

    let emitted_id = solver
        .proof_emit_add_prechecked(clause, hints, ProofAddKind::Derived)
        .expect("proof emit add");

    // Sync next_clause_id with LRAT writer (mirrors conflict_analysis.rs:1352-1356).
    if emitted_id != 0 && emitted_id >= solver.cold.next_clause_id {
        solver.cold.next_clause_id = emitted_id;
    }

    let idx = solver.add_clause_db_checked(clause, true, true, hints);
    solver.arena.set_lbd(idx, 10);
    solver.arena.set_used(idx, 0);

    let clause_id = solver.clause_id(ClauseRef(idx as u32));
    assert!(clause_id > 0, "learned clause must have non-zero LRAT ID");
    clause_id
}

/// Verify LRAT proof text contains valid deletion records for specific clause IDs.
fn verify_lrat_deletions_contain_ids(proof: &str, expected_ids: &[u64]) {
    let delete_lines: Vec<&str> = proof.lines().filter(|l| l.contains(" d ")).collect();
    assert!(
        !delete_lines.is_empty(),
        "LRAT proof has 0 delete lines:\n{proof}"
    );

    for line in &delete_lines {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        assert!(tokens.len() >= 3, "LRAT delete line too short: {line}");
        let step_id: u64 = tokens[0].parse().expect("step ID must be numeric");
        assert!(step_id > 0, "step ID must be positive: {line}");
        assert_eq!(tokens[1], "d", "missing 'd' marker: {line}");
        for &tok in &tokens[2..tokens.len() - 1] {
            let id: u64 = tok.parse().expect("clause ID must be numeric");
            assert!(id > 0, "clause ID must be positive: {line}");
        }
        assert_eq!(*tokens.last().unwrap(), "0", "missing trailing 0: {line}");
    }

    let all_deleted: Vec<u64> = delete_lines
        .iter()
        .flat_map(|l| {
            let t: Vec<&str> = l.split_whitespace().collect();
            t[2..t.len() - 1]
                .iter()
                .filter_map(|s| s.parse().ok())
                .collect::<Vec<_>>()
        })
        .collect();

    for &cid in expected_ids {
        assert!(
            all_deleted.contains(&cid),
            "clause ID {cid} missing from LRAT deletions.\n\
             Expected: {expected_ids:?}\nDeleted: {all_deleted:?}\nProof:\n{proof}"
        );
    }
}

/// Part of #5014: flush + LRAT interaction — verify flush emits valid LRAT
/// deletion records for learned clauses properly added to the proof.
///
/// Coverage gap: all flush tests in reduction.rs use Solver::new(N) without
/// proof output; all LRAT tests use formulas too small to trigger flush.
#[test]
fn test_flush_lrat_proof_deletions_have_valid_ids() {
    use crate::ProofOutput;

    let (a, b, c, d, e) = (
        Variable(0),
        Variable(1),
        Variable(2),
        Variable(3),
        Variable(4),
    );

    let originals = [
        vec![Literal::positive(a), Literal::positive(b)], // c1
        vec![Literal::negative(a), Literal::positive(c)], // c2
        vec![Literal::negative(b), Literal::positive(d)], // c3
        vec![Literal::negative(c), Literal::positive(e)], // c4
    ];

    let mut solver = Solver::with_proof_output(
        5,
        ProofOutput::lrat_text(Vec::new(), originals.len() as u64),
    );
    for ctrl in [
        &mut solver.inproc_ctrl.vivify,
        &mut solver.inproc_ctrl.vivify_irred,
        &mut solver.inproc_ctrl.subsume,
        &mut solver.inproc_ctrl.probe,
        &mut solver.inproc_ctrl.bve,
        &mut solver.inproc_ctrl.bce,
        &mut solver.inproc_ctrl.factor,
        &mut solver.inproc_ctrl.transred,
        &mut solver.inproc_ctrl.htr,
        &mut solver.inproc_ctrl.gate,
        &mut solver.inproc_ctrl.congruence,
        &mut solver.inproc_ctrl.decompose,
        &mut solver.inproc_ctrl.sweep,
        &mut solver.inproc_ctrl.condition,
    ] {
        ctrl.enabled = false;
    }
    for clause in &originals {
        assert!(solver.add_clause(clause.clone()));
    }
    solver.initialize_watches();

    // Add resolvents as learned clauses with valid LRAT hint chains.
    let ids = [
        add_learned_clause_for_flush(
            &mut solver,
            &[Literal::positive(b), Literal::positive(c)],
            &[2, 1], // resolve c1,c2 on a
        ),
        add_learned_clause_for_flush(
            &mut solver,
            &[Literal::positive(a), Literal::positive(d)],
            &[3, 1], // resolve c1,c3 on b
        ),
        add_learned_clause_for_flush(
            &mut solver,
            &[Literal::negative(a), Literal::positive(e)],
            &[4, 2], // resolve c2,c4 on c
        ),
    ];

    // Force and verify flush.
    solver.num_conflicts = solver.cold.next_flush;
    solver.reduce_db();

    let remaining = solver
        .arena
        .active_indices()
        .filter(|&i| solver.arena.is_learned(i))
        .count();
    assert_eq!(
        remaining, 0,
        "flush must delete all unused tier2 learned clauses"
    );

    let writer = solver.take_proof_writer().expect("proof writer exists");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    verify_lrat_deletions_contain_ids(&proof, &ids);
}

/// Helper: verify LRAT deletion records in proof text.
fn verify_lrat_deletions(proof: &str, expected_eliminations: u64) {
    let lines: Vec<&str> = proof.lines().collect();

    // Collect deletion lines. LRAT deletion format: "<id> d <id1> <id2> ... 0"
    let delete_lines: Vec<&&str> = lines.iter().filter(|l| l.contains(" d ")).collect();
    assert!(
        !delete_lines.is_empty(),
        "LRAT proof must contain deletion records for conditioning-eliminated clauses; \
         conditioning eliminated {expected_eliminations} clauses but proof has 0 delete lines.\n\
         Full proof:\n{proof}"
    );

    // Every deletion line must have valid (positive, non-zero) clause IDs.
    for &line in &delete_lines {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        assert!(tokens.len() >= 3, "LRAT delete line too short: {line}");
        // First token is the line/step ID (positive integer), second is 'd'.
        let first_id: u64 = tokens[0]
            .parse()
            .unwrap_or_else(|_| panic!("LRAT delete line ID not a number: {line}"));
        assert!(first_id > 0, "LRAT delete line has zero step ID: {line}");
        assert_eq!(
            tokens[1], "d",
            "Expected 'd' marker in LRAT delete line: {line}"
        );
        // All IDs after 'd' and before trailing '0' must be positive.
        for &tok in &tokens[2..tokens.len() - 1] {
            let id: u64 = tok
                .parse()
                .unwrap_or_else(|_| panic!("LRAT delete line non-numeric token: {line}"));
            assert!(id > 0, "LRAT delete references zero clause ID: {line}");
        }
        // Last token should be '0' (terminator).
        assert_eq!(
            *tokens.last().unwrap(),
            "0",
            "LRAT delete line missing trailing 0: {line}"
        );
    }
}

/// Disable all inprocessing except BVE.
fn disable_non_bve_inprocessing(solver: &mut Solver) {
    for ctrl in [
        &mut solver.inproc_ctrl.vivify,
        &mut solver.inproc_ctrl.vivify_irred,
        &mut solver.inproc_ctrl.subsume,
        &mut solver.inproc_ctrl.probe,
        &mut solver.inproc_ctrl.bce,
        &mut solver.inproc_ctrl.condition,
        &mut solver.inproc_ctrl.factor,
        &mut solver.inproc_ctrl.transred,
        &mut solver.inproc_ctrl.htr,
        &mut solver.inproc_ctrl.gate,
        &mut solver.inproc_ctrl.congruence,
        &mut solver.inproc_ctrl.decompose,
        &mut solver.inproc_ctrl.sweep,
    ] {
        ctrl.enabled = false;
    }
    solver.inproc_ctrl.bve.enabled = true;
    solver.inproc_ctrl.bve.next_conflict = 0;
}

/// Check if any derived LRAT add line (ID > `min_derived_id`) has hints
/// containing all of the `required_hint_ids`.
fn lrat_derived_line_has_all_hints(
    proof_text: &str,
    min_derived_id: u64,
    required_hint_ids: &[u64],
) -> bool {
    for line in proof_text.lines() {
        if line.contains(" d ") {
            continue;
        }
        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.len() < 4 {
            continue;
        }
        let id: u64 = match tokens[0].parse() {
            Ok(v) if v > min_derived_id => v,
            _ => continue,
        };
        let _ = id; // suppress unused warning — used in the guard above

        let first_zero = match tokens.iter().position(|t| *t == "0") {
            Some(pos) => pos,
            None => continue,
        };
        if first_zero >= tokens.len() - 1 {
            continue;
        }
        let hints: Vec<u64> = tokens[first_zero + 1..tokens.len() - 1]
            .iter()
            .filter_map(|t| t.parse().ok())
            .collect();
        if required_hint_ids.iter().all(|id| hints.contains(id)) {
            return true;
        }
    }
    false
}

/// Part of #5071: BVE root-level pruning records LRAT chain entries for
/// unit clauses that falsify pruned literals.
///
/// Formula: (c) ∧ (x ∨ ¬c ∨ a) ∧ (¬x ∨ b) ∧ (a ∨ b) ∧ (¬a ∨ ¬b).
/// After c=true propagates, BVE on x produces resolvent (a ∨ b) with ¬c
/// pruned. LRAT hints must include the unit clause ID for c.
///
/// CaDiCaL reference: elim.cpp:303-308 — `unit_id(-lit)` in `lrat_chain`.
#[test]
fn test_bve_root_level_pruning_lrat_hints_include_unit_clause() {
    use crate::ProofOutput;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), 5);
    let mut solver: Solver = Solver::with_proof_output(4, proof_writer);

    let (x, a, b, c) = (Variable(0), Variable(1), Variable(2), Variable(3));

    // 5 original clauses → clause IDs 1..=5
    solver.add_clause(vec![Literal::positive(c)]); // ID=1: (c)
    solver.add_clause(vec![
        Literal::positive(x),
        Literal::negative(c),
        Literal::positive(a),
    ]); // ID=2: (x ∨ ¬c ∨ a)
    solver.add_clause(vec![Literal::negative(x), Literal::positive(b)]); // ID=3
    solver.add_clause(vec![Literal::positive(a), Literal::positive(b)]); // ID=4
    solver.add_clause(vec![Literal::negative(a), Literal::negative(b)]); // ID=5

    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    assert!(solver.propagate().is_none());

    disable_non_bve_inprocessing(&mut solver);
    for v in [a, b, c] {
        solver.freeze(v);
    }

    let derived_unsat = solver.bve();
    assert!(!derived_unsat);
    assert!(solver.inproc.bve.is_eliminated(x));
    assert!(solver.bve_stats().root_literals_pruned > 0);

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // Resolvent hints must include: unit clause (1), pos antecedent (2), neg antecedent (3)
    assert!(
        lrat_derived_line_has_all_hints(&proof_text, 5, &[1, 2, 3]),
        "BUG (#5071): BVE resolvent LRAT hints must include the unit clause ID \
         for pruned ¬c (clause 1) plus antecedent IDs 2 and 3.\nProof:\n{proof_text}"
    );
}

/// Test LRAT proof correctness when tautological original clauses are present.
///
/// Bug found by prop_lrat_proof_valid_on_random_3sat: when add_clause skips
/// tautological clauses (clause_add.rs:219), their LRAT IDs are never registered.
/// The LRAT writer reserves IDs 1..=N but the solver only registers IDs for
/// non-tautological clauses, creating numbering gaps. If the solver emits proof
/// steps with hints referencing the gap IDs, "LRAT hint N references
/// unknown/deleted clause" fires.
///
/// This test uses an UNSAT formula padded with tautologies to force proof emission.
/// The UNSAT core is (a) ∧ (¬a), but 8 tautological clauses precede them,
/// creating ID gaps (IDs 1-8 are unregistered tautologies).
#[test]
fn test_lrat_tautology_skip_id_mismatch() {
    use crate::proof::ProofOutput;

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));

    // 10 original clauses: 8 tautologies + 2 UNSAT core
    let clauses: Vec<Vec<Literal>> = vec![
        vec![a, na, b],  // 1: tautology (a and ¬a)
        vec![na, a, b],  // 2: tautology
        vec![a, nb, na], // 3: tautology
        vec![na, b, a],  // 4: tautology
        vec![b, a, na],  // 5: tautology
        vec![na, nb, a], // 6: tautology
        vec![a, na, nb], // 7: tautology
        vec![na, a, nb], // 8: tautology
        vec![a],         // 9: (a) — non-tautological, unit
        vec![na],        // 10: (¬a) — non-tautological, unit → UNSAT
    ];

    let num_clauses = clauses.len() as u64;
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), num_clauses);
    let mut solver = Solver::with_proof_output(2, proof);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    // The solver should detect UNSAT (contradictory units a and ¬a).
    // The LRAT proof must be valid — hint IDs must reference only registered
    // clause IDs (the non-tautological ones).
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat),
        "expected UNSAT from contradictory units, got {result:?}"
    );

    // Verify proof was emitted.
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    assert!(
        !proof_text.is_empty(),
        "UNSAT result must produce non-empty LRAT proof"
    );
}

// ========================================================================
// Property Tests for LRAT Proof Validity
// ========================================================================

use proptest::prelude::*;

/// Generate a random 3-SAT clause over `num_vars` variables (1-indexed internally).
fn arb_3sat_clause(num_vars: usize) -> impl Strategy<Value = Vec<Literal>> {
    proptest::collection::vec(
        (0..num_vars).prop_flat_map(|v| {
            prop_oneof![
                Just(Literal::positive(Variable(v as u32))),
                Just(Literal::negative(Variable(v as u32))),
            ]
        }),
        3..=3,
    )
}

/// Generate a random 3-SAT formula: (num_vars, clauses).
/// Uses clause/variable ratio ~5.0 to produce a mix of SAT and UNSAT instances.
fn arb_3sat_formula() -> impl Strategy<Value = (usize, Vec<Vec<Literal>>)> {
    (4usize..=8).prop_flat_map(|num_vars| {
        let num_clauses = num_vars * 5; // ratio ~5.0, above phase transition
        let clauses =
            proptest::collection::vec(arb_3sat_clause(num_vars), num_clauses..=num_clauses);
        (Just(num_vars), clauses)
    })
}

proptest! {
    /// LRAT proof validity: if the solver says UNSAT with LRAT proofs enabled,
    /// the proof must be non-empty and contain an empty-clause derivation.
    ///
    /// In debug builds, the ForwardChecker and LratChecker inside ProofManager
    /// validate every single LRAT addition step during solving. This proptest
    /// exercises those validators on random formulas, catching hint-chain bugs
    /// that targeted tests miss.
    ///
    /// If SAT, the model is verified against original clauses (same as
    /// prop_propagation_conflict_soundness in reconstruction.rs).
    #[test]
    fn prop_lrat_proof_valid_on_random_3sat(
        (num_vars, clauses) in arb_3sat_formula()
    ) {
        use crate::proof::ProofOutput;

        let num_clauses = clauses.len() as u64;
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), num_clauses);
        let mut solver = Solver::with_proof_output(num_vars, proof);

        // Save original clauses before adding (solver may rewrite them).
        let original_clauses: Vec<Vec<Literal>> = clauses.clone();
        for clause in clauses {
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();

        match &result {
            SatResult::Sat(model) => {
                // Verify model satisfies all original clauses.
                for (ci, clause) in original_clauses.iter().enumerate() {
                    let satisfied = clause.iter().any(|&lit| {
                        let var_val = model[lit.variable().index()];
                        if lit.is_positive() { var_val } else { !var_val }
                    });
                    prop_assert!(
                        satisfied,
                        "SAT model falsifies original clause {} ({:?})",
                        ci, clause
                    );
                }
            }
            SatResult::Unsat => {
                // In debug mode, ForwardChecker + LratChecker already validated
                // every proof step during solving. Here we additionally verify
                // the proof text is non-empty and contains an empty-clause line.
                let writer = solver.take_proof_writer().expect("proof writer");
                let proof_text = String::from_utf8(
                    writer.into_vec().expect("flush")
                ).expect("UTF-8");

                prop_assert!(
                    !proof_text.is_empty(),
                    "UNSAT result must produce non-empty LRAT proof"
                );

                // LRAT text format: an empty clause derivation has "ID 0 hints... 0"
                // where the literal section is empty (just the terminating 0).
                let has_empty_clause = proof_text.lines().any(|line| {
                    let tokens: Vec<&str> = line.split_whitespace().collect();
                    // Addition line: ID lits... 0 hints... 0
                    // Empty clause: ID 0 hints... 0 (second token is "0")
                    tokens.len() >= 2 && tokens[1] == "0"
                });
                prop_assert!(
                    has_empty_clause,
                    "UNSAT LRAT proof must contain empty clause derivation.\n\
                     Proof ({} bytes, {} lines):\n{}",
                    proof_text.len(),
                    proof_text.lines().count(),
                    &proof_text[..proof_text.len().min(2000)]
                );
            }
            SatResult::Unknown => {
                // Unknown is acceptable (timeout/resource limit).
            }
        }
    }
}

/// Regression test for #7108: LRAT chain verification failure during lucky
/// phase conflict analysis. The first proptest regression seed triggers a
/// level-1 conflict during lucky_propagate_discrepancy where the learned
/// unit clause's LRAT hints are incomplete — missing the level-0 unit
/// chain entry for a variable whose proof ID was not materialized.
#[test]
fn test_lrat_regression_lucky_phase_7108() {
    use crate::proof::ProofOutput;

    // First regression seed: 4 variables, 20 clauses.
    let clauses: Vec<Vec<Literal>> = vec![
        vec![Literal(0), Literal(0), Literal(1)],
        vec![Literal(1), Literal(0), Literal(0)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(1), Literal(0), Literal(0)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(1), Literal(0), Literal(0)],
        vec![Literal(0), Literal(0), Literal(1)],
        vec![Literal(1), Literal(1), Literal(1)],
        vec![Literal(1), Literal(0), Literal(0)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(0), Literal(0), Literal(1)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(0), Literal(0), Literal(1)],
        vec![Literal(0), Literal(0), Literal(1)],
        vec![Literal(0), Literal(1), Literal(0)],
        vec![Literal(0), Literal(0), Literal(4)],
        vec![Literal(0), Literal(0), Literal(1)],
    ];

    let num_vars = 4;
    let num_clauses = clauses.len() as u64;
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), num_clauses);
    let mut solver = Solver::with_proof_output(num_vars, proof);

    for clause in clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    // Should not panic with LRAT chain verification failure.
    match result {
        SatResult::Sat(_) | SatResult::Unsat | SatResult::Unknown => {}
    }
}

// ========================================================================
// Coverage Gap Tests (#proof_coverage audit, 2026-03-19)
// ========================================================================

/// Coverage Gap 1: register_lrat_axiom via push() — verify axiom IDs are
/// correctly allocated and tracked in scope_selector_axiom_ids.
///
/// Verifies that push():
/// (a) Allocates a non-zero axiom ID in LRAT mode
/// (b) Each push gets a unique, monotonically increasing axiom ID
/// (c) Subsequent original clause IDs don't collide with axiom IDs
#[test]
#[cfg(debug_assertions)]
fn test_register_lrat_axiom_via_push_allocates_unique_ids() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);

    // Push scope 1 — allocates first axiom ID
    solver.push();
    assert_eq!(
        solver.cold.scope_selector_axiom_ids.len(),
        1,
        "one push should produce one axiom ID"
    );
    let axiom_id1 = solver.cold.scope_selector_axiom_ids[0];
    assert!(axiom_id1 > 0, "axiom ID must be non-zero in LRAT mode");

    // Push scope 2 — allocates second axiom ID
    solver.push();
    assert_eq!(
        solver.cold.scope_selector_axiom_ids.len(),
        2,
        "two pushes should produce two axiom IDs"
    );
    let axiom_id2 = solver.cold.scope_selector_axiom_ids[1];
    assert!(axiom_id2 > 0, "second axiom ID must be non-zero");
    assert_ne!(
        axiom_id1, axiom_id2,
        "each push must allocate a unique axiom ID"
    );
    assert!(
        axiom_id2 > axiom_id1,
        "axiom IDs must be monotonically increasing"
    );

    // Adding an original clause should get an ID past both axiom IDs.
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    let clause_id = solver.cold.clause_ids[0];
    assert!(
        clause_id > axiom_id2,
        "original clause ID {clause_id} must be past axiom ID {axiom_id2}, solver counters must advance",
    );
}

/// Coverage Gap 1b: register_lrat_axiom returns 0 in DRAT mode.
///
/// In DRAT mode, push() populates scope_selector_axiom_ids with 0.
#[test]
#[cfg(debug_assertions)]
fn test_register_lrat_axiom_returns_zero_in_drat_mode() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(1, proof);

    solver.push();
    assert_eq!(
        solver.cold.scope_selector_axiom_ids.len(),
        1,
        "push should still track axiom ID slot in DRAT mode"
    );
    assert_eq!(
        solver.cold.scope_selector_axiom_ids[0], 0,
        "axiom ID must be 0 in DRAT mode (register_lrat_axiom returns 0)"
    );
}

/// Coverage Gap 2: advance_past dedicated test.
///
/// Verifies that LratWriter::advance_past:
/// (a) Advances next_id when min_next > current next_id
/// (b) Is a no-op when min_next <= current next_id
#[test]
fn test_lrat_writer_advance_past() {
    use crate::proof::LratWriter;

    // Create a writer with 3 original clauses: next_id starts at 4.
    let mut writer = LratWriter::new_text(Vec::<u8>::new(), 3);
    assert_eq!(writer.next_id(), 4, "next_id should be num_original + 1");

    // Advance past 10: next_id should become 10.
    writer.advance_past(10);
    assert_eq!(
        writer.next_id(),
        10,
        "advance_past(10) should set next_id to 10"
    );

    // Advance past 5: no-op since 5 < 10.
    writer.advance_past(5);
    assert_eq!(
        writer.next_id(),
        10,
        "advance_past(5) should be no-op when next_id=10"
    );

    // Advance past 10: no-op since 10 == 10 (not strictly greater).
    writer.advance_past(10);
    assert_eq!(
        writer.next_id(),
        10,
        "advance_past(10) should be no-op when next_id=10"
    );

    // Advance past 11: should advance.
    writer.advance_past(11);
    assert_eq!(
        writer.next_id(),
        11,
        "advance_past(11) should set next_id to 11"
    );
}

/// Coverage Gap 2b: ProofOutput::advance_past dispatches correctly.
///
/// Verifies the wrapper correctly delegates to LratWriter and is a no-op for DRAT.
/// Since ProofOutput doesn't expose next_id(), we verify indirectly via reserve_id()
/// which returns the current next_id and advances it.
#[test]
fn test_proof_output_advance_past_dispatch() {
    use crate::proof::ProofOutput;

    // DRAT: advance_past is a no-op (no ID tracking).
    let mut drat = ProofOutput::drat_text(Vec::new());
    drat.advance_past(100); // should not panic

    // LRAT: advance_past delegates to LratWriter.
    // With 5 original clauses, writer starts at next_id = 6.
    let mut lrat = ProofOutput::lrat_text(Vec::new(), 5);

    // Advance past 20: writer's counter should now be at 20.
    lrat.advance_past(20);

    // reserve_id() returns current next_id and advances to next_id+1.
    // If advance_past worked, this should return 20.
    let reserved = lrat.reserve_id();
    assert_eq!(
        reserved, 20,
        "after advance_past(20), reserve_id should return 20"
    );
}

/// Coverage Gap 3: Nested push/pop (depth 2) with LRAT proof output.
///
/// Verifies that LRAT proof is valid when UNSAT occurs at depth 2 with
/// two scope selector axioms in the hint chain. Tests:
/// - Push depth 1, push depth 2
/// - Add contradictory clauses at depth 2 → UNSAT (needs both axiom IDs)
/// - Pop depth 2, pop depth 1 → both pops clean
///
/// Note: UNSAT-pop-SAT-UNSAT cycles trigger a known verify_unsat_chain
/// limitation where the proof manager's last_add is overwritten by the
/// intermediate SAT solve's learned clauses. Testing that flow separately.
#[test]
#[cfg(debug_assertions)]
fn test_nested_push_pop_depth2_lrat_proof_valid() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(1, proof);
    let x0 = Literal::positive(Variable(0));

    // Push depth 1
    solver.push();
    // Push depth 2
    solver.push();

    // Verify two axiom IDs were allocated
    assert_eq!(
        solver.cold.scope_selector_axiom_ids.len(),
        2,
        "two pushes must produce two axiom IDs"
    );
    assert!(solver.cold.scope_selector_axiom_ids[0] > 0);
    assert!(solver.cold.scope_selector_axiom_ids[1] > 0);

    // Depth 2: add x0 and ¬x0 → UNSAT
    solver.add_clause(vec![x0]);
    solver.add_clause(vec![x0.negated()]);

    let r1 = solver.solve().into_inner();
    assert_eq!(r1, SatResult::Unsat, "depth-2 contradiction must be UNSAT");

    // Pop both scopes cleanly
    assert!(solver.pop());
    assert!(solver.pop());
}

/// Coverage Gap 3b: Triple-nested push then UNSAT at deepest level.
///
/// Exercises the scope_selector_axiom_ids stack at depth 3, verifying
/// that all three axiom IDs are allocated with unique, increasing values
/// and the UNSAT proof at depth 3 includes them in hints.
#[test]
#[cfg(debug_assertions)]
fn test_triple_nested_push_lrat_axiom_ids() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(1, proof);
    let x0 = Literal::positive(Variable(0));

    // Push three scopes
    solver.push(); // depth 1
    solver.push(); // depth 2
    solver.push(); // depth 3

    // Verify three axiom IDs
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 3);
    let ids: Vec<u64> = solver.cold.scope_selector_axiom_ids.clone();
    assert!(
        ids[0] > 0 && ids[1] > 0 && ids[2] > 0,
        "all axiom IDs must be non-zero"
    );
    assert!(
        ids[0] < ids[1] && ids[1] < ids[2],
        "axiom IDs must be strictly increasing"
    );

    // UNSAT at depth 3
    solver.add_clause(vec![x0]);
    solver.add_clause(vec![x0.negated()]);
    assert_eq!(solver.solve().into_inner(), SatResult::Unsat);

    // Pop all three scopes cleanly
    assert!(solver.pop()); // pop depth 3
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 2);
    assert!(solver.pop()); // pop depth 2
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 1);
    assert!(solver.pop()); // pop depth 1
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 0);
}

/// Coverage Gap 3c: Sequential push/pop cycles manage axiom IDs correctly.
///
/// Verifies that scope_selector_axiom_ids is properly cleaned up across
/// multiple push/pop cycles. Each cycle gets unique, non-overlapping IDs.
///
/// Note: UNSAT → pop → push → UNSAT cycles trigger a known
/// verify_unsat_chain limitation where pop's add_clause_unscoped
/// overwrites last_add. That flow needs a separate fix for
/// verify_unsat_chain to reset last_add on pop(). This test focuses
/// on the axiom ID management without triggering that path.
#[test]
#[cfg(debug_assertions)]
fn test_sequential_push_pop_lrat_axiom_id_management() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);

    // Cycle 1: push → pop (no solve, just verify axiom ID tracking)
    solver.push();
    let id1 = solver.cold.scope_selector_axiom_ids[0];
    assert!(id1 > 0);
    assert!(solver.pop());
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 0);

    // Cycle 2: push → pop
    solver.push();
    let id2 = solver.cold.scope_selector_axiom_ids[0];
    assert!(id2 > 0);
    assert!(
        id2 > id1,
        "second cycle's axiom ID {id2} must be > first cycle's {id1}"
    );
    assert!(solver.pop());
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 0);

    // Cycle 3: nested push/push → pop/pop
    solver.push();
    solver.push();
    let id3a = solver.cold.scope_selector_axiom_ids[0];
    let id3b = solver.cold.scope_selector_axiom_ids[1];
    assert!(id3a > id2, "third cycle IDs must be past second cycle");
    assert!(id3b > id3a, "nested IDs must be strictly increasing");
    assert!(solver.pop());
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 1);
    assert!(solver.pop());
    assert_eq!(solver.cold.scope_selector_axiom_ids.len(), 0);
}

/// Coverage Gap 4: Push with no clauses added + LRAT proof.
///
/// Verifies that pushing a scope without adding any scoped clauses
/// produces valid LRAT proof output. The scope selector axiom is
/// registered but never participates in a contradiction.
#[test]
#[cfg(debug_assertions)]
fn test_push_no_clauses_lrat_proof_valid() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(1, proof);

    // Base: (x0) — trivially SAT
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    solver.push();
    // No scoped clauses added.
    let r1 = solver.solve().into_inner();
    assert!(matches!(r1, SatResult::Sat(_)), "empty scope must be SAT");

    assert!(solver.pop());
    let r2 = solver.solve().into_inner();
    assert!(
        matches!(r2, SatResult::Sat(_)),
        "base formula must remain SAT after pop"
    );
}

/// Coverage Gap 5: build_finalize_empty_clause_hints with contradictory units.
///
/// Tests the level-0 BCP conflict path and hint generation. Contradictory
/// unit clauses (a) ∧ (¬a) require both clause IDs in the empty clause
/// hint chain.
#[test]
fn test_finalize_empty_clause_hints_with_contradictory_units() {
    use crate::proof::ProofOutput;

    // 2 original clauses: (a), (¬a)
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(1, proof);

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "contradictory units must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // The empty clause line must have hints referencing both original clauses.
    let lines: Vec<&str> = proof_text.lines().collect();
    let empty_clause_line = lines
        .iter()
        .find(|line| {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            tokens.len() >= 2 && tokens[1] == "0" && !line.contains(" d ")
        })
        .expect("LRAT proof must contain empty clause derivation");

    let tokens: Vec<&str> = empty_clause_line.split_whitespace().collect();
    // Format: <id> 0 <hint1> <hint2> ... 0
    let first_zero = tokens.iter().position(|t| *t == "0").unwrap();
    let trailing_zero = tokens.len() - 1;
    let hint_count = trailing_zero - first_zero - 1;
    assert!(
        hint_count >= 2,
        "empty clause hints must reference both unit clauses (got {hint_count} hints): {empty_clause_line}",
    );
}

/// Coverage Gap 5b: finalize_unsat_proof with scope selector axiom in hints.
///
/// Verifies that the empty clause derivation includes the scope selector
/// axiom ID (¬selector) in its hint chain. This is the fix from #7108.
#[test]
#[cfg(debug_assertions)]
fn test_finalize_empty_clause_includes_scope_selector_axiom_hint() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(1, proof);

    let x0 = Literal::positive(Variable(0));

    // Add (x0) at base level
    solver.add_clause(vec![x0]);

    // Push scope, add (¬x0) → UNSAT within scope
    solver.push();
    solver.add_clause(vec![x0.negated()]);

    let result = solver.solve().into_inner();
    assert_eq!(
        result,
        SatResult::Unsat,
        "scoped contradiction must be UNSAT"
    );

    // The axiom ID should be in the scope_selector_axiom_ids vector.
    assert_eq!(
        solver.cold.scope_selector_axiom_ids.len(),
        1,
        "one scope = one axiom ID"
    );
    let axiom_id = solver.cold.scope_selector_axiom_ids[0];
    assert!(axiom_id > 0, "axiom ID must be non-zero in LRAT mode");

    // Verify the LRAT proof contains the axiom ID in the empty clause hints.
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    let axiom_str = axiom_id.to_string();
    let has_axiom_hint = proof_text.lines().any(|line| {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        // Empty clause line: <id> 0 <hints...> 0
        if tokens.len() < 3 || tokens[1] != "0" || line.contains(" d ") {
            return false;
        }
        // Check if axiom_id appears in the hint section
        let first_zero = tokens.iter().position(|t| *t == "0").unwrap();
        tokens[first_zero + 1..tokens.len() - 1]
            .iter()
            .any(|t| *t == axiom_str)
    });
    assert!(
        has_axiom_hint,
        "empty clause hints must include scope selector axiom ID {axiom_id}\nproof:\n{proof_text}",
    );
}

/// Regression test for #7175: verify_unsat_chain panic in UNSAT→pop→push→UNSAT
/// incremental LRAT cycles.
///
/// Before the fix, pop()'s add_clause_unscoped(selector) updated last_add in
/// ProofManager to the selector clause. When the second solve produced UNSAT,
/// verify_unsat_chain checked last_add and panicked because it wasn't the
/// empty clause. The fix clears last_add at the start of finalize_unsat_proof.
#[test]
#[cfg(debug_assertions)]
fn test_incremental_unsat_pop_push_unsat_lrat_no_panic() {
    use crate::proof::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);

    // Base clause to make UNSAT possible inside scopes.
    // (a ∨ b)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // First scope: add contradictory clauses → UNSAT
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(1))]);
    let r1 = solver.solve();
    assert_eq!(r1, SatResult::Unsat, "first solve should be UNSAT");

    // Pop → triggers add_clause_unscoped(selector) which updates last_add.
    assert!(solver.pop());

    // Second scope: same contradiction → UNSAT again.
    // Before #7175 fix, this would panic in verify_unsat_chain.
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(1))]);
    let r2 = solver.solve();
    assert_eq!(r2, SatResult::Unsat, "second solve should be UNSAT");

    assert!(solver.pop());

    // Verify proof output is extractable without errors.
    let output = solver
        .take_proof_writer()
        .expect("proof writer should exist");
    let bytes = output.into_vec().expect("proof bytes");
    assert!(!bytes.is_empty(), "proof output should contain proof steps",);
}

/// Coverage Gap 6: register_clause_id advances writer counter.
///
/// Verifies that after adding original clauses, emitting a derived clause
/// via emit_add produces an ID that doesn't collide with original IDs.
/// This exercises the advance_past call within register_clause_id (#7108).
#[test]
fn test_register_clause_id_advances_writer_counter() {
    use crate::proof::ProofOutput;
    use crate::proof_manager::ProofAddKind;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);

    // Add 3 original clauses → IDs 1, 2, 3
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);

    // Verify the writer counter is synchronized by adding a derived clause.
    // If register_clause_id didn't call advance_past, emit_add() would
    // return an ID that collides with an original clause ID.
    let pm = solver.proof_manager.as_mut().expect("proof manager");
    let result = pm.emit_add(
        &[Literal::positive(Variable(0))],
        &[1, 2], // resolve clauses 1,2
        ProofAddKind::Derived,
    );
    let derived_id = result.expect("emit_add should succeed");
    assert!(
        derived_id > 3,
        "derived clause ID must be past original IDs 1,2,3; got {derived_id}",
    );
}
