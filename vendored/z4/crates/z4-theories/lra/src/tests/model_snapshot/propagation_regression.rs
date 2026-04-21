// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for the `last_simplex_feasible` simplex-skip guard (#6256).
///
/// When the simplex returns Unsat and no new bounds are asserted, the
/// simplex-skip optimization must NOT return Sat. The `last_simplex_feasible`
/// flag prevents this: when false, the skip path returns Unknown instead.
///
/// Without this guard, the simplex-skip would see `need_simplex == false`
/// (no bounds tightened, no new rows) and return Sat — a false positive.
#[test]
fn test_simplex_skip_after_unsat_does_not_return_sat_6256() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // Contradictory: x >= 10 and x <= 5
    let ge_ten = terms.mk_ge(x, ten);
    let le_five = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_ten, true); // x >= 10
    solver.assert_literal(le_five, true); // x <= 5

    // First check: simplex detects infeasibility.
    let result1 = solver.check();
    assert!(
        matches!(
            result1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "First check() should detect UNSAT for (x>=10, x<=5), got {result1:?}"
    );

    // Second check without any new assertions.
    // The simplex-skip sees need_simplex=false (no bounds tightened, no new rows).
    // Without last_simplex_feasible guard, this would return Sat (false positive).
    let result2 = solver.check();
    assert!(
        !matches!(result2, TheoryResult::Sat),
        "Second check() after UNSAT must NOT return Sat when no new bounds asserted. \
         Got {result2:?}. Bug: last_simplex_feasible guard not preventing false-SAT \
         on simplex-skip path (#6256)."
    );
}

/// Regression test: after check() returns Unsat, a subsequent check() without
/// new assertions must NOT return Sat — even through the simplex-skip path.
/// This tests the same invariant as test_simplex_skip_after_unsat_does_not_return_sat_6256
/// but uses a problem requiring the simplex (not just bound precheck) to detect
/// the infeasibility.
///
/// Pattern A from P2:142 strategic audit: the dirty flag and
/// last_simplex_feasible guard must work together to prevent false-SAT on
/// repeated check() calls without assert_literal().
#[test]
fn test_simplex_skip_after_infeasible_requires_pivots_6259() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x + y <= 5, x >= 10, y >= 0 — infeasible (x+y >= 10, but x+y <= 5)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_5 = terms.mk_le(sum, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_5);
    solver.register_atom(x_ge_10);
    solver.register_atom(y_ge_0);
    solver.assert_literal(sum_le_5, true);
    solver.assert_literal(x_ge_10, true);
    solver.assert_literal(y_ge_0, true);

    // First check: should detect infeasibility.
    let result1 = solver.check();
    assert!(
        !matches!(result1, TheoryResult::Sat),
        "First check() should detect infeasibility (x+y<=5, x>=10, y>=0), got {result1:?}"
    );

    // Second check without any new assertions.
    // Tests that the last_simplex_feasible guard and dirty flag prevent false-SAT.
    let result2 = solver.check();
    assert!(
        !matches!(result2, TheoryResult::Sat),
        "Second check() after infeasible state must NOT return Sat. \
         Got {result2:?}. Bug: dirty flag cleared after non-Sat result, !dirty \
         early return produces false-SAT without assert_literal()."
    );

    // Third check — same pattern, verifying stability.
    let result3 = solver.check();
    assert!(
        !matches!(result3, TheoryResult::Sat),
        "Third check() after infeasible state must NOT return Sat. Got {result3:?}."
    );
}

#[test]
fn test_compute_implied_bounds_keeps_fully_assigned_refinement_rows() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(sum_le_3);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);

    assert!(
        solver.unassigned_atom_count.iter().all(|&count| count == 0),
        "all atoms are assigned; this regression specifically targets the fully-assigned row case"
    );

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x + y <= 3, got {result:?}"
    );

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    let (lb, ub) = &solver.implied_bounds[x_var as usize];
    assert!(
        lb.is_none(),
        "x + y <= 3 with y = 0 must not derive a lower bound on x, got {lb:?}; row0={:?}; slack_bounds=({:?}, {:?}); x_status={:?}",
        solver.rows.first(),
        solver.vars[solver.rows[0].basic_var as usize]
            .lower
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[solver.rows[0].basic_var as usize]
            .upper
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[x_var as usize].status
    );
    let derived_upper = ub
        .as_ref()
        .is_some_and(|b| !b.strict && b.value.to_big() == BigRational::from(BigInt::from(3)));
    assert!(
        derived_upper,
        "fully-assigned rows must derive the upper bound x <= 3 (via row or eager derivation), got {ub:?}"
    );
}

#[test]
fn test_check_queues_bound_refinement_for_fully_assigned_row_without_x_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(sum_le_3);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x + y <= 3, got {result:?}"
    );

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    let (lb_dbg, ub_dbg) = &solver.implied_bounds[x_var as usize];
    assert!(
        lb_dbg.is_none(),
        "x + y <= 3 with y = 0 must not derive a lower bound on x, got {lb_dbg:?}; row0={:?}; slack_bounds=({:?}, {:?}); x_status={:?}",
        solver.rows.first(),
        solver.vars[solver.rows[0].basic_var as usize]
            .lower
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[solver.rows[0].basic_var as usize]
            .upper
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[x_var as usize].status
    );
    // The upper bound on x is derived via compute_implied_bounds (#6617).
    // The old inline eager_row_bound_derivation path was removed; bound
    // writing is now exclusively via the batch path after simplex.
    let has_upper = ub_dbg
        .as_ref()
        .is_some_and(|b| !b.strict && b.value.to_big() == three_value)
        || solver.vars[x_var as usize]
            .upper
            .as_ref()
            .is_some_and(|b| !b.strict && b.value == three_value);
    assert!(
        has_upper,
        "x should have upper bound <= 3 (via implied or eager derivation), got implied_ub={ub_dbg:?}, direct_ub={:?}",
        solver.vars[x_var as usize].upper.as_ref().map(|b| &b.value)
    );
    assert!(
        solver.propagation_dirty_vars.contains(&x_var),
        "derived bound should mark x dirty for propagation/refinement"
    );

    // After #6617, the inline path only queues refinement requests for slack
    // targets — it no longer writes bounds. Verify that either:
    // (a) a refinement request was queued (if x is a slack var), or
    // (b) compute_implied_bounds derived a direct bound on x.
    let refinements = solver.take_bound_refinements();
    let has_refinement = refinements
        .iter()
        .any(|req| req.variable == x && req.is_upper && req.bound_value == three_value);
    let has_direct = solver.vars[x_var as usize]
        .upper
        .as_ref()
        .is_some_and(|b| !b.strict && b.value == three_value);
    assert!(
        has_refinement || has_direct,
        "expected either bound refinement or direct bound x <= 3, got refinements={refinements:?}, direct_ub={:?}",
        solver.vars[x_var as usize].upper.as_ref().map(|b| &b.value)
    );
}

#[test]
fn test_lra_registered_x_atom_gets_propagated_from_fully_assigned_row_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_le_3 = terms.mk_le(x, three);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(x_le_3);
    solver.register_atom(sum_le_3);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x + y <= 3, got {result:?}"
    );
    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let pending_x = solver
        .pending_propagations
        .iter()
        .find(|pending| pending.propagation.literal == TheoryLit::new(x_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected pending propagation for x <= 3 after check(), got {:?}",
                solver.pending_propagations
            )
        });
    assert!(
        pending_x.propagation.reason.is_empty(),
        "row-derived implied propagation should defer materialization until propagate()"
    );
    let deferred = pending_x
        .deferred
        .expect("row-derived implied propagation should carry a deferred reason token");
    assert_eq!(
        deferred.var, x_var,
        "deferred token must target x's implied bound"
    );
    assert!(
        deferred.need_upper,
        "x <= 3 should defer the implied upper-bound explanation"
    );
    assert!(
        deferred.fallback_row_idx.is_some(),
        "deferred implied propagation should preserve a single-row fallback"
    );

    let propagations = solver.propagate();
    let propagated_x = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(x_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected x <= 3 to be propagated from the row-derived bound, got {propagations:?}"
            )
        });
    assert!(
        !propagated_x.reason.is_empty(),
        "row-derived propagation for x <= 3 must carry a non-empty reason"
    );
    assert!(
        propagated_x
            .reason
            .iter()
            .all(|lit| solver.asserted.get(&lit.term) == Some(&lit.value)),
        "propagation reasons must reference asserted literals, got {:?}",
        propagated_x.reason
    );
    assert!(
        solver.propagated_atoms.contains(&(x_le_3, true)),
        "successful propagate() should mark the literal as propagated"
    );
    assert!(
        solver.take_bound_refinements().is_empty(),
        "registered x <= 3 atom should be propagated, not queued as a fresh refinement"
    );
}

#[test]
fn test_collect_statistics_tracks_eager_and_deferred_reasons_issue_6617() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let neg_one = terms.mk_rational(BigRational::from(BigInt::from(-1)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_le_3 = terms.mk_le(x, three);
    let z_ge_0 = terms.mk_ge(z, zero);
    let z_ge_neg_one = terms.mk_ge(z, neg_one);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    for atom in [y_ge_0, y_le_0, x_le_3, z_ge_0, z_ge_neg_one, sum_le_3] {
        solver.register_atom(atom);
    }

    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);
    solver.assert_literal(z_ge_0, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT before draining propagations, got {result:?}"
    );

    let propagations = solver.propagate();
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(x_le_3, true)),
        "expected deferred row-backed propagation for x <= 3, got {propagations:?}"
    );
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(z_ge_neg_one, true)),
        "expected eager direct-bound propagation for z >= -1, got {propagations:?}"
    );

    let stats: HashMap<_, _> = TheorySolver::collect_statistics(&solver)
        .into_iter()
        .collect();
    assert_eq!(
        stats.get("lra_reasons_deferred").copied(),
        Some(1),
        "expected one deferred reason materialization"
    );
    assert_eq!(
        stats.get("lra_reasons_eager").copied(),
        Some(1),
        "expected one eager reason materialization"
    );
}

#[test]
fn test_propagate_runs_touched_row_batch_with_single_row_issue_6617() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let x0 = terms.mk_var("x0", Sort::Real);
    let s0 = terms.mk_var("s0", Sort::Real);

    let slack_lb = terms.mk_ge(s0, zero);
    let x0_le_3 = terms.mk_le(x0, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x0_le_3);

    let x_var = solver.ensure_var_registered(x0);
    let slack_var = solver.ensure_var_registered(s0);
    let max_var = x_var.max(slack_var) as usize;
    solver.vars = (0..=max_var).map(|_| VarInfo::default()).collect();
    solver.rows.clear();
    solver.col_index = vec![Vec::new(); max_var + 1];
    solver.basic_var_to_row.clear();
    solver.touched_rows.clear();
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    solver.vars[x_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: None,
        upper: None,
        status: Some(VarStatus::NonBasic),
    };
    solver.vars[slack_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: Some(Bound::new(
            BigRational::zero().into(),
            vec![slack_lb],
            vec![true],
            vec![BigRational::one()],
            false,
        )),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    };
    solver.asserted.insert(slack_lb, true);
    solver.rows.push(TableauRow::new(
        slack_var,
        vec![(x_var, BigRational::from(BigInt::from(-1)))],
        three_value,
    ));
    solver.col_index[x_var as usize].push(0);
    solver.basic_var_to_row.insert(slack_var, 0);
    solver.touched_rows.insert(0);
    solver.propagate_direct_touched_rows_pending = true;

    solver.last_simplex_feasible = true;

    let propagations = solver.propagate();
    let propagated_x0 = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(x0_le_3, true))
        .unwrap_or_else(|| {
            panic!("expected propagate() to batch touched rows into x0 <= 3, got {propagations:?}")
        });
    assert!(
        !propagated_x0.reason.is_empty(),
        "propagate-time touched-row derivation must carry a non-empty reason"
    );
    let x0_upper = solver.implied_bounds[x_var as usize]
        .1
        .as_ref()
        .expect("propagate() should materialize the row-derived x0 <= 3 bound");
    assert_eq!(x0_upper.value, Rational::from(3i32));
    assert!(
        !solver.propagate_direct_touched_rows_pending,
        "propagate() should consume the fresh direct-touch batch flag"
    );
}

#[test]
fn test_propagate_skips_cascade_only_rows_until_check_issue_6617() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let x0 = terms.mk_var("x0", Sort::Real);
    let s0 = terms.mk_var("s0", Sort::Real);

    let slack_lb = terms.mk_ge(s0, zero);
    let x0_le_3 = terms.mk_le(x0, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x0_le_3);

    let x_var = solver.ensure_var_registered(x0);
    let slack_var = solver.ensure_var_registered(s0);
    let max_var = x_var.max(slack_var) as usize;
    solver.vars = (0..=max_var).map(|_| VarInfo::default()).collect();
    solver.rows.clear();
    solver.col_index = vec![Vec::new(); max_var + 1];
    solver.basic_var_to_row.clear();
    solver.touched_rows.clear();
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    solver.vars[x_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: None,
        upper: None,
        status: Some(VarStatus::NonBasic),
    };
    solver.vars[slack_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: Some(Bound::new(
            BigRational::zero().into(),
            vec![slack_lb],
            vec![true],
            vec![BigRational::one()],
            false,
        )),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    };
    solver.asserted.insert(slack_lb, true);
    solver.rows.push(TableauRow::new(
        slack_var,
        vec![(x_var, BigRational::from(BigInt::from(-1)))],
        three_value,
    ));
    solver.col_index[x_var as usize].push(0);
    solver.basic_var_to_row.insert(slack_var, 0);
    solver.touched_rows.insert(0);
    solver.propagate_direct_touched_rows_pending = true;
    solver.last_simplex_feasible = true;

    let first = solver.propagate();
    assert!(
        first
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(x0_le_3, true)),
        "first propagate() should materialize x0 <= 3 from the fresh direct-touch row batch"
    );
    let cascade_rows = solver.touched_rows.clone();
    assert!(
        !cascade_rows.is_empty(),
        "first propagate() should leave cascade rows queued for the next check() batch"
    );

    let second = solver.propagate();
    assert!(
        second.is_empty(),
        "second propagate() should not rescan cascade-only rows without a fresh direct touch"
    );
    assert_eq!(
        solver.touched_rows, cascade_rows,
        "cascade-only rows should remain queued for check() instead of being drained by propagate()"
    );
    assert!(
        !solver.propagate_direct_touched_rows_pending,
        "fresh direct-touch flag should stay cleared after the initial propagate() batch"
    );
}

#[test]
fn test_check_during_propagate_interleaves_bound_cascade_issue_7719() {
    let mut terms = TermStore::new();
    let five_value = BigRational::from(BigInt::from(5));
    let five = terms.mk_rational(five_value.clone());

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);

    let x_le_y = terms.mk_le(x, y);
    let y_le_z = terms.mk_le(y, z);
    let x_ge_5 = terms.mk_ge(x, five);
    let five_again = terms.mk_rational(five_value.clone());
    let z_ge_5 = terms.mk_ge(z, five_again);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_le_y, y_le_z, x_ge_5, z_ge_5] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_le_y, true);
    solver.assert_literal(y_le_z, true);
    solver.assert_literal(x_ge_5, true);

    let result = solver.check_during_propagate();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x <= y <= z with x >= 5 should remain SAT during BCP, got {result:?}"
    );

    let z_var = *solver.term_to_var.get(&z).expect("z should be interned");
    let z_lower = solver.implied_bounds[z_var as usize]
        .0
        .as_ref()
        .expect("interleaved atom processing must derive z >= 5 in the same batched BCP check");
    assert_eq!(
        z_lower.value, five_value,
        "x <= y <= z and x >= 5 must imply z >= 5 during the same check"
    );
    assert!(
        solver.propagation_dirty_vars.contains(&z_var),
        "derived z bound should be marked dirty for propagation"
    );

    let propagations = solver.propagate();
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(z_ge_5, true)),
        "derived z >= 5 bound should reach propagate(); got {propagations:?}"
    );
}

/// Verify that propagate() refreshes simplex feasibility before running
/// touched-row analysis (#6987). When `bounds_tightened_since_simplex` is
/// true, propagate() must call dual_simplex() to update the basis before
/// compute_implied_bounds(). Without this refresh, row analysis runs
/// against a stale basis and may miss pivot-created opportunities.
///
/// Z3 reference: theory_lra.cpp:2254 — make_feasible() inside propagate_core().
#[test]
fn test_propagate_refreshes_simplex_before_touched_row_batch_issue_6987() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let x0 = terms.mk_var("x0", Sort::Real);
    let s0 = terms.mk_var("s0", Sort::Real);

    let slack_lb = terms.mk_ge(s0, zero);
    let x0_le_3 = terms.mk_le(x0, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x0_le_3);

    let x_var = solver.ensure_var_registered(x0);
    let slack_var = solver.ensure_var_registered(s0);
    let max_var = x_var.max(slack_var) as usize;
    solver.vars = (0..=max_var).map(|_| VarInfo::default()).collect();
    solver.rows.clear();
    solver.col_index = vec![Vec::new(); max_var + 1];
    solver.basic_var_to_row.clear();
    solver.touched_rows.clear();
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    solver.vars[x_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: None,
        upper: None,
        status: Some(VarStatus::NonBasic),
    };
    solver.vars[slack_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: Some(Bound::new(
            BigRational::zero().into(),
            vec![slack_lb],
            vec![true],
            vec![BigRational::one()],
            false,
        )),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    };
    solver.asserted.insert(slack_lb, true);
    solver.rows.push(TableauRow::new(
        slack_var,
        vec![(x_var, BigRational::from(BigInt::from(-1)))],
        three_value,
    ));
    solver.col_index[x_var as usize].push(0);
    solver.basic_var_to_row.insert(slack_var, 0);
    solver.touched_rows.insert(0);
    solver.propagate_direct_touched_rows_pending = true;

    // Key difference from the #6617 test: set bounds_tightened_since_simplex
    // to true, simulating a BCP bound tightening that happened after the last
    // check(). The old code would skip row analysis because it never called
    // dual_simplex() during propagate(). The new code (#6987) calls
    // refresh_simplex_for_propagate() first.
    solver.bounds_tightened_since_simplex = true;
    solver.last_simplex_feasible = true;

    let propagations = solver.propagate();
    // After the simplex refresh, the touched row should derive x0 <= 3.
    let found_x0_le_3 = propagations
        .iter()
        .any(|prop| prop.literal == TheoryLit::new(x0_le_3, true));
    assert!(
        found_x0_le_3,
        "propagate() should derive x0 <= 3 after simplex refresh (#6987), got {propagations:?}"
    );
    // bounds_tightened_since_simplex should be cleared by the refresh.
    assert!(
        !solver.bounds_tightened_since_simplex,
        "refresh_simplex_for_propagate should clear bounds_tightened_since_simplex"
    );
}

#[test]
fn test_register_atom_tracks_compound_wakeups_separately_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("compound atom should create exactly one slack variable");

    assert!(
        solver
            .atom_index
            .get(&x_var)
            .is_none_or(|atoms| atoms.iter().all(|atom| atom.term != sum_le_3)),
        "compound atom must not pollute direct-bound index for x"
    );
    assert!(
        solver
            .atom_index
            .get(&y_var)
            .is_none_or(|atoms| atoms.iter().all(|atom| atom.term != sum_le_3)),
        "compound atom must not pollute direct-bound index for y"
    );
    for wake_key in [x_var, y_var, slack] {
        assert!(
            solver
                .compound_use_index
                .get(&wake_key)
                .is_some_and(|atoms| atoms
                    .iter()
                    .any(|entry| { entry.term == sum_le_3 && entry.slack == slack })),
            "compound atom must be queued under wake key {wake_key}"
        );
    }
}

#[test]
fn test_compound_propagation_uses_compound_use_index_without_var_to_atoms_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_le_3 = terms.mk_le(x, three);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(x_le_3);
    solver.register_atom(sum_le_3);
    solver.var_to_atoms.clear();

    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(x_le_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x <= 3, got {result:?}"
    );
    assert!(
        solver
            .pending_propagations
            .iter()
            .any(|pending| pending.propagation.literal == TheoryLit::new(sum_le_3, true)),
        "compound wakeup helper should queue x + y <= 3 even when var_to_atoms is empty"
    );

    let propagations = solver.propagate();
    let propagated_sum = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected x + y <= 3 to be propagated from compound_use_index, got {propagations:?}"
            )
        });
    assert!(
        !propagated_sum.reason.is_empty(),
        "compound propagation must carry a non-empty reason"
    );
}

#[test]
fn test_compound_same_expression_stronger_atom_propagates_weaker_atom_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_1);
    solver.register_atom(sum_le_3);

    solver.assert_literal(sum_le_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after asserting stronger compound atom, got {result:?}"
    );

    let pending = solver
        .pending_propagations
        .iter()
        .find(|pending| pending.propagation.literal == TheoryLit::new(sum_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "same-expression stronger compound atom should eagerly imply the weaker atom, got {:?}",
                solver.pending_propagations
            )
        });
    assert_eq!(
        pending.propagation.reason,
        vec![TheoryLit::new(sum_le_1, true)],
        "weaker same-expression compound propagation should use the stronger asserted atom as its direct witness"
    );

    let propagations = solver.propagate();
    let propagated_sum = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected x + y <= 3 to propagate from the stronger same-expression atom, got {propagations:?}"
            )
        });
    assert_eq!(
        propagated_sum.reason,
        vec![TheoryLit::new(sum_le_1, true)],
        "propagate() should preserve the direct stronger-atom witness"
    );
}

#[test]
fn test_compute_expr_interval_preserves_open_zero_lower_endpoint_6582() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    let x_gt_0 = terms.mk_gt(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.intern_var(x);
    let y_var = solver.intern_var(y);
    solver.assert_var_bound(
        x_var,
        BigRational::zero().into(),
        BoundType::Lower,
        true,
        x_gt_0,
        true,
        BigRational::from(BigInt::from(1)).into(),
    );
    solver.assert_var_bound(
        y_var,
        BigRational::zero().into(),
        BoundType::Lower,
        false,
        y_ge_0,
        true,
        BigRational::from(BigInt::from(1)).into(),
    );

    let mut expr = LinearExpr::zero();
    expr.add_term(x_var, BigRational::from(BigInt::from(1)));
    expr.add_term(y_var, BigRational::from(BigInt::from(1)));
    let (lb, ub) = solver.compute_expr_interval(&expr);
    let boundary = lb.expect("x > 0 and y >= 0 should produce a finite lower endpoint");
    assert_eq!(
        boundary.value,
        BigRational::zero().into(),
        "strict boundary endpoint should stay at the zero boundary"
    );
    assert!(
        boundary.strict,
        "strictness must be preserved so the zero lower endpoint remains open (#6582)"
    );
    assert!(
        ub.is_none(),
        "no upper bounds were asserted, so x + y should remain unbounded above"
    );
}

#[test]
fn test_compound_interval_open_zero_lower_propagates_false_upper_atom_6582() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    let x_gt_0 = terms.mk_gt(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_0 = terms.mk_le(sum, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_0);
    solver.assert_literal(x_gt_0, true);
    solver.assert_literal(y_ge_0, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x > 0, y >= 0 should stay SAT before propagating x + y <= 0, got {result:?}"
    );

    let propagations = solver.propagate();
    let propagated = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_le_0, false))
        .unwrap_or_else(|| {
            panic!("expected x > 0 and y >= 0 to imply not(x + y <= 0), got {propagations:?}")
        });
    assert!(
        !propagated.reason.is_empty(),
        "strict open-zero contradiction must carry reasons"
    );
}

#[test]
fn test_compound_interval_open_zero_upper_propagates_false_lower_atom_6582() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    let x_lt_0 = terms.mk_lt(x, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_ge_0 = terms.mk_ge(sum, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_ge_0);
    solver.assert_literal(x_lt_0, true);
    solver.assert_literal(y_le_0, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x < 0, y <= 0 should stay SAT before propagating x + y >= 0, got {result:?}"
    );

    let propagations = solver.propagate();
    let propagated = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_ge_0, false))
        .unwrap_or_else(|| {
            panic!("expected x < 0 and y <= 0 to imply not(x + y >= 0), got {propagations:?}")
        });
    assert!(
        !propagated.reason.is_empty(),
        "strict open-zero contradiction must carry reasons"
    );
}
