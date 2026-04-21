// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;

fn vd(levels: &[u32]) -> Vec<VarData> {
    levels
        .iter()
        .map(|&l| VarData {
            level: l,
            ..VarData::UNASSIGNED
        })
        .collect()
}

#[test]
fn test_conflict_analyzer_basic() {
    let mut analyzer = ConflictAnalyzer::new(5);
    let mut var_data = vd(&[0, 0, 0, 0, 0]);

    // Mark some variables as seen
    analyzer.mark_seen(0, &mut var_data);
    analyzer.mark_seen(2, &mut var_data);
    assert!(analyzer.is_seen(0, &var_data));
    assert!(!analyzer.is_seen(1, &var_data));
    assert!(analyzer.is_seen(2, &var_data));

    // Clear and verify
    analyzer.clear(&mut var_data);
    assert!(!analyzer.is_seen(0, &var_data));
    assert!(!analyzer.is_seen(2, &var_data));
}

#[test]
fn test_learned_clause_construction() {
    let mut analyzer = ConflictAnalyzer::new(5);

    // Build a learned clause
    analyzer.add_to_learned(Literal::negative(Variable(1)));
    analyzer.add_to_learned(Literal::positive(Variable(2)));
    analyzer.set_asserting_literal(Literal::negative(Variable(0)));

    let var_data = vd(&[1, 2, 1, 0, 0]); // Levels for variables 0-4
    let bt_level = analyzer.compute_backtrack_level(&var_data);
    let lbd = analyzer.compute_lbd(&var_data);

    assert_eq!(bt_level, 2); // Highest level among non-asserting literals
                             // CaDiCaL convention: glue = distinct_levels - 1. Levels {1, 2} → glue = 1.
    assert_eq!(lbd, 1);

    let result = analyzer.get_result(bt_level, lbd);
    assert_eq!(result.learned_clause.len(), 3);
    assert_eq!(result.learned_clause[0], Literal::negative(Variable(0)));
}

#[test]
fn test_unit_learned_clause() {
    let mut analyzer = ConflictAnalyzer::new(3);

    // Only an asserting literal (unit learned clause)
    analyzer.set_asserting_literal(Literal::positive(Variable(0)));

    let var_data = vd(&[1, 0, 0]);
    let bt_level = analyzer.compute_backtrack_level(&var_data);

    assert_eq!(bt_level, 0); // Unit clause backtracks to level 0
}

#[test]
fn test_reorder_for_watches() {
    let mut clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ];
    let var_data = vd(&[3, 1, 2]);
    reorder_for_watches(&mut clause, &var_data, 2);
    // Variable(2) at level 2 should be swapped to position 1
    assert_eq!(clause[1], Literal::positive(Variable(2)));
    assert_eq!(clause.len(), 3);
}

#[test]
fn test_compact_clears_seen_state_regression() {
    let mut analyzer = ConflictAnalyzer::new(8);
    let mut var_data = vd(&[0; 8]);
    analyzer.mark_seen(1, &mut var_data);
    analyzer.mark_seen(6, &mut var_data);
    analyzer.clear(&mut var_data);

    // Reproduce the stale-prefix shape: seen bit set in var_data without
    // matching sparse-clear bookkeeping.
    var_data[1].set_seen(true);
    analyzer.seen_to_clear.clear();
    #[cfg(debug_assertions)]
    {
        analyzer.seen_true_count = 0;
    }

    // Compact now clears seen flags in var_data AND resets bookkeeping.
    analyzer.compact(&mut var_data);
    let mut var_data = vd(&[0; 4]);

    assert!(analyzer.seen_to_clear.is_empty());
    #[cfg(debug_assertions)]
    assert_eq!(analyzer.seen_true_count, 0);

    // Must remain safe for normal mark/unmark/clear lifecycle after compact.
    analyzer.mark_seen(1, &mut var_data);
    analyzer.unmark_seen(1, &mut var_data);
    analyzer.clear(&mut var_data);
    assert!(!analyzer.is_seen(1, &var_data));
}

#[test]
fn test_compact_resets_analysis_buffers() {
    let mut analyzer = ConflictAnalyzer::new(6);
    let mut var_data = vd(&[1, 2, 3, 0, 0, 0]);
    analyzer.mark_seen(0, &mut var_data);
    analyzer.add_to_learned(Literal::positive(Variable(2)));
    analyzer.set_asserting_literal(Literal::negative(Variable(1)));
    analyzer.add_to_chain(42);
    let _ = analyzer.compute_lbd(&var_data);

    analyzer.compact(&mut var_data);

    // Seen marks cleared by compact() via sparse-clear
    assert!(analyzer.seen_to_clear.is_empty());
    #[cfg(debug_assertions)]
    assert_eq!(analyzer.seen_true_count, 0);
    assert_eq!(analyzer.learned_count(), 0);
    assert!(analyzer.asserting_lit.is_none());
    assert!(analyzer.resolution_chain.is_empty());
    assert!(analyzer.lbd_seen.is_empty());
    assert!(analyzer.lbd_to_clear.is_empty());
    assert!(analyzer.clause_buf.is_empty());
}

/// Test reorder_for_watches fallback path: no literal at exact backtrack level.
/// When no literal matches backtrack_level, position 1 should get the
/// highest-level literal among positions 2..len (2WL correctness).
#[test]
fn test_reorder_for_watches_fallback_highest_level() {
    // clause[0] at level 5 (asserting), clause[1] at level 1,
    // clause[2] at level 3, clause[3] at level 4.
    // Backtrack level is 2, which NO literal matches.
    // Fallback: swap position 1 with the highest non-asserting level (4, at index 3).
    let mut clause = vec![
        Literal::positive(Variable(0)), // level 5
        Literal::positive(Variable(1)), // level 1
        Literal::positive(Variable(2)), // level 3
        Literal::positive(Variable(3)), // level 4
    ];
    let var_data = vd(&[5, 1, 3, 4]);
    reorder_for_watches(&mut clause, &var_data, 2);

    // Position 1 should now be Variable(3) at level 4 (highest non-asserting)
    assert_eq!(
        clause[1],
        Literal::positive(Variable(3)),
        "fallback should place highest-level literal at position 1"
    );
    // Position 0 should be unchanged (asserting literal)
    assert_eq!(clause[0], Literal::positive(Variable(0)));
    assert_eq!(clause.len(), 4);
}

/// Test reorder_for_watches when position 1 already has the highest level.
/// No swap should occur.
#[test]
fn test_reorder_for_watches_fallback_already_correct() {
    let mut clause = vec![
        Literal::positive(Variable(0)), // level 5
        Literal::positive(Variable(1)), // level 4 (already highest of rest)
        Literal::positive(Variable(2)), // level 2
        Literal::positive(Variable(3)), // level 1
    ];
    let var_data = vd(&[5, 4, 2, 1]);
    let clause_before = clause.clone();
    reorder_for_watches(&mut clause, &var_data, 3); // no level-3 match
                                                    // Position 1 was already the highest among non-asserting, no swap needed
    assert_eq!(clause, clause_before);
}

/// Test compute_lbd_for_clause counts ALL levels (no subtraction).
/// This differs from compute_lbd which subtracts 1 (CaDiCaL convention).
#[test]
fn test_compute_lbd_for_clause_counts_all_levels() {
    let mut analyzer = ConflictAnalyzer::new(5);
    let var_data = vd(&[0, 1, 2, 1, 3]);

    // Clause: vars 0,1,2,3 at levels 0,1,2,1 → 3 distinct levels {0,1,2}
    let lits = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ];
    let lbd = analyzer.compute_lbd_for_clause(&lits, &var_data);
    assert_eq!(
        lbd, 3,
        "compute_lbd_for_clause should count all distinct levels"
    );

    // Compare with compute_lbd which subtracts 1:
    // Set up same learned clause
    analyzer.set_asserting_literal(Literal::positive(Variable(0)));
    analyzer.add_to_learned(Literal::positive(Variable(1)));
    analyzer.add_to_learned(Literal::positive(Variable(2)));
    analyzer.add_to_learned(Literal::positive(Variable(3)));
    let learned_lbd = analyzer.compute_lbd(&var_data);
    // compute_lbd counts {0,1,2} = 3 distinct levels, then subtracts 1 → 2
    assert_eq!(
        learned_lbd, 2,
        "compute_lbd should subtract 1 from level count"
    );
    assert_eq!(
        lbd,
        learned_lbd + 1,
        "compute_lbd_for_clause = compute_lbd + 1 for same literals"
    );
}

/// Test compute_lbd_for_clause returns at least 1 even for empty clause.
#[test]
fn test_compute_lbd_for_clause_min_one() {
    let mut analyzer = ConflictAnalyzer::new(3);
    let var_data = vd(&[0, 1, 2]);
    let lbd = analyzer.compute_lbd_for_clause(&[], &var_data);
    assert_eq!(lbd, 1, "empty clause should have LBD 1 (min clamped)");
}

/// Test reorder_for_watches with binary clause (len == 2).
/// Position 1 should remain as-is since there's nothing to search in 2..len.
#[test]
fn test_reorder_for_watches_binary_clause() {
    let mut clause = vec![
        Literal::positive(Variable(0)), // level 3
        Literal::positive(Variable(1)), // level 1
    ];
    let var_data = vd(&[3, 1]);
    let clause_before = clause.clone();
    reorder_for_watches(&mut clause, &var_data, 1);
    // Binary clause: the loop `2..clause.len()` is empty, fallback also
    // iterates `2..2` (empty). No swap occurs.
    assert_eq!(
        clause, clause_before,
        "binary clause should not be modified"
    );
}
