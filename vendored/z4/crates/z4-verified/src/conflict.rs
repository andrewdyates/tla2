// Copyright (c) 2024-2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0
// SPDX-License-Identifier: Apache-2.0

//! Stub-only Conflict Analysis properties
//!
//! These theorems are placeholders for Creusot workflow validation only.
//!
//! This module contains stub specifications for key properties of 1-UIP conflict analysis:
//! 1. 1-UIP property: Exactly one literal at conflict level
//! 2. Backtrack level = second-highest level in learned clause
//! 3. Asserting literal is first in learned clause
//! 4. Learned clause is unit at backtrack level
//! 5. Resolution produces valid implied clause

use creusot_std::prelude::{ensures, logic, requires, Int};

/// STUB THEOREM: 1-UIP property
///
/// The learned clause has exactly one literal at the conflict level.
/// This is the First Unique Implication Point.
///
/// Proof: We start with counter = # lits at conflict level in conflict clause.
/// We decrement counter by resolving until counter == 0.
/// The last literal resolved is the UIP.
#[logic]
#[requires(literals_at_conflict_level == 1)]
#[requires(is_uip == (literals_at_conflict_level == 1))]
#[ensures(is_uip)]
pub fn one_uip_property(literals_at_conflict_level: Int, is_uip: bool) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Counter decrements correctly
///
/// When we resolve on a literal at the conflict level:
/// - Remove it from consideration (-1)
/// - Add antecedent literals at conflict level (+k)
/// - Net change: counter + k - 1
///
/// At UIP, counter becomes 0 because no new conflict-level literals added.
#[logic]
#[requires(old_counter >= 1)]
#[requires(new_lits_at_level >= 0)]
#[requires(new_counter == old_counter + new_lits_at_level - 1)]
#[ensures(new_counter >= 0 || (old_counter == 1 && new_lits_at_level == 0))]
pub fn counter_decrement_correct(
    old_counter: Int,
    new_counter: Int,
    new_lits_at_level: Int,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Backtrack level is second-highest
///
/// The backtrack level is the second-highest decision level among
/// literals in the learned clause. This ensures the clause becomes
/// unit after backtracking.
#[logic]
#[requires(max_level >= second_max_level)]
#[requires(second_max_level >= 0)]
#[requires(backtrack_level == second_max_level)]
#[ensures(backtrack_level <= max_level)]
pub fn backtrack_level_is_second_highest(
    max_level: Int,
    second_max_level: Int,
    backtrack_level: Int,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Unit learned clause backtracks to level 0
///
/// If the learned clause has only the asserting literal,
/// we must backtrack to level 0.
#[logic]
#[requires(clause_len == 1)]
#[requires(backtrack_level == if clause_len == 1 { 0 } else { backtrack_level })]
#[ensures(backtrack_level == 0)]
pub fn unit_learned_to_level_zero(clause_len: Int, backtrack_level: Int) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Asserting literal is first
///
/// The first literal in the learned clause is the asserting literal
/// (negation of UIP). This is required for efficient propagation.
#[logic]
#[requires(first_lit_is_asserting)]
#[ensures(first_lit_is_asserting)]
pub fn asserting_literal_first(first_lit_is_asserting: bool) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Learned clause is unit at backtrack level
///
/// After backtracking to backtrack_level:
/// - All literals except asserting are false (at levels > backtrack_level)
/// - Asserting literal is unassigned
/// - Therefore clause is unit
#[logic]
#[requires(all_others_false)]
#[requires(asserting_unassigned)]
#[requires(is_unit == (all_others_false && asserting_unassigned))]
#[ensures(is_unit)]
pub fn clause_unit_after_backtrack(
    all_others_false: bool,
    asserting_unassigned: bool,
    is_unit: bool,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Resolution preserves implication
///
/// If C1 implies C1' and C2 implies C2', then
/// resolving C1 and C2 on literal L implies resolving C1' and C2'.
///
/// This ensures learned clauses are valid consequences of original clauses.
#[logic]
#[requires(c1_valid)]
#[requires(c2_valid)]
#[requires(resolvent_from_c1_c2)]
#[requires(resolvent_valid == (c1_valid && c2_valid && resolvent_from_c1_c2))]
#[ensures(resolvent_valid)]
pub fn resolution_preserves_implication(
    c1_valid: bool,
    c2_valid: bool,
    resolvent_from_c1_c2: bool,
    resolvent_valid: bool,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: LBD >= 1 when asserting literal set
///
/// Literal Block Distance is at least 1 when we have an asserting literal,
/// because the asserting literal is at the conflict level (one distinct level).
#[logic]
#[requires(has_asserting_literal)]
#[requires(lbd >= 1)]
#[ensures(lbd >= 1)]
pub fn lbd_at_least_one(has_asserting_literal: bool, lbd: Int) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Reorder for watches preserves clause
///
/// Reordering the learned clause so the asserting literal and
/// a literal at backtrack level are at positions 0 and 1
/// preserves the clause content (just permutes).
#[logic]
#[requires(old_len == new_len)]
#[requires(is_permutation)]
#[ensures(new_len == old_len)]
pub fn reorder_preserves_clause(old_len: Int, new_len: Int, is_permutation: bool) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Clear resets analyzer state
///
/// After calling clear(), the analyzer is in initial state:
/// - No asserting literal
/// - Empty learned clause
/// - All seen flags cleared
#[logic]
#[requires(clear_called)]
#[requires(learned_len == 0)]
#[requires(!has_asserting)]
#[ensures(learned_len == 0)]
#[ensures(!has_asserting)]
pub fn clear_resets_state(clear_called: bool, learned_len: Int, has_asserting: bool) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Trail walk finds all seen literals
///
/// Walking backward through the trail and checking the seen flag
/// will find all literals that were marked during resolution.
#[logic]
#[requires(lit_was_marked)]
#[requires(trail_contains_lit)]
#[requires(will_be_found == (lit_was_marked && trail_contains_lit))]
#[ensures(will_be_found)]
pub fn trail_walk_complete(
    lit_was_marked: bool,
    trail_contains_lit: bool,
    will_be_found: bool,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

#[cfg(test)]
#[path = "conflict_tests.rs"]
mod tests;
