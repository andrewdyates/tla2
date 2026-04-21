// Copyright (c) 2024-2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0
// SPDX-License-Identifier: Apache-2.0

//! Stub-only Two-Watched Literal properties
//!
//! These theorems are placeholders for Creusot workflow validation only.
//!
//! This module contains stub specifications for key invariants of the two-watched literal scheme:
//! 1. Two-watched invariant: Every clause has exactly 2 watches
//! 2. Watch symmetry: If L watched in C, then C in L's watch list
//! 3. No missed propagation: Unit clauses detected
//! 4. Two-pointer bounds: j <= i during propagate iteration
//!
//! The two-watched literal scheme (Moskewicz et al., 2001) ensures:
//! - Only watch 2 literals per clause (not all)
//! - When a watched literal becomes false, find replacement or propagate
//! - If no replacement found, clause is unit or conflict

use creusot_std::prelude::{ensures, logic, requires, Int};

/// STUB THEOREM: Two-watched invariant
///
/// For any active clause C with len >= 2, exactly 2 literals are watched.
/// This is the core invariant maintained by the CDCL solver.
#[logic]
#[requires(clause_len >= 2)]
#[requires(num_watches == 2)]
#[ensures(num_watches == 2)]
pub fn two_watched_invariant(clause_len: Int, num_watches: Int) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Watch list membership symmetry
///
/// If literal L is watched in clause C at position P,
/// then clause C appears in L's watch list.
/// (The implementation maintains this invariant: whenever we add C to L's
/// watch list, we also set the watched position in C)
#[logic]
#[requires(clause_in_lit_watch_list == lit_watched_in_clause)] // Invariant: they're equivalent
#[ensures(lit_watched_in_clause ==> clause_in_lit_watch_list)]
pub fn watch_symmetry(lit_watched_in_clause: bool, clause_in_lit_watch_list: bool) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Binary clause watch correctness
///
/// For a binary clause (L1, L2):
/// - L1's watch list contains (clause_ref, blocker=L2)
/// - L2's watch list contains (clause_ref, blocker=L1)
#[logic]
#[requires(is_binary)]
#[requires(l1_watches_l2)] // L1's watch has blocker L2
#[requires(l2_watches_l1)] // L2's watch has blocker L1
#[ensures(l1_watches_l2 && l2_watches_l1)]
pub fn binary_clause_watch_correct(
    is_binary: bool,
    l1_watches_l2: bool,
    l2_watches_l1: bool,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Two-pointer bounds during propagate
///
/// During the in-place two-pointer iteration:
/// - j (write position) <= i (read position)
/// - Both j and i < watch_len
///
/// This is "Gap 8" from the verification audit.
#[logic]
#[requires(j <= i)]
#[requires(i <= watch_len)]
#[ensures(j <= watch_len)]
pub fn two_pointer_bounds(j: Int, i: Int, watch_len: Int) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Watch decrement preserves bounds
///
/// When we decrement j after finding a replacement literal:
/// j' = j - 1 implies j' >= 0 when j > 0
#[logic]
#[requires(j > 0)]
#[ensures(j - 1 >= 0)]
pub fn decrement_preserves_nonneg(j: Int) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Watch list truncation valid
///
/// After propagate loop, truncating to length j is valid
/// because j <= original watch_len and j >= 0.
#[logic]
#[requires(j <= original_len)]
#[requires(j >= 0)]
#[ensures(j >= 0 && j <= original_len)]
pub fn truncation_valid(j: Int, original_len: Int) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Unit propagation completeness
///
/// If a clause becomes unit (one unassigned literal, rest false),
/// the two-watched scheme detects it.
///
/// Proof: If both watched literals become false, we search for replacement.
/// If no unassigned literal found (all others false), clause is unit/conflict.
/// The is_unit flag is set when these conditions hold.
#[logic]
#[requires(watch0_false && watch1_false)]
#[requires(!replacement_found)]
#[requires(unassigned_count == 1)]
#[requires(is_unit == (watch0_false && watch1_false && !replacement_found && unassigned_count == 1))]
#[ensures(is_unit)]
pub fn unit_detection_complete(
    watch0_false: bool,
    watch1_false: bool,
    replacement_found: bool,
    unassigned_count: Int,
    is_unit: bool,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Conflict detection completeness
///
/// If a clause becomes empty (all literals false),
/// the two-watched scheme detects the conflict.
/// The is_conflict flag is set when these conditions hold.
#[logic]
#[requires(watch0_false && watch1_false)]
#[requires(!replacement_found)]
#[requires(unassigned_count == 0)]
#[requires(is_conflict == (watch0_false && watch1_false && !replacement_found && unassigned_count == 0))]
#[ensures(is_conflict)]
pub fn conflict_detection_complete(
    watch0_false: bool,
    watch1_false: bool,
    replacement_found: bool,
    unassigned_count: Int,
    is_conflict: bool,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: Watch replacement preserves invariant
///
/// When replacing a watch from position P to position K:
/// - Old watch (at P) is removed from false_lit's list
/// - New watch (at K) is added to lit_k's list
/// - Clause still has exactly 2 watches (2 - 1 + 1 = 2)
#[logic]
#[requires(old_watches == 2)]
#[requires(removed_one && added_one)]
#[requires(new_watches == old_watches - 1 + 1)] // 2 - 1 + 1 = 2
#[ensures(new_watches == 2)]
pub fn replacement_preserves_two_watched(
    old_watches: Int,
    new_watches: Int,
    removed_one: bool,
    added_one: bool,
) -> bool {
    // STUB: preconditions trivially imply postcondition, no real proof
    true
}

/// STUB THEOREM: XOR technique for other watched literal
///
/// Given clause lits[0..n] where lits[0] and lits[1] are watched:
/// other = lits[0] ^ lits[1] ^ false_lit
/// This computes the other watched literal branch-lessly.
///
/// Property: XOR(a, b, a) = b and XOR(a, b, b) = a
#[logic]
#[requires(false_lit == lit0 || false_lit == lit1)]
#[ensures(
    if false_lit == lit0 { result == lit1 }
    else { result == lit0 }
)]
pub fn xor_other_watched(lit0: Int, lit1: Int, false_lit: Int) -> Int {
    // STUB: preconditions trivially imply postcondition, no real proof
    // Select the other literal based on which one is false
    if false_lit == lit0 {
        lit1
    } else {
        lit0
    }
}

#[cfg(test)]
#[path = "watched_tests.rs"]
mod tests;
