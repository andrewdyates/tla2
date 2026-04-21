// Copyright (c) 2024-2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

//! STUB-ONLY: Creusot verification scaffolding for Z4 algorithms
//!
//! **STATUS: PLACEHOLDER** - These specifications are intentionally stub-only and
//! do not provide production verification coverage. They exist to establish the
//! Creusot toolchain pattern, not to prove solver correctness. The preconditions
//! trivially imply the postconditions, function bodies return `true`, and no
//! production Z4 types are imported. Real implementation would require specs on
//! actual `Clause`, `WatchList`, `Trail`, and `UnionFind` types.
//!
//! ## Specification Stubs (31 total)
//!
//! ### ITE Elimination (3 theorems)
//! - `exclusivity_sound`: Proves that `¬(v=t ∧ v=e)` is valid when `t ≠ e`
//! - `ite_condition_exhaustive`: Proves `c ∨ ¬c` (excluded middle)
//! - `ite_semantics`: Proves ITE returns correct branch based on condition
//!
//! ### Union-Find (7 theorems)
//! - `find_of_root_is_root`: Proves find(root) = root
//! - `root_is_own_representative`: Proves roots are self-representing
//! - `union_creates_equivalence`: Proves union creates shared representative
//! - `path_compression_sound`: Proves path compression preserves roots
//! - `equivalence_symmetric`: Proves find(x) = find(y) implies find(y) = find(x)
//! - `equivalence_transitive`: Proves transitivity of equivalence
//! - `parent_in_bounds`: Proves parent indices stay within bounds
//!
//! ### Watched Literals (10 theorems)
//! - `two_watched_invariant`: Every clause has exactly 2 watched literals
//! - `watch_symmetry`: If lit0 watches clause, clause is in lit0's watch list
//! - `two_pointer_bounds`: j <= i <= watch_len invariant
//! - `binary_clause_watch_correct`: Binary clauses watch both literals
//! - `unit_detection_complete`: If exactly one false, propagate the other
//! - `conflict_detection_complete`: If both false, return conflict
//! - `replacement_preserves_two_watched`: Swapping watches preserves invariant
//! - `xor_other_watched`: XOR gives the other watched literal
//! - `decrement_preserves_nonneg`: j > 0 implies j - 1 >= 0
//! - `truncation_valid`: Truncation bounds preserved
//!
//! ### Conflict Analysis (11 theorems)
//! - `one_uip_property`: Learned clause has exactly one literal at conflict level
//! - `counter_decrement_correct`: Counter decrements correctly during resolution
//! - `backtrack_level_is_second_highest`: Backtrack level is second-highest in clause
//! - `unit_learned_to_level_zero`: Unit learned clause backtracks to level 0
//! - `asserting_literal_first`: Asserting literal is first in learned clause
//! - `clause_unit_after_backtrack`: Learned clause is unit at backtrack level
//! - `resolution_preserves_implication`: Resolution produces valid implied clause
//! - `lbd_at_least_one`: LBD >= 1 when asserting literal set
//! - `reorder_preserves_clause`: Reordering for watches preserves clause content
//! - `clear_resets_state`: Clear resets analyzer to initial state
//! - `trail_walk_complete`: Trail walk finds all marked literals
//!
//! ## Usage
//!
//! Build with: `CREUSOT_RUSTC=/path/to/creusot-rustc cargo +nightly-2025-11-13 creusot`
//! Prove with: `why3find prove -P z3 verif/z4_verified_rlib/`
//!
//! ## Proof Status
//!
//! All 31 entries are stubs and discharge trivially via Z3 (~0.002s each).
//! Do not treat this crate as evidence of verified production behavior.

pub(crate) mod conflict;
pub(crate) mod ite_elimination;
pub(crate) mod union_find;
pub(crate) mod watched;
