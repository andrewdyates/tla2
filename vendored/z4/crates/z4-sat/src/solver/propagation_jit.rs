// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hybrid BCP propagation: JIT-compiled path for static clauses + 2WL for learned.
//!
//! FC-SAT (Formula-Compiled SAT) compiles irredundant clauses into native
//! propagation functions via custom assembler JIT. This eliminates the watch list
//! indirection and blocker checks for the static portion of the formula.
//!
//! The hybrid approach:
//! 1. **Compiled path**: All irredundant (original) clauses are compiled into
//!    a native function that directly reads `vals[]` and enqueues propagations.
//! 2. **2WL path**: Learned (redundant) clauses still use traditional watched
//!    literals, since they are added/deleted dynamically during search.

use super::*;
#[allow(unused_imports)]
use crate::solver_log::solver_log;

impl Solver {
    /// Hybrid BCP: interleaved JIT + standard 2WL propagation.
    ///
    /// JIT handles compiled static clauses (len 3-5). Standard 2WL handles
    /// learned clauses and uncompiled static clauses (binary + len 6+).
    /// Every trail literal gets both treatments via separate head pointers
    /// (`jit_qhead` and `qhead`), ensuring no propagations are missed even
    /// when compiled clause watches are detached from 2WL.
    ///
    /// Loop structure:
    /// 1. JIT-scan all unprocessed literals (jit_qhead → trail.len())
    /// 2. Standard BCP processes all from qhead (handles learned + long static)
    /// 3. If standard BCP enqueued new literals, loop back so JIT scans them
    pub(super) fn propagate_hybrid(&mut self) -> Option<ClauseRef> {
        loop {
            // Phase 1: JIT-scan any trail literals not yet JIT-processed.
            // The compiled function processes all static clauses containing the
            // trigger literal, writing propagations to a staging buffer and vals[]
            // inline. batch_enqueue_from_jit() then completes each propagation by
            // writing var_data, trail, and phase (vals[] already set by JIT, #8126).
            while self.jit_qhead < self.trail.len() {
                let p = self.trail[self.jit_qhead];
                self.jit_qhead += 1;

                if let Some(conflict_id) = self.jit_propagate_literal(p) {
                    return Some(ClauseRef(conflict_id));
                }
            }

            // Phase 2: Standard BCP handles learned + uncompiled static clauses.
            // This advances qhead internally and may enqueue new literals.
            let trail_before = self.trail.len();
            if let Some(conflict) = self.search_propagate_standard() {
                return Some(conflict);
            }

            // If standard BCP found no new propagations, we're done.
            // If it did enqueue new literals, loop back so JIT scans them too.
            if self.trail.len() == trail_before {
                break;
            }
        }

        None
    }

    /// Run JIT-compiled propagation for a single literal.
    ///
    /// Returns `Some(arena_offset)` if a conflict clause is found.
    /// Returns `None` if all static clauses are satisfied or propagated.
    ///
    /// The JIT function reads the solver's `vals[]` array directly (literal-indexed)
    /// and writes new propagations into a staging buffer. The JIT also writes
    /// vals[] inline so subsequent clauses in the same function see the assignment.
    ///
    /// After the JIT returns, vals[] are already correct for all staged
    /// propagations. `batch_enqueue_from_jit()` writes var_data, trail, and
    /// phase WITHOUT redundantly re-writing vals[]. This eliminates the
    /// undo-and-replay overhead (#8126):
    /// - Removes 2 undo stores per propagation (zeroing vals[lit] and vals[~lit])
    /// - Removes 2 redundant vals[] stores in the replay (already set by JIT)
    ///
    /// Correctness argument for eliminating the undo step:
    /// The JIT checks `vals[lit] == 0` before propagating, so it only enqueues
    /// genuinely unassigned variables. After enqueuing, it sets `vals[lit] = 1`
    /// and `vals[~lit] = -1`, which prevents later clauses in the same function
    /// from re-propagating the same variable. Therefore:
    /// - The staging trail contains only unique, newly-propagated variables
    /// - All vals[] writes by JIT are the exact values that enqueue() would set
    /// - batch_enqueue_from_jit() completes each enqueue by writing var_data/trail/phase
    fn jit_propagate_literal(&mut self, p: Literal) -> Option<u32> {
        let compiled = self.compiled_formula.as_ref()?;

        let var = p.variable().index();
        let polarity = if p.is_positive() { 0 } else { 1 };

        if !compiled.has_function(var, polarity) {
            return None;
        }

        let num_vars = self.num_vars;

        // Ensure staging buffers are sized correctly.
        if self.jit_staging_trail.len() < num_vars * 4 {
            self.jit_staging_trail.resize(num_vars * 4, 0);
        }
        if self.jit_staging_reasons.len() < num_vars {
            self.jit_staging_reasons.resize(num_vars, 0);
        }

        let mut staging_trail_len: u32 = 0;
        let mut conflict: u32 = 0;

        // Pass the solver's vals[] directly -- JIT codegen uses literal indexing
        // (vals[lit_encoded]) which matches the solver's layout exactly.
        let mut ctx = z4_jit::PropagationContext {
            vals: self.vals.as_mut_ptr(),
            trail: self.jit_staging_trail.as_mut_ptr(),
            trail_len: &mut staging_trail_len,
            conflict: &mut conflict,
            levels: std::ptr::null(),
            reasons: self.jit_staging_reasons.as_mut_ptr(),
            decision_level: self.decision_level,
            _pad0: 0,
            guards: self.jit_guards.as_ptr(),
        };

        // SAFETY: All pointer fields in ctx satisfy z4_jit::propagate's requirements:
        //   - vals: points to self.vals (Vec<i8>, size = num_vars * 2), valid and
        //     mutable. JIT code accesses vals[lit_encoded] where lit_encoded < num_vars * 2.
        //   - trail: points to self.jit_staging_trail (resized to num_vars * 4 above),
        //     sufficient for any number of propagations within a single function call.
        //   - trail_len: points to stack-local staging_trail_len, valid for the call duration.
        //   - conflict: points to stack-local conflict, valid for the call duration.
        //   - levels: null pointer (not accessed by compiled propagation code).
        //   - reasons: points to self.jit_staging_reasons (resized to num_vars above).
        //     JIT writes reasons[var] where var < num_vars.
        //   - guards: points to self.jit_guards backing Vec<u8> via ClauseGuards::as_ptr().
        //     Valid as long as jit_guards is not reallocated (no growth during propagation).
        // No concurrent access: the solver is single-threaded.
        // The compiled formula (and its backing ExecutableMemory) is alive via self.compiled_formula.
        #[allow(unsafe_code)]
        let has_conflict = unsafe { z4_jit::propagate(compiled, var, polarity, &mut ctx) };

        // NO undo step -- vals[] written by JIT are correct (#8126).
        // The JIT sets vals[lit]=1 and vals[~lit]=-1 for each propagation.
        // These are the exact values that enqueue_bcp() would write, so we
        // keep them and use batch_enqueue_from_jit() which skips vals[] writes.

        // Batch-enqueue: write var_data, trail, phase for all staged propagations.
        // The staging trail contains only unique, genuinely new propagations
        // (JIT checks vals[] before propagating; intra-function propagations
        // set vals[] immediately, preventing duplicates from later clauses).
        // All entries are processed unconditionally -- no var_is_assigned()
        // check needed since JIT deduplicates via vals[].
        let jit_enqueued = self.batch_enqueue_from_jit(staging_trail_len as usize);
        self.stats.jit_propagations += jit_enqueued;

        if has_conflict {
            self.stats.jit_conflicts += 1;
            solver_log!(
                self,
                "JIT conflict: var={} pol={} clause_id={}",
                var,
                polarity,
                conflict
            );
            return Some(conflict);
        }

        None
    }
}
