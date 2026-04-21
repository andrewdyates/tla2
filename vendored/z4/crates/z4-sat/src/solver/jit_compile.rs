// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT compilation of static (irredundant) clauses into native BCP functions.
//!
//! Called once after initial clause loading and preprocessing completes.
//! Collects all non-learned, non-garbage clauses from the arena, groups them
//! by watched variable, and compiles per-variable propagation functions via
//! the `z4-jit` crate (custom assembler backend).

use super::*;

impl Solver {
    /// Compile static clauses into native propagation functions.
    ///
    /// Called once after initial clause loading and preprocessing. Collects
    /// all irredundant (non-learned), non-garbage clauses and passes them
    /// to the JIT compiler.
    ///
    /// Returns the number of clauses compiled.
    pub(crate) fn compile_static_clauses(&mut self) -> Result<usize, String> {
        // Benchmark override: Z4_NO_JIT=1 disables JIT compilation for A/B testing.
        if std::env::var("Z4_NO_JIT").is_ok() {
            tracing::info!("JIT: disabled by Z4_NO_JIT environment variable");
            return Ok(0);
        }

        // Skip JIT compilation for small formulas where compile overhead > benefit.
        // Conservative threshold: JIT compile cost is ~1-5ms per function.
        // Formulas with <1000 vars solve in <100ms — compilation dominates.
        const MIN_VARS_FOR_JIT: usize = 1_000;
        const MIN_TERNARY_CLAUSES: usize = 500;

        if self.num_vars < MIN_VARS_FOR_JIT {
            tracing::info!(num_vars = self.num_vars, "JIT: skipped (formula too small)");
            return Ok(0);
        }

        let mut clauses: Vec<(u32, Vec<u32>)> = Vec::new();
        let mut binary_skipped: usize = 0;
        let mut long_skipped: usize = 0;

        for offset in self.arena.active_indices() {
            if self.arena.is_learned(offset) {
                continue;
            }

            let len = self.arena.len_of(offset);
            // Compile clauses of length 3-12.
            // Binary (len=2): already fast with inline 2WL path (BINARY_FLAG
            //   watcher entries, no arena access, single cache line).
            // Ternary (len=3): ~3.5x improvement from eliminating arena cache
            //   misses; occurrence/watch ratio (k/2) is only 1.5x.
            // Quaternary/Quinary (len=4,5): still benefit from eliminating
            //   arena indirection; short unrolled scan (2-3 extra checks) is
            //   cheaper than 2WL watch management + arena cache miss.
            // Medium (len=6-12): loop-based codegen with embedded literal
            //   immediates. Lower priority than short clauses in the budget
            //   allocation, but still eliminates arena cache misses for
            //   frequently-visited clauses. Per-function 4KB cap prevents
            //   I-cache pressure from variables with many clause occurrences.
            // Long (len>12): too many occurrences per assignment visit;
            //   2WL's O(1) amortized cost wins at this length.
            if len < 3 || len > 12 {
                if len == 2 {
                    binary_skipped += 1;
                } else if len > 12 {
                    long_skipped += 1;
                }
                continue;
            }

            let lits: Vec<u32> = (0..len)
                .map(|i| self.arena.literal(offset, i).0)
                .collect();
            clauses.push((offset as u32, lits));
        }

        let clause_count = clauses.len();
        tracing::info!(
            binary_skipped,
            long_skipped,
            compiled_candidates = clause_count,
            "JIT: compiling len 3-12 clauses (binary+very-long use 2WL)"
        );
        if clause_count == 0 {
            return Ok(0);
        }

        // Second compile-worthiness gate: need enough compilable clauses to
        // amortize JIT compilation overhead (~5ms baseline).
        if clause_count < MIN_TERNARY_CLAUSES {
            tracing::info!(
                candidate_count = clause_count,
                "JIT: skipped (too few compilable clauses)"
            );
            return Ok(0);
        }

        let jit_input: Vec<(u32, &[u32])> = clauses
            .iter()
            .map(|(id, lits)| (*id, lits.as_slice()))
            .collect();

        let compile_start = std::time::Instant::now();
        match z4_jit::compile(self.num_vars, &jit_input) {
            Ok(compiled) => {
                let compile_elapsed = compile_start.elapsed();
                self.stats.jit_compile_time_us = compile_elapsed.as_micros() as u64;
                let compiled_clauses = compiled.num_clauses();
                self.stats.jit_clauses_compiled = compiled_clauses as u64;
                let budget_exhausted = compiled.budget_exhausted();
                if budget_exhausted {
                    tracing::info!(
                        compiled_clauses,
                        total_clauses = clause_count,
                        estimated_bytes = compiled.estimated_code_bytes(),
                        "JIT: code size budget exhausted, remaining vars use 2WL"
                    );
                }
                tracing::info!(
                    compiled_clauses,
                    compile_time_us = self.stats.jit_compile_time_us,
                    "JIT: compilation complete"
                );
                self.compiled_formula = Some(compiled);
                Ok(compiled_clauses)
            }
            Err(e) => Err(format!("JIT compilation failed: {e}")),
        }
    }

    /// Check if JIT compilation is available and the formula has been compiled.
    #[inline]
    pub(crate) fn has_compiled_formula(&self) -> bool {
        self.compiled_formula.is_some()
    }

    /// Drop the compiled formula, reverting to standard 2WL BCP.
    ///
    /// **Does NOT reattach watches.** Callers must ensure watches are
    /// reattached before standard BCP resumes. Use
    /// `jit_invalidate_for_structural_pass()` for inprocessing paths, or
    /// call `reattach_jit_watches()` manually before this method.
    pub(crate) fn invalidate_compiled_formula(&mut self) {
        self.compiled_formula = None;
    }

    /// Invalidate the compiled formula before a structural inprocessing pass
    /// that modifies clause literals or structure (#8128).
    ///
    /// Does NOT reattach watches here. Structural passes manage their own
    /// watch lifecycle: BVE clears all watches and rebuilds after; decompose,
    /// subsume, and vivify operate on clauses directly and watches are rebuilt
    /// by the inprocessing round's normal watch management. Calling
    /// `reattach_jit_watches()` here would create duplicate watch entries for
    /// clauses whose watches were never detached (e.g., budget_exhausted case).
    ///
    /// No-op if already invalidated or no formula existed.
    pub(crate) fn jit_invalidate_for_structural_pass(&mut self) {
        if self.compiled_formula.is_some() {
            self.compiled_formula = None;
            tracing::debug!("jit: invalidated compiled formula before structural pass");
        }
    }

    /// Detach 2WL watch entries for irredundant clauses covered by JIT.
    ///
    /// After JIT compilation succeeds (with full coverage, no budget exhaustion),
    /// remove watch entries for non-learned, non-binary clauses in the compiled
    /// length range (3-5). These clauses are handled by JIT-compiled BCP and
    /// do not need interpreted 2WL processing.
    ///
    /// Returns the number of watch entries removed.
    pub(crate) fn detach_jit_compiled_watches(&mut self) -> usize {
        if !self.has_compiled_formula() {
            return 0;
        }
        if self
            .compiled_formula
            .as_ref()
            .is_some_and(|cf| cf.budget_exhausted())
        {
            // When budget was exhausted, some compiled-range clauses still need
            // 2WL because their var-polarity pairs were skipped by the compiler.
            // We can't cheaply determine which ones, so keep all watches.
            return 0;
        }
        let removed = self.watches.detach_irredundant_watches(|offset| {
            // Keep learned clauses (not compiled by JIT).
            if self.arena.is_learned(offset) {
                return true;
            }
            // Keep clauses outside compiled range (binary + very long).
            let len = self.arena.len_of(offset);
            len < 3 || len > 12
        });
        self.stats.jit_watches_detached += removed as u64;
        removed
    }

    /// Reattach 2WL watch entries for irredundant clauses that were previously
    /// detached for JIT compilation.
    ///
    /// Called when JIT is invalidated outside of a full watch rebuild (e.g.,
    /// arena GC, variable compaction). Scans all active non-learned clauses
    /// in the compiled length range (3-12) and adds watch entries for any that
    /// are missing.
    ///
    /// Returns the number of watch entries added.
    pub(crate) fn reattach_jit_watches(&mut self) -> usize {
        use crate::watched::ClauseRef;
        let mut reattached = 0;
        let indices: Vec<usize> = self.arena.active_indices().collect();
        for offset in indices {
            if self.arena.is_learned(offset) {
                continue;
            }
            let len = self.arena.len_of(offset);
            if len < 3 || len > 12 {
                continue;
            }
            // Reattach: prepare watched literals and attach.
            let clause_ref = ClauseRef(offset as u32);
            let watched = {
                let lits = self.arena.literals_mut(offset);
                Self::prepare_watched_literals_with_state(
                    &self.vals,
                    &self.var_data,
                    lits,
                    WatchOrderPolicy::AssignmentScore,
                )
            };
            if let Some(watched) = watched {
                self.attach_clause_watches(clause_ref, watched, false);
                reattached += 2; // Each clause attaches 2 watch entries.
            }
        }
        self.stats.jit_watches_reattached += reattached as u64;
        tracing::debug!(reattached, "JIT: reattached watches after invalidation");
        reattached
    }

    /// Report JIT compilation statistics for diagnostics.
    #[allow(dead_code)]
    pub(crate) fn jit_stats(&self) -> (usize, usize) {
        self.compiled_formula
            .as_ref()
            .map(|cf| (cf.num_clauses(), cf.num_vars()))
            .unwrap_or((0, 0))
    }
}
