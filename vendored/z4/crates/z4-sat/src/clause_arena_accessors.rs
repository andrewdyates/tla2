// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Snapshot of the clause header words used by the BCP long-clause path.
///
/// Caches word[0] (literal count) and word[2] (saved_pos + flags) from a
/// single call site. This avoids re-reading both header words for the
/// garbage, vivify-skip, saved-position, and clause-length checks, and
/// eliminates the separate `arena.literals()` call (which goes through
/// `bytemuck::cast_slice` + bounds-checked slice creation).
#[derive(Clone, Copy)]
pub(crate) struct ClauseBcpHeader {
    word: u32,
    /// Clause literal count from word[0], cached to avoid re-reading.
    len: usize,
}

impl ClauseBcpHeader {
    #[inline]
    pub(crate) fn saved_pos(self) -> usize {
        (self.word & 0xFFFF) as usize
    }

    #[inline]
    pub(crate) fn is_garbage_any(self) -> bool {
        ((self.word >> 16) as u16) & (GARBAGE_BIT | PENDING_GARBAGE_BIT) != 0
    }

    #[inline]
    pub(crate) fn is_vivify_skipped(self) -> bool {
        ((self.word >> 16) as u16) & VIVIFY_SKIP_BIT != 0
    }

    /// Clause literal count, cached from word[0] at header read time.
    #[inline]
    pub(crate) fn clause_len(self) -> usize {
        self.len
    }
}

impl ClauseArena {
    /// Read the BCP-relevant header words once for the long-clause slow path.
    ///
    /// Reads both word[0] (literal count) and word[2] (saved_pos + flags)
    /// in one call. The clause length is cached in the header struct so
    /// the BCP loop can skip the `arena.literals()` call entirely and use
    /// direct `bcp_literal()` access instead.
    #[inline]
    pub(crate) fn bcp_header(&self, offset: usize) -> ClauseBcpHeader {
        ClauseBcpHeader {
            word: self.words[offset + 2],
            len: (self.words[offset] & 0xFFFF) as usize,
        }
    }

    /// Unchecked literal access for the BCP hot path.
    ///
    /// Returns the literal at position `idx` within the clause at `offset`,
    /// bypassing bounds checks in release builds (via `z4_prefetch::word_at`).
    /// This matches CaDiCaL's `lits[k]` raw pointer pattern.
    ///
    /// # Safety contract
    ///
    /// Caller must ensure `offset + HEADER_WORDS + idx < self.words.len()`.
    /// This is guaranteed by construction: clause offsets and lengths are
    /// validated at insertion time, and `idx < clause_len` is maintained
    /// by the BCP replacement scan loop bounds.
    #[inline(always)]
    pub(crate) fn bcp_literal(&self, offset: usize, idx: usize) -> Literal {
        Literal(z4_prefetch::word_at(
            &self.words,
            offset + HEADER_WORDS + idx,
        ))
    }

    #[inline]
    pub(crate) fn is_garbage(&self, offset: usize) -> bool {
        self.flags(offset) & GARBAGE_BIT != 0
    }

    /// Mark a clause as garbage without zeroing its literal data.
    ///
    /// Matches CaDiCaL's `mark_garbage()`: sets the garbage flag so BCP skips
    /// the clause, but keeps literal data intact. Used by eager subsumption
    /// (analyze.cpp:728-766) where the clause might still serve as a reason
    /// for an assigned variable. The clause is fully deleted during the next
    /// `reduce_db` or garbage collection pass.
    #[inline]
    pub(crate) fn mark_garbage_keep_data(&mut self, offset: usize) {
        debug_assert!(offset < self.words.len(), "BUG: mark_garbage out of bounds");
        debug_assert!(
            self.lit_len_raw(offset) != 0,
            "BUG: mark_garbage on already-deleted clause"
        );
        let mut f = self.flags(offset);
        f |= GARBAGE_BIT;
        self.set_flags(offset, f);
    }

    /// Set the garbage flag directly. Test-only; production manages garbage
    /// internally through `delete()`, `replace()`, and `mark_garbage_keep_data()`.
    #[cfg(test)]
    pub(crate) fn set_garbage(&mut self, offset: usize, garbage: bool) {
        let mut f = self.flags(offset);
        if garbage {
            f |= GARBAGE_BIT;
        } else {
            f &= !GARBAGE_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Combined garbage check: returns true if either garbage or pending-garbage.
    /// Single flags() read + single bitmask test avoids two separate word reads
    /// in the BCP hot loop. CaDiCaL propagate.cpp:264 checks `c->garbage` which
    /// covers both states.
    #[inline]
    pub(crate) fn is_garbage_any(&self, offset: usize) -> bool {
        self.flags(offset) & (GARBAGE_BIT | PENDING_GARBAGE_BIT) != 0
    }

    #[inline]
    pub(crate) fn is_pending_garbage(&self, offset: usize) -> bool {
        self.flags(offset) & PENDING_GARBAGE_BIT != 0
    }

    #[inline]
    pub(crate) fn set_pending_garbage(&mut self, offset: usize, pending: bool) {
        let mut f = self.flags(offset);
        if pending {
            f |= PENDING_GARBAGE_BIT;
        } else {
            f &= !PENDING_GARBAGE_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Combined liveness check for BCP: returns true if clause is deleted,
    /// garbage, or pending garbage. Single branch replaces three separate
    /// checks in the BCP hot loop.
    #[inline]
    pub(crate) fn is_dead(&self, offset: usize) -> bool {
        self.lit_len_raw(offset) == 0
            || self.flags(offset) & (GARBAGE_BIT | PENDING_GARBAGE_BIT) != 0
    }

    #[inline]
    pub(crate) fn is_learned(&self, offset: usize) -> bool {
        self.flags(offset) & LEARNED_BIT != 0
    }

    #[inline]
    pub(crate) fn set_learned(&mut self, offset: usize, learned: bool) {
        let was_learned = self.is_learned(offset);
        let is_active = self.lit_len_raw(offset) != 0;
        let mut f = self.flags(offset);
        if learned {
            f |= LEARNED_BIT;
        } else {
            f &= !LEARNED_BIT;
        }
        self.set_flags(offset, f);
        if is_active && was_learned != learned {
            if learned {
                self.irredundant_count = self.irredundant_count.saturating_sub(1);
                self.redundant_count += 1;
            } else {
                self.redundant_count = self.redundant_count.saturating_sub(1);
                self.irredundant_count += 1;
            }
        }
    }

    #[inline]
    pub(crate) fn used(&self, offset: usize) -> u8 {
        ((self.flags(offset) & USED_MASK) >> USED_SHIFT) as u8
    }

    #[inline]
    pub(crate) fn set_used(&mut self, offset: usize, val: u8) {
        let clamped = u16::from(val.min(MAX_USED));
        let mut f = self.flags(offset);
        f = (f & !USED_MASK) | ((clamped << USED_SHIFT) & USED_MASK);
        self.set_flags(offset, f);
    }

    #[inline]
    pub(crate) fn decay_used(&mut self, offset: usize) {
        let current = self.used(offset);
        self.set_used(offset, current.saturating_sub(1));
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn is_vivify_skipped(&self, offset: usize) -> bool {
        self.flags(offset) & VIVIFY_SKIP_BIT != 0
    }

    #[inline]
    pub(crate) fn set_vivify_skip(&mut self, offset: usize, skip: bool) {
        let mut f = self.flags(offset);
        if skip {
            f |= VIVIFY_SKIP_BIT;
        } else {
            f &= !VIVIFY_SKIP_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Returns true if this clause was produced by hyper binary or ternary
    /// resolution. CaDiCaL clause.hpp:46 `bool hyper : 1`.
    #[inline]
    pub(crate) fn is_hyper(&self, offset: usize) -> bool {
        self.flags(offset) & HYPER_BIT != 0
    }

    /// Mark or unmark a clause as a hyper resolvent.
    #[inline]
    pub(crate) fn set_hyper(&mut self, offset: usize, hyper: bool) {
        let mut f = self.flags(offset);
        if hyper {
            f |= HYPER_BIT;
        } else {
            f &= !HYPER_BIT;
        }
        self.set_flags(offset, f);
    }

    /// CaDiCaL `c->subsume`: true if this clause should be tried as a
    /// subsumption candidate in the current forward subsumption round.
    #[inline]
    pub(crate) fn is_subsume_candidate(&self, offset: usize) -> bool {
        self.flags(offset) & SUBSUME_TRIED_BIT != 0
    }

    /// Set or clear the per-clause subsumption candidate flag.
    #[inline]
    pub(crate) fn set_subsume_candidate(&mut self, offset: usize, val: bool) {
        let mut f = self.flags(offset);
        if val {
            f |= SUBSUME_TRIED_BIT;
        } else {
            f &= !SUBSUME_TRIED_BIT;
        }
        self.set_flags(offset, f);
    }

    /// CaDiCaL `c->conditioned`: tried as conditioning candidate.
    #[inline]
    pub(crate) fn is_conditioned(&self, offset: usize) -> bool {
        self.flags(offset) & CONDITIONED_BIT != 0
    }

    /// Set/clear per-clause conditioned flag.
    #[inline]
    pub(crate) fn set_conditioned(&mut self, offset: usize, val: bool) {
        let mut f = self.flags(offset);
        if val {
            f |= CONDITIONED_BIT;
        } else {
            f &= !CONDITIONED_BIT;
        }
        self.set_flags(offset, f);
    }

    /// CaDiCaL `c->instantiated`: clause has been tried by post-BVE
    /// instantiation (CaDiCaL instantiate.cpp:211).
    #[inline]
    pub(crate) fn is_instantiated(&self, offset: usize) -> bool {
        self.flags(offset) & INSTANTIATED_BIT != 0
    }

    /// Set/clear per-clause instantiated flag.
    #[inline]
    pub(crate) fn set_instantiated(&mut self, offset: usize, val: bool) {
        let mut f = self.flags(offset);
        if val {
            f |= INSTANTIATED_BIT;
        } else {
            f &= !INSTANTIATED_BIT;
        }
        self.set_flags(offset, f);
    }

    #[inline]
    pub(crate) fn lbd(&self, offset: usize) -> u32 {
        u32::from((self.words[offset] >> 16) as u16)
    }

    #[inline]
    pub(crate) fn set_lbd(&mut self, offset: usize, lbd: u32) {
        let lbd16 = lbd.min(u32::from(u16::MAX)) as u16;
        self.words[offset] = (self.words[offset] & 0x0000_FFFF) | (u32::from(lbd16) << 16);
    }

    #[inline]
    pub(crate) fn signature(&self, offset: usize) -> ClauseSignature {
        u64::from(self.words[offset + 3]) | (u64::from(self.words[offset + 4]) << 32)
    }

    /// Read the activity slot (header word 1) as f32. Test-only; clause activity
    /// was removed from production code in #5132 (CaDiCaL uses no clause activity).
    #[cfg(test)]
    #[inline]
    pub(crate) fn activity(&self, offset: usize) -> f32 {
        f32::from_bits(self.words[offset + 1])
    }

    /// Write the activity slot (header word 1) as f32. Test-only.
    #[cfg(test)]
    #[inline]
    pub(crate) fn set_activity(&mut self, offset: usize, activity: f32) {
        self.words[offset + 1] = activity.to_bits();
    }

    #[inline]
    pub(crate) fn literal(&self, offset: usize, idx: usize) -> Literal {
        Literal(self.words[offset + HEADER_WORDS + idx])
    }

    /// Set a single literal by index. Test-only; production uses `literals_mut()`.
    #[cfg(test)]
    pub(crate) fn set_literal(&mut self, offset: usize, idx: usize, lit: Literal) {
        self.words[offset + HEADER_WORDS + idx] = lit.0;
    }

    #[inline]
    pub(crate) fn watched_literals(&self, offset: usize) -> (Literal, Literal) {
        let base = offset + HEADER_WORDS;
        (Literal(self.words[base]), Literal(self.words[base + 1]))
    }

    /// Zero-copy literal slice. Safe via `bytemuck` because `Literal` is
    /// `#[repr(transparent)]` over `u32` and derives `Pod + Zeroable`.
    #[inline]
    pub(crate) fn literals(&self, offset: usize) -> &[Literal] {
        let len = self.lit_len_raw(offset) as usize;
        let base = offset + HEADER_WORDS;
        bytemuck::cast_slice(&self.words[base..base + len])
    }

    /// Recover literals from a clause that may have been deleted by
    /// `elim_propagate` during BVE.
    ///
    /// When `delete()` marks a clause as garbage it zeros the literal count
    /// but preserves the literal data and saves the original `alloc_len` in
    /// `words[offset + 1]`.  This method reads that saved length to return
    /// the original literals even after deletion.
    ///
    /// CaDiCaL pushes ALL defining clauses onto the extension stack before
    /// any deletion (`external.cpp:55-69`, `elim.cpp:628-670`).  Z4's
    /// per-variable `elim_propagate` can delete clauses that later variables'
    /// `WitnessEntry` references still need for reconstruction (#5059).
    #[inline]
    pub(crate) fn literals_or_deleted(&self, offset: usize) -> &[Literal] {
        let len = self.lit_len_raw(offset) as usize;
        if len != 0 {
            let base = offset + HEADER_WORDS;
            return bytemuck::cast_slice(&self.words[base..base + len]);
        }
        // Deleted clause: pre-delete literal count in upper 16 bits of word[1].
        let saved_len = (self.words[offset + 1] >> 16) as usize;
        if saved_len == 0 {
            return &[];
        }
        let base = offset + HEADER_WORDS;
        bytemuck::cast_slice(&self.words[base..base + saved_len])
    }

    /// Single-literal access by index within a clause. Returns the literal
    /// by value (Copy), avoiding a slice borrow on the arena. This enables
    /// index-based iteration without borrow conflicts with other Solver fields
    /// (#6989: eliminates clause_buf copy in conflict analysis).
    #[inline]
    pub(crate) fn literal_at(&self, offset: usize, index: usize) -> Literal {
        let base = offset + HEADER_WORDS;
        Literal(self.words[base + index])
    }

    /// Zero-copy mutable literal slice. Same justification as `literals()`.
    #[inline]
    pub(crate) fn literals_mut(&mut self, offset: usize) -> &mut [Literal] {
        let len = self.lit_len_raw(offset) as usize;
        let base = offset + HEADER_WORDS;
        bytemuck::cast_slice_mut(&mut self.words[base..base + len])
    }

    #[inline]
    pub(crate) fn swap_literals(&mut self, offset: usize, i: usize, j: usize) {
        let base = offset + HEADER_WORDS;
        self.words.swap(base + i, base + j);
    }

    /// Total literals stored across all clauses (including deleted). Test-only.
    #[cfg(test)]
    pub(crate) fn total_literals(&self) -> usize {
        let mut total = 0;
        for off in self.indices() {
            total += self.lit_len_raw(off) as usize;
        }
        total
    }

    /// Total literals stored across active clauses. Test-only.
    ///
    /// Note: identical to `total_literals()` because the arena iterator walks
    /// all entries (including deleted) and `lit_len_raw` returns 0 for deleted
    /// clauses, so they contribute nothing. Kept as a separate name for
    /// semantic clarity in callers that want "active" counts.
    #[cfg(test)]
    pub(crate) fn active_literals(&self) -> usize {
        self.total_literals()
    }

    pub(crate) fn memory_bytes(&self) -> usize {
        24 + self.words.capacity() * 4 + 48
    }
}
