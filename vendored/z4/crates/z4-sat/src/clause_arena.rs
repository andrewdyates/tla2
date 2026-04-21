// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified clause arena with inline literals (CaDiCaL-style).
//!
//! Layout per clause: 5 header words + N literal words in a contiguous `Vec<u32>`.
//! The extra two header words store a 64-bit clause signature for BVE filtering.
//! A 3-literal clause = 32 bytes, still fitting comfortably in a single cache line.
//! Reference: CaDiCaL `clause.hpp:31-122`, `arena.hpp:56-101`.
//!
//! # Direct-Offset Design (Step 2 of #3904)
//!
//! `ClauseRef(u32)` stores the **word offset** directly into this arena.
//! There is no indirection table — all methods accept `usize` offsets directly.
//! This eliminates one cache miss per BCP propagation step.

use crate::clause::{compute_clause_signature, ClauseSignature};
use crate::kani_compat::DetHashMap;
use crate::literal::Literal;

/// Number of u32 header words before the literal data.
pub(crate) const HEADER_WORDS: usize = 5;
const LEARNED_BIT: u16 = 0b0_0000_0001;
const USED_MASK: u16 = 0b0_0011_1110;
const USED_SHIFT: u32 = 1;
const GARBAGE_BIT: u16 = 0b0_0100_0000;
const VIVIFY_SKIP_BIT: u16 = 0b0_1000_0000;
const PENDING_GARBAGE_BIT: u16 = 0b1_0000_0000;
/// Marks clauses produced by hyper binary resolution (HBR, probing) or hyper
/// ternary resolution (HTR). CaDiCaL clause.hpp:46 `bool hyper : 1`.
/// Hyper resolvents get one-round lifetime in reduce_db: if unused since last
/// reduce, they are deleted immediately without entering the sort pool.
const HYPER_BIT: u16 = 0b10_0000_0000;
/// CaDiCaL clause.hpp `bool subsume : 1`. Per-clause flag for forward
/// subsumption scheduling: marks clauses that should be *tried* as subsumption
/// candidates in the current round. Set for all scheduled size>2 clauses when
/// no left-overs exist from a prior incomplete round; cleared after attempting
/// subsumption. Without this, Z4 re-attempts subsumption on every dirty clause
/// every round, wasting the effort budget on clauses already tried (#7393).
const SUBSUME_TRIED_BIT: u16 = 0b100_0000_0000;
/// CaDiCaL condition.cpp `c->conditioned`. Round-robin scheduling flag.
const CONDITIONED_BIT: u16 = 0b1000_0000_0000;
/// CaDiCaL clause.hpp `bool instantiated : 1`. Marks clauses that have
/// already been tried by post-BVE instantiation (CaDiCaL instantiate.cpp:211).
/// When the `instantiateonce` strategy is active, instantiated clauses are
/// skipped in subsequent collection rounds.
const INSTANTIATED_BIT: u16 = 0b1_0000_0000_0000;

/// Maximum value of the used counter (CaDiCaL internal.hpp:315).
pub(crate) const MAX_USED: u8 = 31;

/// Unified clause arena with inline header + literal storage.
///
/// `ClauseRef(u32)` values are word offsets directly into `words`.
/// All methods accept `usize` offsets; no indirection table.
pub(crate) struct ClauseArena {
    words: Vec<u32>,
    num_clauses: usize,
    /// Number of active (non-deleted) clauses.
    /// Maintained incrementally by `add`, `delete`, and `compact`.
    active_count: usize,
    /// Number of active (non-deleted) irredundant (non-learned) clauses.
    /// CaDiCaL equivalent: `stats.current.irredundant`. Maintained
    /// incrementally by `add`, `delete`, `set_learned`, and `compact`.
    irredundant_count: usize,
    /// Number of active (non-deleted) redundant (learned) clauses.
    /// Maintained incrementally by `add`, `delete`, `set_learned`, and `compact`.
    pub(crate) redundant_count: usize,
    /// Tracks clauses shrunk by `replace()`: maps word offset → original allocated
    /// literal count. Needed for arena walking: the header stores the current
    /// (shorter) literal count, but the stride must span the original allocation.
    /// Cleared on `compact()`.
    shrink_map: DetHashMap<u32, u16>,
    /// Accumulated dead words from deleted clauses. Gates arena compaction:
    /// compact when `dead_words > arena.len() / 4`. Reset on compaction.
    dead_words: usize,
}

impl ClauseArena {
    pub(crate) fn new() -> Self {
        Self {
            words: Vec::new(),
            num_clauses: 0,
            active_count: 0,
            irredundant_count: 0,
            redundant_count: 0,
            shrink_map: DetHashMap::default(),
            dead_words: 0,
        }
    }

    pub(crate) fn with_capacity(clause_hint: usize, literal_hint: usize) -> Self {
        Self {
            words: Vec::with_capacity(clause_hint * HEADER_WORDS + literal_hint),
            num_clauses: 0,
            active_count: 0,
            irredundant_count: 0,
            redundant_count: 0,
            shrink_map: DetHashMap::default(),
            dead_words: 0,
        }
    }

    /// Add a new clause. Returns the word offset as `usize`.
    pub(crate) fn add(&mut self, lits: &[Literal], learned: bool) -> usize {
        debug_assert!(!lits.is_empty(), "BUG: ClauseArena::add() with 0 literals");
        let offset = self.words.len();
        let lit_len = lits.len().min(u16::MAX as usize) as u16;
        let signature = compute_clause_signature(lits);
        self.words.push(u32::from(lit_len));
        self.words.push(0u32);
        let flags: u16 = if learned { LEARNED_BIT } else { 0 };
        self.words.push(2u32 | (u32::from(flags) << 16));
        self.words.push(signature as u32);
        self.words.push((signature >> 32) as u32);
        for lit in lits {
            self.words.push(lit.0);
        }
        self.num_clauses += 1;
        self.active_count += 1;
        if learned {
            self.redundant_count += 1;
        } else {
            self.irredundant_count += 1;
        }
        offset
    }

    #[inline]
    pub(crate) fn delete(&mut self, offset: usize) {
        debug_assert!(offset < self.words.len(), "BUG: delete out of bounds");
        debug_assert!(
            self.lit_len_raw(offset) != 0,
            "BUG: delete on deleted clause"
        );
        self.active_count = self.active_count.saturating_sub(1);
        if self.is_learned(offset) {
            self.redundant_count = self.redundant_count.saturating_sub(1);
        } else {
            self.irredundant_count = self.irredundant_count.saturating_sub(1);
        }
        // Save both the allocated literal count (for ArenaIter stride) and the
        // current literal count (for literals_or_deleted reconstruction) in
        // word[1] (activity slot).  Layout: upper 16 bits = current_len,
        // lower 16 bits = alloc_len.  Both are u16, so this is lossless.
        let current_len = self.lit_len_raw(offset);
        let alloc_len = if let Some(orig) = self.shrink_map.remove(&(offset as u32)) {
            orig
        } else {
            current_len
        };
        // Track dead space for compaction gating.
        self.dead_words += HEADER_WORDS + alloc_len as usize;
        self.words[offset + 1] = u32::from(alloc_len) | ((u32::from(current_len)) << 16);
        // Zero the literal count to mark as deleted.
        self.words[offset] &= 0xFFFF_0000;
        let mut f = self.flags(offset);
        f |= GARBAGE_BIT;
        f &= !PENDING_GARBAGE_BIT;
        self.set_flags(offset, f);
    }

    /// Replace a clause's literals in place (clause can only shrink).
    pub(crate) fn replace(&mut self, offset: usize, new_lits: &[Literal]) {
        let current_len = self.lit_len_raw(offset);
        debug_assert!(!new_lits.is_empty(), "BUG: replace with empty literals");
        debug_assert!(
            new_lits.len() <= current_len as usize,
            "BUG: replace grows clause"
        );
        if new_lits.len() < current_len as usize {
            // Track the original allocation for arena walking.
            // `or_insert` preserves the FIRST (largest) allocation if shrunk twice.
            self.shrink_map.entry(offset as u32).or_insert(current_len);
        }
        let signature = compute_clause_signature(new_lits);
        self.words[offset] = (self.words[offset] & 0xFFFF_0000) | (new_lits.len() as u32);
        self.words[offset + 3] = signature as u32;
        self.words[offset + 4] = (signature >> 32) as u32;
        let base = offset + HEADER_WORDS;
        for (i, lit) in new_lits.iter().enumerate() {
            self.words[base + i] = lit.0;
        }
        self.set_saved_pos(offset, 2);
        let mut f = self.flags(offset);
        f &= !(GARBAGE_BIT | PENDING_GARBAGE_BIT);
        self.set_flags(offset, f);
    }

    /// Number of clauses ever added (including deleted, excluding compacted-away).
    #[inline]
    pub(crate) fn num_clauses(&self) -> usize {
        self.num_clauses
    }

    /// Number of currently active clauses.
    ///
    /// Unlike `num_clauses()`, this excludes deleted clauses and therefore
    /// matches the residual formula size seen by inprocessing passes.
    #[inline]
    pub(crate) fn active_clause_count(&self) -> usize {
        self.active_count
    }

    /// Number of active irredundant (non-learned) clauses.
    #[inline]
    pub(crate) fn irredundant_count(&self) -> usize {
        self.irredundant_count
    }

    /// Override the reported clause count for scheduler-focused tests.
    ///
    /// This is only valid in tests that exercise size-based gates. Production
    /// code must derive the count from actual arena contents.
    #[cfg(test)]
    pub(crate) fn spoof_num_clauses_for_test(&mut self, num_clauses: usize) {
        self.num_clauses = num_clauses;
    }

    /// Raw read-only access to the arena word buffer.
    ///
    /// Used by `propagate_bcp_unsafe` to obtain a `*const u32` for direct
    /// pointer-arithmetic literal access, matching CaDiCaL's `lits[k]` pattern.
    #[cfg(feature = "unsafe-bcp")]
    #[inline]
    pub(crate) fn words(&self) -> &[u32] {
        &self.words
    }

    /// Issue a software prefetch hint for the clause header at `offset`.
    ///
    /// Prefetches the first cache line of the clause (header + first few
    /// literals). This hides main-memory latency (~60-80 cycles) when the
    /// BCP loop knows it will access a clause's arena data shortly.
    ///
    /// Used in the BCP long-clause path: when a non-binary watcher's blocker
    /// is not satisfied, we will read `arena[clause_ref]`. Prefetching the
    /// next clause's data while processing the current one overlaps the
    /// memory access with computation.
    ///
    /// Reference: CaDiCaL propagate.cpp clause data prefetch pattern (#8000).
    #[inline(always)]
    pub(crate) fn prefetch_clause(&self, offset: usize) {
        // Prefetch word[0] of the clause header. The CPU will bring in the
        // entire cache line (64 bytes = 16 u32 words), which covers the
        // 5-word header + first 11 literal words — enough for most clauses.
        z4_prefetch::prefetch_arena_at(&self.words, offset);
    }

    /// Total words in the arena. Used for bounds checks: `idx < arena.len()`
    /// works when `idx` is a word offset.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.words.len()
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    /// Iterate over all clause offsets (live and deleted) by walking arena headers.
    pub(crate) fn indices(&self) -> ArenaIter<'_> {
        ArenaIter {
            words: &self.words,
            shrink_map: &self.shrink_map,
            pos: 0,
        }
    }

    /// Iterate over offsets of active (non-deleted) clauses.
    pub(crate) fn active_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.indices().filter(|&off| self.lit_len_raw(off) != 0)
    }

    #[inline]
    pub(crate) fn is_active(&self, offset: usize) -> bool {
        offset < self.words.len() && self.lit_len_raw(offset) != 0
    }

    /// Accumulated dead words from deleted clauses. Used to gate compaction:
    /// compact when `dead_words() > len() / 4`.
    #[inline]
    pub(crate) fn dead_words(&self) -> usize {
        self.dead_words
    }

    /// Reorder and compact live clauses into a fresh arena. Returns a flat
    /// remap table where `remap[old_offset] = new_offset` (unmapped offsets
    /// contain `u32::MAX`).
    ///
    /// Clauses are copied in the order specified by `order` (word offsets of
    /// live clauses). Only `HEADER_WORDS + current_lit_len` words are copied
    /// per clause, healing any shrink gaps from `replace()`.
    ///
    /// Reference: CaDiCaL collect.cpp:385-399 (arenatype=3).
    pub(crate) fn compact_reorder(&mut self, order: &[u32]) -> Vec<u32> {
        let mut remap = vec![u32::MAX; self.words.len()];
        let estimated_live = self.active_count * (HEADER_WORDS + 8);
        let mut new_words = Vec::with_capacity(estimated_live);
        let mut new_clause_count = 0usize;
        let mut new_active_count = 0usize;
        let mut new_irredundant = 0usize;
        let mut new_redundant = 0usize;

        for &old_off in order {
            let off = old_off as usize;
            let lit_len = self.lit_len_raw(off) as usize;
            if lit_len == 0 {
                // Deleted clause snuck into order — skip.
                continue;
            }
            let new_off = new_words.len();
            // Copy header + current literals (not the original alloc tail).
            let end = off + HEADER_WORDS + lit_len;
            debug_assert!(
                end <= self.words.len(),
                "BUG: compact_reorder clause at {off} extends past arena (end={end}, len={})",
                self.words.len()
            );
            new_words.extend_from_slice(&self.words[off..end]);
            remap[off] = new_off as u32;
            new_clause_count += 1;
            new_active_count += 1;
            if self.is_learned(off) {
                new_redundant += 1;
            } else {
                new_irredundant += 1;
            }
        }

        self.words = new_words;
        self.num_clauses = new_clause_count;
        self.active_count = new_active_count;
        self.irredundant_count = new_irredundant;
        self.redundant_count = new_redundant;
        self.shrink_map.clear();
        self.dead_words = 0;
        remap
    }

    #[inline]
    fn lit_len_raw(&self, off: usize) -> u16 {
        (self.words[off] & 0xFFFF) as u16
    }

    #[inline]
    pub(crate) fn len_of(&self, offset: usize) -> usize {
        self.lit_len_raw(offset) as usize
    }

    #[inline]
    pub(crate) fn is_empty_clause(&self, offset: usize) -> bool {
        self.lit_len_raw(offset) == 0
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn saved_pos(&self, offset: usize) -> usize {
        (self.words[offset + 2] & 0xFFFF) as usize
    }

    #[inline]
    pub(crate) fn set_saved_pos(&mut self, offset: usize, pos: usize) {
        let w = offset + 2;
        let pos16 = pos.min(u16::MAX as usize) as u16;
        self.words[w] = (self.words[w] & 0xFFFF_0000) | u32::from(pos16);
    }

    #[inline]
    fn flags(&self, off: usize) -> u16 {
        (self.words[off + 2] >> 16) as u16
    }

    #[inline]
    fn set_flags(&mut self, off: usize, flags: u16) {
        self.words[off + 2] = (self.words[off + 2] & 0x0000_FFFF) | (u32::from(flags) << 16);
    }

    /// Total words in the arena backing store. Test-only (production uses `len()`).
    #[cfg(test)]
    pub(crate) fn total_words(&self) -> usize {
        self.words.len()
    }

    /// Remove deleted clauses. Returns (old_offset, new_offset) remapping.
    ///
    /// Production code does NOT call this — `arena.compact()` renumbers word
    /// offsets, invalidating all `ClauseRef` values in watch lists, reason
    /// vectors, and the trail. See `solver/reduction.rs:446` and `solver/compact.rs`.
    /// Kept for test coverage of the compaction algorithm.
    #[cfg(test)]
    pub(crate) fn compact(&mut self) -> Vec<(usize, usize)> {
        let mut new_words = Vec::new();
        let mut remapping = Vec::new();
        let mut new_clause_count = 0usize;
        let mut new_active_count = 0usize;
        let mut new_irredundant = 0usize;
        let mut new_redundant = 0usize;
        let mut pos = 0;

        while pos < self.words.len() {
            let current_len = self.lit_len_raw(pos) as usize;
            let alloc_len = if current_len == 0 {
                (self.words[pos + 1] & 0xFFFF) as usize
            } else if let Some(&orig) = self.shrink_map.get(&(pos as u32)) {
                orig as usize
            } else {
                current_len
            };
            debug_assert!(alloc_len > 0, "BUG: zero alloc_len at pos {pos}");

            if current_len > 0 {
                // Live clause: copy header + current literals (not dead tail).
                let new_off = new_words.len();
                new_words.extend_from_slice(&self.words[pos..pos + HEADER_WORDS + current_len]);
                remapping.push((pos, new_off));
                new_clause_count += 1;
                new_active_count += 1;
                if self.is_learned(pos) {
                    new_redundant += 1;
                } else {
                    new_irredundant += 1;
                }
            }

            pos += HEADER_WORDS + alloc_len;
        }

        self.words = new_words;
        self.num_clauses = new_clause_count;
        self.active_count = new_active_count;
        self.irredundant_count = new_irredundant;
        self.redundant_count = new_redundant;
        self.shrink_map.clear();
        remapping
    }
}

impl Default for ClauseArena {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator that walks the arena by reading clause headers to determine stride.
pub(crate) struct ArenaIter<'a> {
    words: &'a [u32],
    shrink_map: &'a DetHashMap<u32, u16>,
    pos: usize,
}

impl Iterator for ArenaIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.pos >= self.words.len() {
            return None;
        }
        let off = self.pos;
        let current_len = (self.words[off] & 0xFFFF) as usize;
        let alloc_len = if current_len == 0 {
            // Deleted clause: alloc_len in lower 16 bits of word[1].
            (self.words[off + 1] & 0xFFFF) as usize
        } else if let Some(&orig) = self.shrink_map.get(&(off as u32)) {
            // Shrunk clause: stride spans original allocation.
            orig as usize
        } else {
            // Normal live clause.
            current_len
        };
        debug_assert!(alloc_len > 0, "BUG: zero alloc_len in arena walk at {off}");
        self.pos += HEADER_WORDS + alloc_len;
        Some(off)
    }
}

#[path = "clause_arena_accessors.rs"]
mod accessors;

#[cfg(test)]
#[path = "clause_arena_tests.rs"]
mod tests;
