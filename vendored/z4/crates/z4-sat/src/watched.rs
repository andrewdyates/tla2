// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! 2-Watched Literal scheme with unified contiguous buffer (Kissat vector.c design).
//!
//! Each watcher is a packed u64: low 32 bits = blocker, high 32 bits = clause.
//! This keeps blocker and clause contiguous in memory (single cache line hit)
//! and enables single-memmove compaction in the BCP hot loop.
//!
//! The `WatchedLists` struct stores ALL watch entries for ALL literals in a
//! single contiguous `Vec<u64>` buffer. Each literal has a `(offset, len, capacity)`
//! triple describing its region within the buffer. This replaces 2N separate
//! heap allocations (one Vec per literal) with a single allocation, improving
//! spatial locality and reducing allocator overhead.
//!
//! Reference: Kissat `vector.c` (Armin Biere, MIT license).
//! CaDiCaL uses a similar AoS layout (watch.hpp:31-44).

use crate::literal::Literal;

#[cfg(test)]
mod tests;
#[cfg(kani)]
mod verification;

/// Index of a clause in the clause database
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct ClauseRef(pub(crate) u32);

impl ClauseRef {
    /// Create a new clause reference from a raw index
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw index value
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Get the raw u32 value
    #[inline]
    pub fn id(self) -> u32 {
        self.0
    }
}

/// High bit flag for binary clauses in the clause u32
pub(crate) const BINARY_FLAG: u32 = 0x8000_0000;

/// Pack a (blocker, clause) pair into a single u64.
#[inline(always)]
const fn pack(blocker_raw: u32, clause_raw: u32) -> u64 {
    (blocker_raw as u64) | ((clause_raw as u64) << 32)
}

/// Extract blocker (low 32 bits) from a packed u64.
#[inline(always)]
const fn unpack_blocker(entry: u64) -> u32 {
    entry as u32
}

/// Extract clause (high 32 bits) from a packed u64.
#[inline(always)]
const fn unpack_clause(entry: u64) -> u32 {
    (entry >> 32) as u32
}

/// Count binary entries in a packed-entry slice.
#[inline]
fn count_binary(entries: &[u64]) -> u32 {
    let mut bc: u32 = 0;
    for &e in entries {
        if unpack_clause(e) & BINARY_FLAG != 0 {
            bc += 1;
        }
    }
    bc
}

/// A watcher entry (parameter type for add_watch API)
///
/// For binary clauses: `blocker_raw` stores the other literal's raw value
/// For longer clauses: `blocker_raw` is a hint for early satisfaction check
///
/// The high bit of `clause_raw` indicates whether this is a binary clause.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Watcher {
    /// The clause being watched. High bit set if this is a binary clause.
    pub(crate) clause_raw: u32,
    /// For binary clauses: the other literal in the clause
    /// For non-binary clauses: blocker literal for faster filtering
    pub(crate) blocker_raw: u32,
}

impl Watcher {
    /// Create a watcher for a binary clause
    #[inline]
    pub(crate) fn binary(clause: ClauseRef, other_lit: Literal) -> Self {
        Self {
            clause_raw: clause.0 | BINARY_FLAG,
            blocker_raw: other_lit.0,
        }
    }

    /// Create a watcher for a non-binary clause (3+ literals)
    #[inline]
    pub(crate) fn new(clause: ClauseRef, blocker: Literal) -> Self {
        debug_assert!(clause.0 & BINARY_FLAG == 0, "ClauseRef too large");
        Self {
            clause_raw: clause.0,
            blocker_raw: blocker.0,
        }
    }

    /// Check if this is a binary clause watcher
    #[inline]
    #[cfg(kani)]
    pub(crate) fn is_binary(self) -> bool {
        self.clause_raw & BINARY_FLAG != 0
    }

    /// Get the clause reference (strips binary flag)
    #[inline]
    #[cfg(kani)]
    pub(crate) fn clause_ref(self) -> ClauseRef {
        ClauseRef(self.clause_raw & !BINARY_FLAG)
    }

    /// Get the blocker/other literal
    #[inline]
    #[cfg(kani)]
    pub(crate) fn blocker(self) -> Literal {
        Literal(self.blocker_raw)
    }
}

/// Standalone watch list for scratch / deferred-swap buffers.
///
/// Used by `Solver::deferred_watch_list` for the BCP swap pattern,
/// and by tests that build watch lists independently.
#[derive(Debug, Default, Clone)]
pub(crate) struct WatchList {
    /// Packed (blocker, clause) entries: low u32 = blocker, high u32 = clause
    entries: Vec<u64>,
}

impl WatchList {
    /// Create an empty watch list
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Number of watchers
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Direct mutable access to the packed entries slice.
    ///
    /// Used by BCP hot loop for field-level split borrows: the caller can
    /// hold `&mut entries[..]` simultaneously with `&self.vals[..]` because
    /// they are disjoint struct fields. This lets the compiler cache pointers
    /// in registers instead of reloading through `&mut self` on every
    /// iteration (#3758).
    #[inline]
    pub(crate) fn entries_mut(&mut self) -> &mut [u64] {
        &mut self.entries
    }

    /// Prefetch hint for first watch entry.
    ///
    /// CaDiCaL propagate.cpp:160-166: `__builtin_prefetch(&ws[0], 0, 1)`.
    /// BCP will scan this watch list on the next propagation step. Prefetch
    /// is isolated in the `z4-prefetch` crate to preserve z4-sat's
    /// `#![forbid(unsafe_code)]`.
    #[inline]
    pub(crate) fn prefetch_first(&self) {
        if let Some(first) = self.entries.first() {
            z4_prefetch::prefetch_read_l2(std::ptr::from_ref::<u64>(first));
        }
    }

    /// Get blocker raw value at index
    #[inline]
    pub(crate) fn blocker_raw(&self, i: usize) -> u32 {
        unpack_blocker(self.entries[i])
    }

    /// Get clause raw value at index (includes BINARY_FLAG if binary)
    #[inline]
    pub(crate) fn clause_raw(&self, i: usize) -> u32 {
        unpack_clause(self.entries[i])
    }

    /// Get the packed entry at index (for hot loop speculative copy)
    #[inline]
    pub(crate) fn entry(&self, i: usize) -> u64 {
        self.entries[i]
    }

    /// Get blocker as Literal at index
    #[inline]
    pub(crate) fn blocker(&self, i: usize) -> Literal {
        Literal(unpack_blocker(self.entries[i]))
    }

    /// Get clause ref at index (strips BINARY_FLAG)
    #[inline]
    pub(crate) fn clause_ref(&self, i: usize) -> ClauseRef {
        ClauseRef(unpack_clause(self.entries[i]) & !BINARY_FLAG)
    }

    /// Check if watcher at index is binary
    #[inline]
    pub(crate) fn is_binary(&self, i: usize) -> bool {
        unpack_clause(self.entries[i]) & BINARY_FLAG != 0
    }

    /// Push a watcher given raw values
    #[inline]
    pub(crate) fn push(&mut self, blocker_raw: u32, clause_raw: u32) {
        self.entries.push(pack(blocker_raw, clause_raw));
    }

    /// Push a Watcher struct
    #[inline]
    pub(crate) fn push_watcher(&mut self, w: Watcher) {
        self.entries.push(pack(w.blocker_raw, w.clause_raw));
    }

    /// Extend from another WatchList starting at index `start`
    #[cfg(test)]
    #[inline]
    pub(crate) fn extend_from(&mut self, other: &Self, start: usize) {
        self.entries.extend_from_slice(&other.entries[start..]);
    }

    /// Extend from another WatchList for the half-open range [start, end).
    #[cfg(test)]
    #[inline]
    pub(crate) fn extend_range_from(&mut self, other: &Self, start: usize, end: usize) {
        self.entries.extend_from_slice(&other.entries[start..end]);
    }

    /// Swap-remove element at index (O(1) removal)
    #[inline]
    pub(crate) fn swap_remove(&mut self, i: usize) {
        self.entries.swap_remove(i);
    }

    /// Truncate the watch list to `new_len` entries (in-place compaction).
    #[inline]
    pub(crate) fn truncate(&mut self, new_len: usize) {
        self.entries.truncate(new_len);
    }

    /// Write a packed entry at position `dst` (in-place compaction).
    #[inline]
    pub(crate) fn set_packed(&mut self, dst: usize, packed: u64) {
        self.entries[dst] = packed;
    }

    /// Write a (blocker, clause) pair at position `dst` (in-place compaction).
    #[inline]
    pub(crate) fn set_entry(&mut self, dst: usize, blocker_raw: u32, clause_raw: u32) {
        self.entries[dst] = pack(blocker_raw, clause_raw);
    }

    /// Copy entries `[src_start..src_end)` to `[dst..)` within the same list.
    #[inline]
    pub(crate) fn copy_within(&mut self, src_start: usize, src_end: usize, dst: usize) {
        self.entries.copy_within(src_start..src_end, dst);
    }

    /// Clear all entries
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }

    /// Total capacity (for memory stats)
    #[cfg(test)]
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Sort watchers so binary clauses come first (stable relative order).
    ///
    /// Mirrors [`WatchedLists::debug_assert_binary_first`] invariant for a standalone list.
    #[cfg(test)]
    pub(crate) fn sort_binary_first(&mut self) {
        if self.entries.len() <= 1 {
            return;
        }
        let mut non_binary = Vec::new();
        let mut write = 0;
        for read in 0..self.entries.len() {
            let entry = self.entries[read];
            let clause_raw = unpack_clause(entry);
            if clause_raw & BINARY_FLAG != 0 {
                self.entries[write] = entry;
                write += 1;
            } else {
                non_binary.push(entry);
            }
        }
        self.entries[write..write + non_binary.len()].copy_from_slice(&non_binary);
    }

    /// Remap clause refs using a relocation map, dropping dead entries.
    ///
    /// Mirrors [`WatchedLists::remap_clause_refs`] for a standalone list.
    #[cfg(test)]
    pub(crate) fn remap_clause_refs(&mut self, remap: &[u32]) {
        let mut j = 0;
        for i in 0..self.entries.len() {
            let entry = self.entries[i];
            let clause_raw = unpack_clause(entry);
            let blocker_raw = unpack_blocker(entry);
            let is_binary = clause_raw & BINARY_FLAG != 0;
            let old_offset = (clause_raw & !BINARY_FLAG) as usize;
            if old_offset >= remap.len() || remap[old_offset] == u32::MAX {
                continue;
            }
            let new_offset = remap[old_offset];
            let new_clause_raw = new_offset | if is_binary { BINARY_FLAG } else { 0 };
            self.entries[j] = pack(blocker_raw, new_clause_raw);
            j += 1;
        }
        self.entries.truncate(j);
    }
}

// ─── Per-literal metadata into the unified buffer ───────────────────

/// Metadata for a single literal's region in the unified watch buffer.
#[derive(Debug, Clone, Copy, Default)]
struct WatchMeta {
    /// Start index into the unified buffer.
    offset: u32,
    /// Number of active entries.
    len: u32,
    /// Allocated capacity (slots in buffer starting at offset).
    capacity: u32,
    /// Number of binary watch entries at the front of this region.
    /// Invariant: entries [offset..offset+binary_count) have BINARY_FLAG set,
    /// entries [offset+binary_count..offset+len) do not.
    binary_count: u32,
}

/// Watched literal lists with unified contiguous buffer (Kissat vector.c design).
///
/// All watch entries for all literals are stored in a single `Vec<u64>`.
/// Each literal has a `WatchMeta` triple `(offset, len, capacity)` describing
/// its region within the buffer. This replaces 2N separate heap allocations
/// with a single allocation, improving spatial locality and reducing allocator
/// overhead by ~48 bytes per literal (two Vec headers eliminated).
///
/// Defragmentation (`defragment()`) compacts the buffer by sorting non-empty
/// regions by offset and copying forward, reclaiming gaps left by cleared
/// or shrunk watch lists. Called from `shrink_capacity()` after arena GC.
#[derive(Debug, Default)]
pub(crate) struct WatchedLists {
    /// Single contiguous buffer holding ALL watch entries for ALL literals.
    buffer: Vec<u64>,
    /// Per-literal metadata: (offset, len, capacity) into buffer.
    /// Indexed by `literal.index()` (= var * 2 + sign).
    meta: Vec<WatchMeta>,
    /// Total number of "dead" (freed but not reclaimed) slots in the buffer.
    dead_slots: usize,
}

impl WatchedLists {
    /// Create new watched lists for n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        let num_lits = num_vars.saturating_mul(2);
        Self {
            buffer: Vec::new(),
            meta: vec![WatchMeta::default(); num_lits],
            dead_slots: 0,
        }
    }

    /// Ensure the watched lists can index literals for `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let target = num_vars.saturating_mul(2);
        if self.meta.len() < target {
            self.meta.resize(target, WatchMeta::default());
        }
    }

    /// Clear all watch lists without deallocating the buffer.
    pub(crate) fn clear(&mut self) {
        for m in &mut self.meta {
            m.len = 0;
            m.capacity = 0;
            m.offset = 0;
            m.binary_count = 0;
        }
        self.buffer.clear();
        self.dead_slots = 0;
    }

    /// Number of watch lists (one per literal index).
    #[inline]
    pub(crate) fn num_lists(&self) -> usize {
        self.meta.len()
    }

    // ─── Single-literal read access (indexed by literal + watcher index) ─

    /// Number of watchers for a literal
    #[inline]
    pub(crate) fn len_of(&self, lit: Literal) -> usize {
        self.meta[lit.index()].len as usize
    }

    /// Get blocker raw value at watcher index within a literal's watch list
    #[inline]
    pub(crate) fn blocker_raw(&self, lit: Literal, i: usize) -> u32 {
        let start = self.meta[lit.index()].offset as usize;
        unpack_blocker(self.buffer[start + i])
    }

    /// Get clause raw value at watcher index (includes BINARY_FLAG if binary)
    #[inline]
    pub(crate) fn clause_raw(&self, lit: Literal, i: usize) -> u32 {
        let start = self.meta[lit.index()].offset as usize;
        unpack_clause(self.buffer[start + i])
    }

    /// Get the packed entry at watcher index
    #[inline]
    pub(crate) fn entry_at(&self, lit: Literal, i: usize) -> u64 {
        let start = self.meta[lit.index()].offset as usize;
        self.buffer[start + i]
    }

    /// Get blocker as Literal at watcher index
    #[inline]
    pub(crate) fn blocker(&self, lit: Literal, i: usize) -> Literal {
        Literal(self.blocker_raw(lit, i))
    }

    /// Get clause ref at watcher index (strips BINARY_FLAG)
    #[inline]
    pub(crate) fn clause_ref(&self, lit: Literal, i: usize) -> ClauseRef {
        ClauseRef(self.clause_raw(lit, i) & !BINARY_FLAG)
    }

    /// Check if watcher at index is binary
    #[inline]
    pub(crate) fn is_binary(&self, lit: Literal, i: usize) -> bool {
        self.clause_raw(lit, i) & BINARY_FLAG != 0
    }

    // ─── Single-literal write access ────────────────────────────────

    /// Write a packed entry at position `dst` within a literal's region.
    #[inline]
    pub(crate) fn set_packed(&mut self, lit: Literal, dst: usize, packed: u64) {
        let start = self.meta[lit.index()].offset as usize;
        self.buffer[start + dst] = packed;
    }

    /// Write a (blocker, clause) pair at position `dst` within a literal's region.
    #[inline]
    pub(crate) fn set_entry(
        &mut self,
        lit: Literal,
        dst: usize,
        blocker_raw: u32,
        clause_raw: u32,
    ) {
        let start = self.meta[lit.index()].offset as usize;
        self.buffer[start + dst] = pack(blocker_raw, clause_raw);
    }

    /// Swap-remove element at watcher index within a literal's watch list.
    ///
    /// Two-step swap pattern (AI Model 3.1 review): naive swap_remove with the
    /// last element would break the binary-first partition. Instead:
    ///
    /// - Deleting a binary entry (i < binary_count):
    ///   1. Swap with last binary entry (at binary_count - 1).
    ///   2. Swap that vacated position with the last long entry (at len - 1).
    ///   3. Decrement binary_count and len.
    ///
    /// - Deleting a long entry (i >= binary_count):
    ///   1. Swap with the last entry (at len - 1).
    ///   2. Decrement len.
    #[inline]
    pub(crate) fn swap_remove(&mut self, lit: Literal, i: usize) {
        let m = &mut self.meta[lit.index()];
        let start = m.offset as usize;
        let last = m.len as usize - 1;
        let bc = m.binary_count as usize;

        if i < bc {
            // Deleting a binary entry.
            let last_binary = bc - 1;
            // Step 1: swap deleted binary with last binary.
            if i != last_binary {
                self.buffer.swap(start + i, start + last_binary);
            }
            // Step 2: fill the vacated binary slot with the last long entry
            // (which is at position `last`), if there are any long entries.
            if last_binary < last {
                self.buffer.swap(start + last_binary, start + last);
            }
            m.binary_count -= 1;
        } else {
            // Deleting a long entry: swap with last entry.
            if i != last {
                self.buffer.swap(start + i, start + last);
            }
        }
        m.len -= 1;
        self.dead_slots += 1;
    }

    /// Truncate a literal's watch list to `new_len` entries.
    #[inline]
    pub(crate) fn truncate_lit(&mut self, lit: Literal, new_len: usize) {
        let m = &mut self.meta[lit.index()];
        let old_len = m.len as usize;
        if new_len < old_len {
            self.dead_slots += old_len - new_len;
            m.len = new_len as u32;
            // Clamp binary_count if truncation removes binary entries.
            if (m.binary_count as usize) > new_len {
                m.binary_count = new_len as u32;
            }
        }
    }

    /// Clear a single literal's watch list.
    #[inline]
    pub(crate) fn clear_lit(&mut self, lit: Literal) {
        let m = &mut self.meta[lit.index()];
        self.dead_slots += m.len as usize;
        m.len = 0;
        m.binary_count = 0;
    }

    // ─── Slice access into the unified buffer ───────────────────────

    /// Get the watch entries for a literal as an immutable slice.
    #[inline]
    pub(crate) fn entries(&self, lit: Literal) -> &[u64] {
        let m = &self.meta[lit.index()];
        let start = m.offset as usize;
        &self.buffer[start..start + m.len as usize]
    }

    /// Get the watch entries for a literal as a mutable slice.
    #[inline]
    pub(crate) fn entries_mut(&mut self, lit: Literal) -> &mut [u64] {
        let m = self.meta[lit.index()];
        let start = m.offset as usize;
        let end = start + m.len as usize;
        &mut self.buffer[start..end]
    }

    /// Raw mutable pointer to a literal's entry region and its length.
    ///
    /// Used by `propagate_bcp_unsafe` for CaDiCaL-style in-place pointer
    /// iteration. The caller must ensure no aliasing references exist and
    /// that indices stay within `[0, len)`.
    #[cfg(feature = "unsafe-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) fn entries_raw_mut(&mut self, lit: Literal) -> (*mut u64, usize) {
        let m = self.meta[lit.index()];
        let start = m.offset as usize;
        let len = m.len as usize;
        // SAFETY: start..start+len is within buffer bounds by construction.
        (unsafe { self.buffer.as_mut_ptr().add(start) }, len)
    }

    /// Unsafe set_len for in-place compaction by the unsafe BCP loop.
    ///
    /// # Safety
    /// `new_len` must be <= the current length. All entries in `[0, new_len)`
    /// must be valid (initialized). This is guaranteed by the BCP compaction
    /// invariant: `j <= i <= original_len`.
    ///
    /// BCP compaction preserves binary-first order because: (a) the watch list
    /// starts sorted (binary entries first), and (b) BCP only drops long-clause
    /// watchers (replacement found). Binary watchers are always kept. So
    /// binary_count is unchanged; we only clamp it if new_len is smaller.
    #[cfg(feature = "unsafe-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) unsafe fn set_len(&mut self, lit: Literal, new_len: usize) {
        let m = &mut self.meta[lit.index()];
        debug_assert!(new_len <= m.len as usize);
        let freed = m.len as usize - new_len;
        m.len = new_len as u32;
        self.dead_slots += freed;
        // Clamp binary_count. In normal BCP this is a no-op since binary
        // watchers are never dropped, but defensive for edge cases.
        if m.binary_count > m.len {
            m.binary_count = m.len;
        }
    }

    /// Prefetch hint for first watch entry of a literal.
    ///
    /// CaDiCaL propagate.cpp:160-166: `__builtin_prefetch(&ws[0], 0, 1)`.
    #[inline]
    pub(crate) fn prefetch_first(&self, lit: Literal) {
        let m = &self.meta[lit.index()];
        if m.len > 0 {
            let start = m.offset as usize;
            z4_prefetch::prefetch_read_l2(std::ptr::from_ref::<u64>(&self.buffer[start]));
        }
    }

    // ─── Push / add operations ──────────────────────────────────────

    /// Push a packed entry to a literal's watch list, growing if needed.
    ///
    /// Maintains the binary-first invariant: binary watches occupy
    /// `[offset..offset+binary_count)`, long watches occupy
    /// `[offset+binary_count..offset+len)`.
    ///
    /// - Binary insert: swap the first long entry to position `len`, place
    ///   the new binary entry at position `binary_count`. O(1).
    /// - Long insert: append at position `len`. O(1).
    fn push_packed(&mut self, lit: Literal, packed: u64) {
        let li = lit.index();
        let m = self.meta[li];
        let is_binary = unpack_clause(packed) & BINARY_FLAG != 0;
        if m.len < m.capacity {
            // Fast path: space available in existing region.
            let start = m.offset as usize;
            if is_binary {
                // Swap first long entry to end, insert binary at binary_count.
                let bc = m.binary_count as usize;
                if bc < m.len as usize {
                    // There is at least one long entry: move it to the end.
                    self.buffer[start + m.len as usize] = self.buffer[start + bc];
                }
                self.buffer[start + bc] = packed;
                self.meta[li].binary_count += 1;
            } else {
                // Long insert: append at end.
                self.buffer[start + m.len as usize] = packed;
            }
            self.meta[li].len += 1;
        } else {
            // Slow path: allocate new region at end of buffer.
            self.grow_and_push(li, packed);
        }
    }

    /// Grow a literal's region (allocate at end of buffer) and push one entry.
    ///
    /// Maintains binary-first invariant: copies existing entries preserving
    /// the partition, then inserts the new entry at the correct position.
    #[cold]
    fn grow_and_push(&mut self, li: usize, packed: u64) {
        let m = self.meta[li];
        let old_len = m.len as usize;
        let old_offset = m.offset as usize;
        let old_bc = m.binary_count as usize;
        let new_capacity = if old_len == 0 { 2 } else { old_len * 2 };
        let new_offset = self.buffer.len();
        let is_binary = unpack_clause(packed) & BINARY_FLAG != 0;

        // Allocate new region at the end.
        self.buffer.reserve(new_capacity);

        if is_binary {
            // Copy binary entries first.
            for i in 0..old_bc {
                self.buffer.push(self.buffer[old_offset + i]);
            }
            // Insert new binary entry.
            self.buffer.push(packed);
            // Copy long entries.
            for i in old_bc..old_len {
                self.buffer.push(self.buffer[old_offset + i]);
            }
        } else {
            // Copy all existing entries (already partitioned).
            for i in 0..old_len {
                self.buffer.push(self.buffer[old_offset + i]);
            }
            // Append new long entry.
            self.buffer.push(packed);
        }

        // Pad remaining capacity with zeros.
        for _ in (old_len + 1)..new_capacity {
            self.buffer.push(0);
        }

        // Mark old region as dead.
        self.dead_slots += m.capacity as usize;

        self.meta[li] = WatchMeta {
            offset: new_offset as u32,
            len: (old_len + 1) as u32,
            capacity: new_capacity as u32,
            binary_count: (old_bc + usize::from(is_binary)) as u32,
        };
    }

    /// Push a Watcher to a literal's watch list.
    #[inline]
    pub(crate) fn push_watcher(&mut self, lit: Literal, w: Watcher) {
        self.push_packed(lit, pack(w.blocker_raw, w.clause_raw));
    }

    /// Push raw (blocker, clause) values to a literal's watch list.
    #[inline]
    pub(crate) fn push_raw(&mut self, lit: Literal, blocker_raw: u32, clause_raw: u32) {
        self.push_packed(lit, pack(blocker_raw, clause_raw));
    }

    /// Add a watcher for a literal
    #[inline]
    pub(crate) fn add_watch(&mut self, lit: Literal, watcher: Watcher) {
        self.push_watcher(lit, watcher);
    }

    /// Set up both watches for a clause on its first two literals.
    #[inline]
    pub(crate) fn watch_clause(
        &mut self,
        clause_ref: ClauseRef,
        lit0: Literal,
        lit1: Literal,
        is_binary: bool,
    ) {
        if is_binary {
            self.add_watch(lit0, Watcher::binary(clause_ref, lit1));
            self.add_watch(lit1, Watcher::binary(clause_ref, lit0));
        } else {
            self.add_watch(lit0, Watcher::new(clause_ref, lit1));
            self.add_watch(lit1, Watcher::new(clause_ref, lit0));
        }
    }

    // ─── BCP swap pattern ───────────────────────────────────────────

    /// Swap a literal's watch entries into the standalone WatchList (deferred buffer).
    ///
    /// After this call, the literal's watch list in the unified buffer has len=0
    /// (capacity/offset preserved) and all its entries are in `deferred`.
    /// The deferred buffer is cleared first.
    pub(crate) fn swap_to_deferred(&mut self, lit: Literal, deferred: &mut WatchList) {
        deferred.entries.clear();
        let m = self.meta[lit.index()];
        let start = m.offset as usize;
        let len = m.len as usize;
        deferred
            .entries
            .extend_from_slice(&self.buffer[start..start + len]);
        // Mark the literal's region as empty. Don't add to dead_slots since
        // we'll swap back shortly and want to reuse the capacity.
        self.meta[lit.index()].len = 0;
        self.meta[lit.index()].binary_count = 0;
    }

    /// Swap entries from the standalone WatchList back into a literal's region.
    ///
    /// If the deferred buffer's length fits in the literal's existing capacity,
    /// entries are copied in-place. Otherwise, a new region is allocated.
    /// Also handles overflow entries added to this literal during the BCP scan
    /// (e.g., HBR watchers targeting false_lit in probe mode).
    ///
    /// For the no-overflow paths, BCP compaction preserves binary-first order
    /// (binary watchers are never dropped), so we just count leading binaries.
    /// For the overflow path (HBR), we merge maintaining binary-first order.
    pub(crate) fn swap_from_deferred(&mut self, lit: Literal, deferred: &mut WatchList) {
        let li = lit.index();
        let deferred_len = deferred.entries.len();
        let overflow_len = self.meta[li].len as usize;
        let total_len = deferred_len + overflow_len;

        if total_len == 0 {
            return;
        }

        let m = self.meta[li];
        if total_len <= m.capacity as usize && overflow_len == 0 {
            // Fast path: fits in existing capacity, no overflow.
            let start = m.offset as usize;
            self.buffer[start..start + deferred_len]
                .copy_from_slice(&deferred.entries);
            self.meta[li].len = deferred_len as u32;
            // Count binary entries in the compacted deferred data.
            self.meta[li].binary_count = count_binary(&deferred.entries);
        } else if overflow_len == 0 {
            // Need more capacity, no overflow. Allocate at end.
            let new_capacity = total_len.next_power_of_two().max(4);
            let new_offset = self.buffer.len();
            self.buffer.reserve(new_capacity);
            self.buffer.extend_from_slice(&deferred.entries);
            self.buffer.resize(new_offset + new_capacity, 0);
            self.dead_slots += m.capacity as usize;
            let bc = count_binary(&deferred.entries);
            self.meta[li] = WatchMeta {
                offset: new_offset as u32,
                len: deferred_len as u32,
                capacity: new_capacity as u32,
                binary_count: bc,
            };
        } else {
            // Overflow exists: merge deferred + overflow with binary-first order.
            let start = m.offset as usize;
            let overflow: Vec<u64> = self.buffer[start..start + overflow_len].to_vec();
            let new_capacity = total_len.next_power_of_two().max(4);
            let new_offset = self.buffer.len();
            self.buffer.reserve(new_capacity);

            // Merge: all binary entries first (from deferred then overflow),
            // then all long entries (from deferred then overflow).
            let mut bc: u32 = 0;
            // Binary from deferred.
            for &e in &deferred.entries {
                if unpack_clause(e) & BINARY_FLAG != 0 {
                    self.buffer.push(e);
                    bc += 1;
                }
            }
            // Binary from overflow.
            for &e in &overflow {
                if unpack_clause(e) & BINARY_FLAG != 0 {
                    self.buffer.push(e);
                    bc += 1;
                }
            }
            // Long from deferred.
            for &e in &deferred.entries {
                if unpack_clause(e) & BINARY_FLAG == 0 {
                    self.buffer.push(e);
                }
            }
            // Long from overflow.
            for &e in &overflow {
                if unpack_clause(e) & BINARY_FLAG == 0 {
                    self.buffer.push(e);
                }
            }

            // Pad remaining capacity.
            self.buffer.resize(new_offset + new_capacity, 0);
            self.dead_slots += self.meta[li].capacity as usize;
            self.meta[li] = WatchMeta {
                offset: new_offset as u32,
                len: total_len as u32,
                capacity: new_capacity as u32,
                binary_count: bc,
            };
        }

        deferred.entries.clear();
    }

    // ─── Bulk operations ────────────────────────────────────────────

    /// Assert that all watch lists satisfy the binary-first invariant.
    ///
    /// In debug builds, verifies that entries [0..binary_count) have BINARY_FLAG
    /// set and entries [binary_count..len) do not. No-op in release builds.
    ///
    /// Replaces the previous `sort_all_binary_first()` which was O(total_watches).
    /// The invariant is now maintained incrementally on every insert/remove.
    pub(crate) fn debug_assert_binary_first(&self) {
        #[cfg(debug_assertions)]
        {
            for li in 0..self.meta.len() {
                let m = self.meta[li];
                let start = m.offset as usize;
                let bc = m.binary_count as usize;
                let len = m.len as usize;
                debug_assert!(
                    bc <= len,
                    "BUG: binary_count ({bc}) > len ({len}) for lit index {li}"
                );
                for i in 0..bc {
                    debug_assert!(
                        unpack_clause(self.buffer[start + i]) & BINARY_FLAG != 0,
                        "BUG: entry {i} in binary zone (0..{bc}) of lit {li} is not binary"
                    );
                }
                for i in bc..len {
                    debug_assert!(
                        unpack_clause(self.buffer[start + i]) & BINARY_FLAG == 0,
                        "BUG: entry {i} in long zone ({bc}..{len}) of lit {li} is binary"
                    );
                }
            }
        }
    }

    /// Remap clause refs in all watch lists using a relocation map.
    ///
    /// Recounts binary entries per literal after remapping since entries may
    /// be dropped (dead clauses). Uses single-pass compaction (matching the
    /// original algorithm) and then recounts binary entries. The binary-first
    /// invariant is preserved because: (a) the input is already binary-first,
    /// (b) the single-pass stable compaction preserves relative order.
    pub(crate) fn remap_clause_refs(&mut self, remap: &[u32]) {
        for li in 0..self.meta.len() {
            let m = self.meta[li];
            let start = m.offset as usize;
            let len = m.len as usize;
            let mut j = 0;
            let mut bc: u32 = 0;
            for i in 0..len {
                let entry = self.buffer[start + i];
                let clause_raw = unpack_clause(entry);
                let blocker_raw = unpack_blocker(entry);
                let is_binary = clause_raw & BINARY_FLAG != 0;
                let old_offset = (clause_raw & !BINARY_FLAG) as usize;
                if old_offset >= remap.len() || remap[old_offset] == u32::MAX {
                    continue;
                }
                let new_offset = remap[old_offset];
                debug_assert!(
                    new_offset & BINARY_FLAG == 0,
                    "BUG: arena offset {new_offset} collides with BINARY_FLAG"
                );
                let new_clause_raw = new_offset | if is_binary { BINARY_FLAG } else { 0 };
                self.buffer[start + j] = pack(blocker_raw, new_clause_raw);
                if is_binary {
                    bc += 1;
                }
                j += 1;
            }
            if j < len {
                self.dead_slots += len - j;
                self.meta[li].len = j as u32;
            }
            self.meta[li].binary_count = bc;
        }
    }

    /// Shrink the unified buffer if dead slots exceed a threshold.
    pub(crate) fn shrink_capacity(&mut self) {
        if self.dead_slots > self.buffer.len() / 4 {
            self.defragment();
        }
    }

    /// Compact the unified buffer (Kissat `kissat_defrag_vectors`).
    ///
    /// Sorts non-empty regions by offset and copies forward, reclaiming gaps.
    /// Preserves `binary_count` for each literal's region.
    pub(crate) fn defragment(&mut self) {
        if self.buffer.is_empty() {
            self.dead_slots = 0;
            return;
        }

        let mut active: Vec<usize> = (0..self.meta.len())
            .filter(|&li| self.meta[li].len > 0)
            .collect();
        active.sort_by_key(|&li| self.meta[li].offset);

        let mut write_pos: usize = 0;
        for &li in &active {
            let m = self.meta[li];
            let src_start = m.offset as usize;
            let len = m.len as usize;
            if write_pos != src_start {
                self.buffer.copy_within(src_start..src_start + len, write_pos);
            }
            self.meta[li] = WatchMeta {
                offset: write_pos as u32,
                len: len as u32,
                capacity: len as u32,
                binary_count: m.binary_count,
            };
            write_pos += len;
        }

        for li in 0..self.meta.len() {
            if self.meta[li].len == 0 {
                self.meta[li] = WatchMeta::default();
            }
        }

        self.buffer.truncate(write_pos);
        self.buffer.shrink_to_fit();
        self.dead_slots = 0;
    }

    /// Retain only entries for a literal where the predicate returns `true`.
    ///
    /// Preserves binary-first order (stable compaction) and recounts binary entries.
    #[allow(dead_code)]
    pub(crate) fn retain_lit(&mut self, lit: Literal, mut keep: impl FnMut(u32, u32) -> bool) {
        let li = lit.index();
        let m = self.meta[li];
        let start = m.offset as usize;
        let len = m.len as usize;
        let mut j = 0;
        let mut bc: u32 = 0;
        for i in 0..len {
            let entry = self.buffer[start + i];
            let clause_raw = unpack_clause(entry);
            let blocker_raw = unpack_blocker(entry);
            if keep(clause_raw, blocker_raw) {
                self.buffer[start + j] = entry;
                if clause_raw & BINARY_FLAG != 0 {
                    bc += 1;
                }
                j += 1;
            }
        }
        if j < len {
            self.dead_slots += len - j;
            self.meta[li].len = j as u32;
        }
        self.meta[li].binary_count = bc;
    }

    /// Remove watchers for JIT-compiled clauses from all watch lists.
    #[cfg(feature = "jit")]
    pub(crate) fn detach_irredundant_watches(
        &mut self,
        should_keep: impl Fn(usize) -> bool,
    ) -> usize {
        let mut total_removed = 0;
        for li in 0..self.meta.len() {
            let before = self.meta[li].len as usize;
            let lit = Literal::from_index(li);
            self.retain_lit(lit, |clause_raw, _blocker_raw| {
                if clause_raw & BINARY_FLAG != 0 {
                    return true;
                }
                should_keep(clause_raw as usize)
            });
            total_removed += before - self.meta[li].len as usize;
        }
        total_removed
    }

    /// Count total watches for a clause (used for verification)
    #[cfg(test)]
    pub(crate) fn count_watches_for_clause(&self, clause_ref: ClauseRef) -> usize {
        let target = clause_ref.0;
        let mut count = 0;
        for li in 0..self.meta.len() {
            let m = self.meta[li];
            let start = m.offset as usize;
            for i in 0..m.len as usize {
                let entry = self.buffer[start + i];
                let cr = unpack_clause(entry) & !BINARY_FLAG;
                if cr == target {
                    count += 1;
                }
            }
        }
        count
    }

    /// Heap-backed bytes used by the unified buffer plus the meta table.
    #[cfg(test)]
    pub(crate) fn heap_bytes(&self) -> usize {
        use std::mem::size_of;
        self.buffer.capacity() * size_of::<u64>()
            + self.meta.capacity() * size_of::<WatchMeta>()
    }

    /// Capacity of the meta table (for statistics).
    #[cfg(test)]
    pub(crate) fn outer_capacity(&self) -> usize {
        self.meta.capacity()
    }

    /// Get the length of a watch list (kani proofs only)
    #[inline]
    #[cfg(kani)]
    pub(crate) fn watch_count(&self, lit: Literal) -> usize {
        self.meta[lit.index()].len as usize
    }

    /// Capacity of a single literal's watch list region.
    #[inline]
    pub(crate) fn capacity_of(&self, lit: Literal) -> usize {
        self.meta[lit.index()].capacity as usize
    }

    /// Return an immutable view of a literal's watch list.
    #[inline]
    pub(crate) fn get_watches(&self, lit: Literal) -> WatchListView<'_> {
        WatchListView { lists: self, lit }
    }

    /// Return a mutable view of a literal's watch list.
    #[inline]
    pub(crate) fn get_watches_mut(&mut self, lit: Literal) -> WatchListViewMut<'_> {
        WatchListViewMut { lists: self, lit }
    }
}

// ─── Watch list view types ─────────────────────────────────────────

/// Immutable view into a single literal's watch list within a `WatchedLists`.
///
/// Wraps `(&WatchedLists, Literal)` and delegates per-watcher read methods.
pub(crate) struct WatchListView<'a> {
    lists: &'a WatchedLists,
    lit: Literal,
}

impl<'a> WatchListView<'a> {
    /// Number of watchers in this list.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.lists.len_of(self.lit)
    }

    /// Allocated capacity for this literal's region.
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.lists.capacity_of(self.lit)
    }

    /// Get the clause reference at watcher index (strips BINARY_FLAG).
    #[inline]
    pub(crate) fn clause_ref(&self, i: usize) -> ClauseRef {
        self.lists.clause_ref(self.lit, i)
    }

    /// Get the raw clause value at watcher index (includes BINARY_FLAG).
    #[inline]
    pub(crate) fn clause_raw(&self, i: usize) -> u32 {
        self.lists.clause_raw(self.lit, i)
    }

    /// Get the raw blocker value at watcher index.
    #[inline]
    pub(crate) fn blocker_raw(&self, i: usize) -> u32 {
        self.lists.blocker_raw(self.lit, i)
    }

    /// Get the blocker as a `Literal` at watcher index.
    #[inline]
    pub(crate) fn blocker(&self, i: usize) -> Literal {
        self.lists.blocker(self.lit, i)
    }

    /// Check if watcher at index is binary.
    #[inline]
    pub(crate) fn is_binary(&self, i: usize) -> bool {
        self.lists.is_binary(self.lit, i)
    }

    /// Get the packed entry at watcher index.
    #[inline]
    pub(crate) fn entry(&self, i: usize) -> u64 {
        self.lists.entry_at(self.lit, i)
    }
}

/// Mutable view into a single literal's watch list within a `WatchedLists`.
///
/// Wraps `(&mut WatchedLists, Literal)` and delegates read/write methods.
pub(crate) struct WatchListViewMut<'a> {
    lists: &'a mut WatchedLists,
    lit: Literal,
}

impl<'a> WatchListViewMut<'a> {
    /// Number of watchers in this list.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.lists.len_of(self.lit)
    }

    /// Allocated capacity for this literal's region.
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.lists.capacity_of(self.lit)
    }

    /// Get the clause reference at watcher index (strips BINARY_FLAG).
    #[inline]
    pub(crate) fn clause_ref(&self, i: usize) -> ClauseRef {
        self.lists.clause_ref(self.lit, i)
    }

    /// Get the raw clause value at watcher index (includes BINARY_FLAG).
    #[inline]
    pub(crate) fn clause_raw(&self, i: usize) -> u32 {
        self.lists.clause_raw(self.lit, i)
    }

    /// Get the raw blocker value at watcher index.
    #[inline]
    pub(crate) fn blocker_raw(&self, i: usize) -> u32 {
        self.lists.blocker_raw(self.lit, i)
    }

    /// Get the blocker as a `Literal` at watcher index.
    #[inline]
    pub(crate) fn blocker(&self, i: usize) -> Literal {
        self.lists.blocker(self.lit, i)
    }

    /// Check if watcher at index is binary.
    #[inline]
    pub(crate) fn is_binary(&self, i: usize) -> bool {
        self.lists.is_binary(self.lit, i)
    }

    /// Get the packed entry at watcher index.
    #[inline]
    pub(crate) fn entry(&self, i: usize) -> u64 {
        self.lists.entry_at(self.lit, i)
    }

    /// Write a (blocker, clause) pair at position `dst`.
    #[inline]
    pub(crate) fn set_entry(&mut self, dst: usize, blocker_raw: u32, clause_raw: u32) {
        self.lists.set_entry(self.lit, dst, blocker_raw, clause_raw);
    }

    /// Write a packed entry at position `dst`.
    #[inline]
    pub(crate) fn set_packed(&mut self, dst: usize, packed: u64) {
        self.lists.set_packed(self.lit, dst, packed);
    }

    /// Swap-remove element at watcher index (O(1) removal).
    #[inline]
    pub(crate) fn swap_remove(&mut self, i: usize) {
        self.lists.swap_remove(self.lit, i);
    }

    /// Truncate the watch list to `new_len` entries.
    #[inline]
    pub(crate) fn truncate(&mut self, new_len: usize) {
        self.lists.truncate_lit(self.lit, new_len);
    }

    /// Push a `Watcher` to this literal's watch list.
    #[inline]
    pub(crate) fn push_watcher(&mut self, w: Watcher) {
        self.lists.push_watcher(self.lit, w);
    }

    /// Clear all entries in this literal's watch list.
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.lists.clear_lit(self.lit);
    }

    /// Raw mutable pointer to the entry region and its length.
    ///
    /// See [`WatchedLists::entries_raw_mut`] for safety requirements.
    #[cfg(feature = "unsafe-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) fn entries_raw_mut(&mut self) -> (*mut u64, usize) {
        self.lists.entries_raw_mut(self.lit)
    }

    /// Unsafe set_len for in-place compaction.
    ///
    /// See [`WatchedLists::set_len`] for safety requirements.
    #[cfg(feature = "unsafe-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) unsafe fn set_len(&mut self, new_len: usize) {
        // SAFETY: Caller guarantees new_len <= current length and entries
        // in [0, new_len) are valid. Delegates to WatchedLists::set_len.
        unsafe {
            self.lists.set_len(self.lit, new_len);
        }
    }
}
