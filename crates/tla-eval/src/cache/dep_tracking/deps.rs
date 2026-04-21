// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dependency data structures: `DepMap`, `VarDepMap`, `OpEvalDeps`.
//!
//! These track which state variables, next-state variables, and captured
//! locals were read during operator evaluation.

use crate::value::Value;
use crate::var_index::VarIndex;
use smallvec::SmallVec;
use tla_core::name_intern::NameId;
use tla_value::CompactValue;

/// Part of #3025: Inline sorted map for tiny dep sets (typically 1-5 entries).
/// Replaces BTreeMap to avoid per-node heap allocations. Linear scan is faster
/// than tree traversal for n <= ~8. SmallVec<4> stores up to 4 entries inline.
pub(crate) type DepMap<K, V> = SmallVec<[(K, V); 4]>;

/// Find existing entry by key in a DepMap. Returns index if found.
#[inline]
fn dep_map_find<K: Eq, V>(map: &DepMap<K, V>, key: &K) -> Option<usize> {
    map.iter().position(|(k, _)| k == key)
}

/// Check if a DepMap contains a given key.
#[inline]
pub(crate) fn dep_map_contains_key<K: Eq, V>(map: &DepMap<K, V>, key: &K) -> bool {
    map.iter().any(|(k, _)| k == key)
}

/// Fix #2414: Dense variable dep map indexed by VarIndex for O(1) record/lookup.
///
/// Replaces `DepMap<VarIndex, Value>` (linear scan per access) with direct
/// array indexing. Typical specs have <20 state variables, so the SmallVec<8>
/// inline capacity covers most cases without heap allocation.
///
/// Part of #3579: Stores `CompactValue` (8B) instead of `Option<Value>` (25B)
/// using `CompactValue::nil()` as the "no dep recorded" sentinel. 3x smaller
/// dep arrays reduce cache pressure on the dep tracking hot path.
///
/// Complexity improvement:
/// - `record_state`/`record_next`: O(n) → O(1)
/// - `merge_from` state/next: O(n*m) → O(n)
#[derive(Clone)]
pub(crate) struct VarDepMap {
    entries: SmallVec<[CompactValue; 8]>,
    count: u16,
}

impl Default for VarDepMap {
    fn default() -> Self {
        Self {
            entries: SmallVec::new(),
            count: 0,
        }
    }
}

impl VarDepMap {
    /// Record a variable read. Returns `true` if the value conflicts with
    /// a previously recorded value for the same variable (inconsistency).
    #[inline]
    pub(crate) fn record(&mut self, idx: VarIndex, value: &Value) -> bool {
        let i = idx.as_usize();
        if i >= self.entries.len() {
            self.entries.resize(i + 1, CompactValue::nil());
        }
        let existing = &self.entries[i];
        if existing.is_nil() {
            self.entries[i] = CompactValue::from(value);
            self.count += 1;
            false
        } else {
            // Part of #3579: compare stored CompactValue against new Value
            // without materializing either side unnecessarily.
            !existing.matches_value(value)
        }
    }

    /// Record from a CompactValue directly (used by merge_from).
    #[inline]
    fn record_compact(&mut self, idx: VarIndex, cv: &CompactValue) -> bool {
        let i = idx.as_usize();
        if i >= self.entries.len() {
            self.entries.resize(i + 1, CompactValue::nil());
        }
        let existing = &self.entries[i];
        if existing.is_nil() {
            self.entries[i] = cv.clone();
            self.count += 1;
            false
        } else {
            existing != cv
        }
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.count == 0
    }

    #[inline]
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn len(&self) -> usize {
        self.count as usize
    }

    /// Check if a variable is recorded.
    #[inline]
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn contains_key(&self, idx: &VarIndex) -> bool {
        self.entries
            .get(idx.as_usize())
            .is_some_and(|v| !v.is_nil())
    }

    /// Iterate over recorded (VarIndex, &CompactValue) pairs.
    ///
    /// Part of #3579: yields CompactValue references instead of Value
    /// for zero-alloc comparison on the cache validation hot path.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (VarIndex, &CompactValue)> {
        self.entries.iter().enumerate().filter_map(|(i, cv)| {
            if cv.is_nil() {
                None
            } else {
                Some((VarIndex(i as u16), cv))
            }
        })
    }

    /// Construct from a slice of (VarIndex, Value) pairs. For test construction.
    #[cfg(test)]
    pub(crate) fn from_entries(entries: &[(VarIndex, Value)]) -> Self {
        let mut map = Self::default();
        for (idx, value) in entries {
            map.record(*idx, value);
        }
        map
    }
}

#[derive(Clone, Default)]
pub(crate) struct OpEvalDeps {
    // Captured locals from the *caller* scope (below base_stack_len).
    // These matter for LET-defined operators that close over bound variables.
    // Part of #3025: SmallVec replaces BTreeMap for 0-3 entry dep sets.
    // Part of #3579: local dep values use CompactValue to avoid cloning full
    // Value payloads on the cache-hit path.
    pub(crate) local: DepMap<NameId, CompactValue>,
    // Reads of unprimed state variables.
    // Fix #2414: VarDepMap for O(1) lookup instead of O(n) linear scan.
    pub(crate) state: VarDepMap,
    // Reads of primed (next-state) variables, plus unprimed reads while evaluating in next-state mode.
    // Fix #2414: VarDepMap for O(1) lookup instead of O(n) linear scan.
    pub(crate) next: VarDepMap,
    pub(crate) inconsistent: bool,
    // Fix #2991: Track state/next inconsistency separately from local inconsistency.
    pub(crate) state_next_inconsistent: bool,
    // Fix #3062: Track TLCGet("level") dependency for cache invalidation.
    // When an operator reads TLCGet("level"), the BFS level at read time is stored here.
    // Cache entries with a recorded tlc_level are only valid when ctx.tlc_level matches.
    pub(crate) tlc_level: Option<u32>,
    // Fix #3447: Track whether this evaluation touched an INSTANCE LazyBinding.
    // When true, the result may not be stored in a persistent zero-arg/nary partition
    // even if state/next/local/tlc_level are all empty. This prevents stale INSTANCE-
    // mediated operator results from surviving across state boundaries.
    pub(crate) instance_lazy_read: bool,
}

impl OpEvalDeps {
    pub(crate) fn record_local(&mut self, name_id: NameId, value: &Value) {
        if let Some(idx) = dep_map_find(&self.local, &name_id) {
            if !self.local[idx].1.matches_value(value) {
                self.inconsistent = true;
            }
        } else {
            self.local.push((name_id, CompactValue::from(value)));
        }
    }

    #[inline]
    fn record_local_compact(&mut self, name_id: NameId, value: &CompactValue) {
        if let Some(idx) = dep_map_find(&self.local, &name_id) {
            if self.local[idx].1 != *value {
                self.inconsistent = true;
            }
        } else {
            self.local.push((name_id, value.clone()));
        }
    }

    pub(crate) fn record_state(&mut self, idx: VarIndex, value: &Value) {
        if self.state.record(idx, value) {
            self.inconsistent = true;
            self.state_next_inconsistent = true;
        }
    }

    pub(crate) fn record_next(&mut self, idx: VarIndex, value: &Value) {
        if self.next.record(idx, value) {
            self.inconsistent = true;
            self.state_next_inconsistent = true;
        }
    }

    /// Fix #3062: Record that this operator evaluation read TLCGet("level").
    /// If the operator reads the level multiple times and gets different values,
    /// mark as inconsistent (should not happen in practice since level is stable
    /// within a single state evaluation).
    pub(crate) fn record_tlc_level(&mut self, level: u32) {
        match self.tlc_level {
            Some(prev) if prev != level => {
                self.inconsistent = true;
            }
            Some(_) => {} // same level, no-op
            None => {
                self.tlc_level = Some(level);
            }
        }
    }

    pub(crate) fn merge_from(&mut self, other: &OpEvalDeps) {
        if other.inconsistent {
            self.inconsistent = true;
        }
        if other.state_next_inconsistent {
            self.state_next_inconsistent = true;
        }
        // Fix #3447: Propagate instance_lazy_read taint.
        if other.instance_lazy_read {
            self.instance_lazy_read = true;
        }
        for (name_id, value) in &other.local {
            self.record_local_compact(*name_id, value);
        }
        for (idx, cv) in other.state.iter() {
            if self.state.record_compact(idx, cv) {
                self.inconsistent = true;
                self.state_next_inconsistent = true;
            }
        }
        for (idx, cv) in other.next.iter() {
            if self.next.record_compact(idx, cv) {
                self.inconsistent = true;
                self.state_next_inconsistent = true;
            }
        }
        // Fix #3062: Merge tlc_level dependency.
        if let Some(level) = other.tlc_level {
            self.record_tlc_level(level);
        }
    }

    /// Part of #2991: Strip local deps that were internal to the operator evaluation.
    ///
    /// After a dep tracking frame completes, local deps whose NameId is NOT found
    /// in the pre-evaluation binding chain (at depth < base_stack_len) are internal
    /// iteration variables (quantifiers, comprehensions). These should not affect
    /// cache validity.
    ///
    /// `record_local_read` correctly filters DIRECT reads using the depth check,
    /// but deps arriving via `propagate_cached_deps` (from Instance binding deps
    /// or nested operator dep tracking) bypass this check. This method applies
    /// the same filter retroactively.
    ///
    /// If filtering removes all local deps and state/next had no conflicts,
    /// `inconsistent` is cleared since it was caused exclusively by internal locals.
    ///
    pub(crate) fn strip_internal_locals(
        &mut self,
        bindings: &crate::binding_chain::BindingChain,
        base_stack_len: usize,
    ) {
        if self.local.is_empty() {
            return;
        }
        self.local.retain(|(name_id, _)| {
            // Keep the dep only if the binding existed BEFORE the evaluation started
            // (i.e., it's an external captured variable, not an internal iteration variable).
            bindings
                .lookup_local_depth(*name_id)
                .is_some_and(|depth| depth < base_stack_len)
        });
        // If all local deps were internal and state/next had no conflicts,
        // the inconsistency was caused solely by internal locals — clear it.
        if self.local.is_empty() && !self.state_next_inconsistent {
            self.inconsistent = false;
        }
    }
}
