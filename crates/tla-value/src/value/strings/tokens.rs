// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use dashmap::DashMap;
use std::sync::atomic::{AtomicU32, Ordering as AtomicOrdering};
use std::sync::{Arc, OnceLock};

// ============================================================================
// TLC-Compatible String Token Registry (Part of #3193)
// ============================================================================
//
// TLC compares strings by intern-token order (`UniqueString.tok`), NOT lexical
// order. Strings get monotonically increasing tokens in first-seen/parse order.
// This registry replicates that contract for TLC-normalized set enumeration.
//
// Separate from STRING_INTERN_TABLE because:
// - The intern table is capped and can be cleared to reclaim memory
// - TLC token order must be append-only for the life of a model-checking run
// - Different lifetimes: intern table = memory optimization, token registry = ordering contract

/// Global TLC string token registry. Maps string content -> monotonic token.
/// Append-only: tokens are assigned once and never removed during a run.
static TLC_STRING_TOKENS: OnceLock<DashMap<Arc<str>, u32>> = OnceLock::new();

/// Counter for the next token to assign.
static TLC_STRING_TOKEN_COUNTER: AtomicU32 = AtomicU32::new(1);

/// Get the TLC string token table, initializing if needed.
#[inline]
pub(super) fn get_token_table() -> &'static DashMap<Arc<str>, u32> {
    TLC_STRING_TOKENS.get_or_init(DashMap::new)
}

/// Get or assign a TLC-compatible token for a string.
///
/// Returns a monotonically increasing u32 reflecting first-seen order.
/// Thread-safe: concurrent calls for the same string return the same token;
/// concurrent calls for different strings get distinct tokens.
///
/// Part of #3193: TLC's `UniqueString.compareTo()` compares by `this.tok - other.tok`.
#[inline]
pub fn tlc_string_token(s: &Arc<str>) -> u32 {
    // Part of #3285: Route through frozen snapshot + worker-local overlay
    // during parallel BFS. Tokens are append-only within a run, so the frozen
    // snapshot captures all parse-time tokens and the overlay handles new ones.
    if super::super::parallel_intern::is_parallel_intern_active() {
        if let Some(tok) = super::super::parallel_intern::parallel_tlc_string_token(s) {
            return tok;
        }
    }

    let table = get_token_table();

    // Fast path: already registered
    if let Some(tok) = table.get(s.as_ref()) {
        return *tok.value();
    }

    // Slow path: register with a new token
    // Use entry API for atomicity
    *table
        .entry(Arc::clone(s))
        .or_insert_with(|| TLC_STRING_TOKEN_COUNTER.fetch_add(1, AtomicOrdering::Relaxed))
        .value()
}

/// Snapshot the TLC string token table into an immutable FxHashMap.
///
/// Part of #3285: Used by `parallel_intern::freeze_value_interners()` to create
/// the frozen snapshot before spawning BFS workers.
pub(in crate::value) fn snapshot_tlc_string_tokens() -> rustc_hash::FxHashMap<Arc<str>, u32> {
    let table = get_token_table();
    table
        .iter()
        .map(|entry| (Arc::clone(entry.key()), *entry.value()))
        .collect()
}

/// Get the current TLC string token counter value.
///
/// Part of #3285: Worker-local token assignment needs a starting counter
/// that won't collide with frozen tokens.
pub(in crate::value) fn tlc_string_token_counter_value() -> u32 {
    TLC_STRING_TOKEN_COUNTER.load(AtomicOrdering::Relaxed)
}

/// Clear the TLC string token registry.
///
/// Call between model checking runs. Unlike the intern table, this should only
/// be cleared between runs -- clearing mid-run would break TLC ordering parity.
pub fn clear_tlc_string_tokens() {
    if let Some(table) = TLC_STRING_TOKENS.get() {
        table.clear();
    }
    TLC_STRING_TOKEN_COUNTER.store(1, AtomicOrdering::Relaxed);
}
