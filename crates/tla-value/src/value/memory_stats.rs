// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(debug_assertions)]
pub(crate) static LAZY_FUNC_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static MEMO_ENTRY_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static ARRAY_STATE_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static ARRAY_STATE_BYTES: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static VALUE_CLONE_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static FUNC_ENTRY_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static FUNC_EXCEPT_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static FUNC_EXCEPT_CLONE_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static SET_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static SET_CACHE_HIT_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static INT_FUNC_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static INT_FUNC_ENTRY_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static INT_FUNC_EXCEPT_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static INT_FUNC_EXCEPT_CLONE_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(crate) static INT_FUNC_BYTES: AtomicUsize = AtomicUsize::new(0);

#[cfg(debug_assertions)]
pub(crate) fn reset() {
    LAZY_FUNC_COUNT.store(0, Ordering::Relaxed);
    MEMO_ENTRY_COUNT.store(0, Ordering::Relaxed);
    ARRAY_STATE_COUNT.store(0, Ordering::Relaxed);
    ARRAY_STATE_BYTES.store(0, Ordering::Relaxed);
    VALUE_CLONE_COUNT.store(0, Ordering::Relaxed);
    FUNC_ENTRY_COUNT.store(0, Ordering::Relaxed);
    FUNC_EXCEPT_COUNT.store(0, Ordering::Relaxed);
    FUNC_EXCEPT_CLONE_COUNT.store(0, Ordering::Relaxed);
    SET_COUNT.store(0, Ordering::Relaxed);
    SET_CACHE_HIT_COUNT.store(0, Ordering::Relaxed);
    INT_FUNC_COUNT.store(0, Ordering::Relaxed);
    INT_FUNC_ENTRY_COUNT.store(0, Ordering::Relaxed);
    INT_FUNC_EXCEPT_COUNT.store(0, Ordering::Relaxed);
    INT_FUNC_EXCEPT_CLONE_COUNT.store(0, Ordering::Relaxed);
    INT_FUNC_BYTES.store(0, Ordering::Relaxed);
}

#[cfg(not(debug_assertions))]
pub(crate) fn reset() {}

#[cfg(debug_assertions)]
fn format_bytes(bytes: usize) -> String {
    if bytes >= 1024 * 1024 * 1024 {
        format!("{:.2} GB", bytes as f64 / (1024.0 * 1024.0 * 1024.0))
    } else if bytes >= 1024 * 1024 {
        format!("{:.2} MB", bytes as f64 / (1024.0 * 1024.0))
    } else if bytes >= 1024 {
        format!("{:.2} KB", bytes as f64 / 1024.0)
    } else {
        format!("{} bytes", bytes)
    }
}

#[cfg(debug_assertions)]
pub fn print_stats() {
    eprintln!("=== Memory Statistics ===");
    eprintln!(
        "LazyFuncValue instances: {}",
        LAZY_FUNC_COUNT.load(Ordering::Relaxed)
    );
    eprintln!("Memo entries: {}", MEMO_ENTRY_COUNT.load(Ordering::Relaxed));
    let array_state_count = ARRAY_STATE_COUNT.load(Ordering::Relaxed);
    let array_state_bytes = ARRAY_STATE_BYTES.load(Ordering::Relaxed);
    eprintln!(
        "ArrayState instances: {} ({})",
        array_state_count,
        format_bytes(array_state_bytes)
    );
    if array_state_count > 0 {
        eprintln!(
            "  Avg bytes/ArrayState: {}",
            array_state_bytes / array_state_count
        );
    }
    eprintln!(
        "Value clones: {}",
        VALUE_CLONE_COUNT.load(Ordering::Relaxed)
    );
    eprintln!(
        "FuncValue entries: {}",
        FUNC_ENTRY_COUNT.load(Ordering::Relaxed)
    );
    eprintln!(
        "FuncValue except ops: {}",
        FUNC_EXCEPT_COUNT.load(Ordering::Relaxed)
    );
    eprintln!(
        "FuncValue except clones: {}",
        FUNC_EXCEPT_CLONE_COUNT.load(Ordering::Relaxed)
    );
    eprintln!(
        "Set instances (calls): {}",
        SET_COUNT.load(Ordering::Relaxed)
    );
    eprintln!(
        "Set cache hits: {}",
        SET_CACHE_HIT_COUNT.load(Ordering::Relaxed)
    );
    let int_func_count = INT_FUNC_COUNT.load(Ordering::Relaxed);
    let int_func_bytes = INT_FUNC_BYTES.load(Ordering::Relaxed);
    eprintln!(
        "IntIntervalFunc instances: {} ({})",
        int_func_count,
        format_bytes(int_func_bytes)
    );
    eprintln!(
        "IntIntervalFunc entries: {}",
        INT_FUNC_ENTRY_COUNT.load(Ordering::Relaxed)
    );
    eprintln!(
        "IntIntervalFunc except ops: {}",
        INT_FUNC_EXCEPT_COUNT.load(Ordering::Relaxed)
    );
    eprintln!(
        "IntIntervalFunc except clones: {}",
        INT_FUNC_EXCEPT_CLONE_COUNT.load(Ordering::Relaxed)
    );

    if let Some(n) = super::intern_tables::set_intern_table_len() {
        eprintln!("Unique interned sets: {}", n);
    }
    if let Some(n) = super::intern_tables::int_func_intern_table_len() {
        eprintln!("Unique interned IntFuncs: {}", n);
    }

    eprintln!("--- Size constants ---");
    eprintln!(
        "sizeof(Value): {} bytes",
        std::mem::size_of::<super::Value>()
    );

    let array_state_bytes = ARRAY_STATE_BYTES.load(Ordering::Relaxed);
    let int_func_bytes = INT_FUNC_BYTES.load(Ordering::Relaxed);
    eprintln!("--- Memory Estimates ---");
    eprintln!(
        "ArrayState heap (Values): {}",
        format_bytes(array_state_bytes)
    );
    eprintln!("IntIntervalFunc heap: {}", format_bytes(int_func_bytes));
    eprintln!(
        "Total tracked: {}",
        format_bytes(array_state_bytes + int_func_bytes)
    );
    eprintln!("=========================");
}

#[cfg(not(debug_assertions))]
pub fn print_stats() {
    eprintln!("Memory statistics are only available in debug builds");
}

#[inline]
pub(crate) fn inc_int_func_except() {
    #[cfg(debug_assertions)]
    INT_FUNC_EXCEPT_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_int_func_except_clone() {
    #[cfg(debug_assertions)]
    INT_FUNC_EXCEPT_CLONE_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_lazy_func() {
    #[cfg(debug_assertions)]
    LAZY_FUNC_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub fn inc_memo_entry() {
    #[cfg(debug_assertions)]
    MEMO_ENTRY_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub fn inc_array_state() {
    #[cfg(debug_assertions)]
    ARRAY_STATE_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub fn inc_array_state_bytes(num_vars: usize) {
    #[cfg(debug_assertions)]
    {
        let value_size = std::mem::size_of::<super::Value>();
        let bytes = num_vars * value_size + 56;
        ARRAY_STATE_BYTES.fetch_add(bytes, Ordering::Relaxed);
    }
}

#[inline]
pub(crate) fn inc_value_clone() {
    #[cfg(debug_assertions)]
    VALUE_CLONE_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_func_entries(count: usize) {
    #[cfg(debug_assertions)]
    FUNC_ENTRY_COUNT.fetch_add(count, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_func_except() {
    #[cfg(debug_assertions)]
    FUNC_EXCEPT_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_func_except_clone() {
    #[cfg(debug_assertions)]
    FUNC_EXCEPT_CLONE_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_set() {
    #[cfg(debug_assertions)]
    SET_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_set_cache_hit() {
    #[cfg(debug_assertions)]
    SET_CACHE_HIT_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn inc_int_func(entries: usize) {
    #[cfg(debug_assertions)]
    {
        INT_FUNC_COUNT.fetch_add(1, Ordering::Relaxed);
        INT_FUNC_ENTRY_COUNT.fetch_add(entries, Ordering::Relaxed);
        let value_size = std::mem::size_of::<super::Value>();
        let bytes = 16 + 24 + entries * value_size;
        INT_FUNC_BYTES.fetch_add(bytes, Ordering::Relaxed);
    }
}
