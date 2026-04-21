// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn prefetch_null_is_safe() {
    // Prefetching null must not panic or fault.
    prefetch_read_l2(core::ptr::null::<u8>());
}

#[test]
fn prefetch_valid_address() {
    let data = [1u64; 16];
    prefetch_read_l2(data.as_ptr());
}

#[test]
fn prefetch_stack_address() {
    let x = 42u32;
    prefetch_read_l2(&raw const x);
}

#[test]
fn val_at_in_bounds() {
    let vals: Vec<i8> = vec![0, 1, -1, 0, 1, -1];
    assert_eq!(val_at(&vals, 0), 0);
    assert_eq!(val_at(&vals, 1), 1);
    assert_eq!(val_at(&vals, 2), -1);
    assert_eq!(val_at(&vals, 5), -1);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of bounds")]
fn val_at_out_of_bounds_panics_in_debug() {
    let vals: Vec<i8> = vec![0, 1, -1];
    let _ = val_at(&vals, 3);
}

#[test]
fn word_at_in_bounds() {
    let words: Vec<u32> = vec![10, 20, 30, 40];
    assert_eq!(word_at(&words, 0), 10);
    assert_eq!(word_at(&words, 3), 40);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of bounds")]
fn word_at_out_of_bounds_panics_in_debug() {
    let words: Vec<u32> = vec![10, 20];
    let _ = word_at(&words, 2);
}

#[test]
fn entry_at_in_bounds() {
    let entries: Vec<u64> = vec![0xDEAD_BEEF_0000_0001, 0x1234_5678_9ABC_DEF0];
    assert_eq!(entry_at(&entries, 0), 0xDEAD_BEEF_0000_0001);
    assert_eq!(entry_at(&entries, 1), 0x1234_5678_9ABC_DEF0);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of bounds")]
fn entry_at_out_of_bounds_panics_in_debug() {
    let entries: Vec<u64> = vec![42];
    let _ = entry_at(&entries, 1);
}

#[test]
fn entry_set_in_bounds() {
    let mut entries: Vec<u64> = vec![0, 0];
    entry_set(&mut entries, 0, 0xCAFE);
    entry_set(&mut entries, 1, 0xBABE);
    assert_eq!(entries[0], 0xCAFE);
    assert_eq!(entries[1], 0xBABE);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of bounds")]
fn entry_set_out_of_bounds_panics_in_debug() {
    let mut entries: Vec<u64> = vec![0];
    entry_set(&mut entries, 1, 42);
}

// --- Tests for raw pointer helpers (#7989) ---

#[test]
fn prefetch_l1_null_is_safe() {
    prefetch_read_l1(core::ptr::null::<u8>());
}

#[test]
fn prefetch_l1_valid_address() {
    let data = [1u64; 16];
    prefetch_read_l1(data.as_ptr());
}

#[test]
fn watch_iter_raw_pointers() {
    let mut entries: Vec<u64> = vec![10, 20, 30];
    let (begin, end) = watch_iter_raw(&mut entries);
    assert!(!begin.is_null());
    // end - begin should equal entries.len()
    let count = unsafe { end.offset_from(begin as *const u64) } as usize;
    assert_eq!(count, 3);
}

#[test]
fn watch_iter_raw_empty() {
    let mut entries: Vec<u64> = vec![];
    let (begin, end) = watch_iter_raw(&mut entries);
    assert_eq!(begin as *const u64, end);
}

#[test]
fn arena_literal_raw_reads_correct() {
    // Simulate arena: 5 header words + 3 literal words
    let words: Vec<u32> = vec![3, 0, 2, 0, 0, 100, 200, 300];
    let ptr = words.as_ptr();
    unsafe {
        assert_eq!(arena_literal_raw(ptr, 0, 5, 0), 100);
        assert_eq!(arena_literal_raw(ptr, 0, 5, 1), 200);
        assert_eq!(arena_literal_raw(ptr, 0, 5, 2), 300);
    }
}

#[test]
fn arena_header_word_raw_reads_correct() {
    let words: Vec<u32> = vec![3, 42, 0x0002_0000, 0, 0, 100, 200, 300];
    let ptr = words.as_ptr();
    unsafe {
        assert_eq!(arena_header_word_raw(ptr, 0, 0), 3); // len
        assert_eq!(arena_header_word_raw(ptr, 0, 1), 42); // activity
        assert_eq!(arena_header_word_raw(ptr, 0, 2), 0x0002_0000); // saved_pos | flags
    }
}

#[test]
fn val_raw_reads_correct() {
    let vals: Vec<i8> = vec![0, 1, -1, 0, 1, -1];
    let ptr = vals_ptr(&vals);
    unsafe {
        assert_eq!(val_raw(ptr, 0), 0);
        assert_eq!(val_raw(ptr, 1), 1);
        assert_eq!(val_raw(ptr, 2), -1);
        assert_eq!(val_raw(ptr, 5), -1);
    }
}

#[test]
fn vec_set_len_truncates() {
    let mut v: Vec<u64> = vec![1, 2, 3, 4, 5];
    unsafe { vec_set_len(&mut v, 3) };
    assert_eq!(v.len(), 3);
    assert_eq!(v, vec![1, 2, 3]);
}

#[test]
fn vec_set_len_zero() {
    let mut v: Vec<u64> = vec![1, 2, 3];
    unsafe { vec_set_len(&mut v, 0) };
    assert_eq!(v.len(), 0);
    assert!(v.is_empty());
}
