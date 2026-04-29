// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// Forked verbatim from xxhash-rust 0.8.15 (https://github.com/DoumanAsh/xxhash-rust)
// Upstream author: Douman <douman@gmx.se>
// Upstream license: BSL-1.0 (see LICENSE-BSL)
// Fork maintainer: Andrew Yates <ayates@dropbox.com>

//! Utilities of the crate
use core::{mem, ptr};

#[inline(always)]
pub const fn get_aligned_chunk_ref<T: Copy>(input: &[u8], offset: usize) -> &T {
    debug_assert!(mem::size_of::<T>() > 0); //Size MUST be positive
    debug_assert!(mem::size_of::<T>() <= input.len().saturating_sub(offset)); //Must fit

    unsafe { &*(input.as_ptr().add(offset) as *const T) }
}

#[allow(unused)]
#[inline(always)]
pub const fn get_aligned_chunk<T: Copy>(input: &[u8], offset: usize) -> T {
    *get_aligned_chunk_ref(input, offset)
}

#[inline(always)]
pub fn get_unaligned_chunk<T: Copy>(input: &[u8], offset: usize) -> T {
    debug_assert!(mem::size_of::<T>() > 0); //Size MUST be positive
    debug_assert!(mem::size_of::<T>() <= input.len().saturating_sub(offset)); //Must fit

    unsafe { ptr::read_unaligned(input.as_ptr().add(offset) as *const T) }
}

#[derive(Debug)]
pub struct Buffer<T> {
    pub ptr: T,
    pub len: usize,
    pub offset: usize,
}

impl Buffer<*mut u8> {
    #[inline(always)]
    pub fn copy_from_slice(&self, src: &[u8]) {
        self.copy_from_slice_by_size(src, src.len())
    }

    #[inline(always)]
    pub fn copy_from_slice_by_size(&self, src: &[u8], len: usize) {
        debug_assert!(self.len.saturating_sub(self.offset) >= len);

        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), self.ptr.add(self.offset), len);
        }
    }
}
