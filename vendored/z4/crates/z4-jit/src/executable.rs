// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executable memory allocation for JIT-compiled code.
//!
//! Uses mmap to allocate memory with execute permission. On macOS aarch64
//! (Apple Silicon), handles W^X enforcement via MAP_JIT and
//! pthread_jit_write_protect_np.

use std::ffi::c_void;
use std::ptr;

use crate::JitError;

// Platform constants for mmap.
const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const PROT_EXEC: i32 = 4;
const MAP_PRIVATE: i32 = 0x0002;

#[cfg(target_os = "macos")]
const MAP_ANON: i32 = 0x1000;
#[cfg(target_os = "linux")]
const MAP_ANON: i32 = 0x0020;

#[cfg(target_os = "macos")]
const MAP_JIT: i32 = 0x0800;

extern "C" {
    fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: i32,
        flags: i32,
        fd: i32,
        offset: i64,
    ) -> *mut c_void;
    fn munmap(addr: *mut c_void, len: usize) -> i32;
    #[cfg(not(target_os = "macos"))]
    fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
extern "C" {
    fn pthread_jit_write_protect_np(enabled: i32);
    fn sys_icache_invalidate(start: *mut c_void, len: usize);
}

/// Executable memory region backed by mmap. Holds JIT-compiled function code.
/// Automatically unmapped on drop.
pub(crate) struct ExecutableMemory {
    ptr: *mut u8,
    len: usize,
}

// SAFETY: ExecutableMemory is immutable after construction — the code region is
// written once during `new()`, then mprotected to read+execute (Linux) or
// toggled via W^X (macOS). No method on ExecutableMemory modifies the code
// after construction. The mmap'd pointer is process-global (not thread-local),
// and function pointers derived from it can be called from any thread safely.
unsafe impl Send for ExecutableMemory {}
unsafe impl Sync for ExecutableMemory {}

impl ExecutableMemory {
    /// Allocate executable memory and copy `code` into it.
    pub(crate) fn new(code: &[u8]) -> Result<Self, JitError> {
        if code.is_empty() {
            return Ok(Self {
                ptr: ptr::null_mut(),
                len: 0,
            });
        }

        // Round up to page size (assume 16KB for Apple Silicon, 4KB for others).
        let page_size = 16384; // Conservative: works for both 4K and 16K pages
        let alloc_len = (code.len() + page_size - 1) & !(page_size - 1);

        #[cfg(target_os = "macos")]
        {
            Self::alloc_macos(code, alloc_len)
        }

        #[cfg(target_os = "linux")]
        {
            Self::alloc_linux(code, alloc_len)
        }

        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = (code, alloc_len);
            Err(JitError::NoNativeIsa)
        }
    }

    #[cfg(target_os = "macos")]
    fn alloc_macos(code: &[u8], alloc_len: usize) -> Result<Self, JitError> {
        // macOS: use MAP_JIT for W^X support on Apple Silicon.
        // SAFETY: mmap is called with valid arguments: null addr (kernel chooses),
        // page-aligned alloc_len, RWX permissions (required for MAP_JIT on macOS),
        // MAP_PRIVATE|MAP_ANON (no file backing, process-private), fd=-1, offset=0.
        // The returned pointer is checked for MAP_FAILED before use.
        let ptr = unsafe {
            mmap(
                ptr::null_mut(),
                alloc_len,
                PROT_READ | PROT_WRITE | PROT_EXEC,
                MAP_PRIVATE | MAP_ANON | MAP_JIT,
                -1,
                0,
            )
        };

        if ptr == usize::MAX as *mut c_void {
            return Err(JitError::MmapFailed);
        }

        let ptr = ptr as *mut u8;

        // On Apple Silicon, toggle W^X protection to write.
        #[cfg(target_arch = "aarch64")]
        // SAFETY: pthread_jit_write_protect_np(0) disables execute protection
        // on the current thread's MAP_JIT pages, allowing writes. This is the
        // standard W^X toggle sequence on Apple Silicon. Must be re-enabled (1)
        // before any function call into the JIT code.
        unsafe {
            pthread_jit_write_protect_np(0); // Allow writes
        }

        // SAFETY: ptr is a valid, writable mmap'd region of alloc_len bytes.
        // code.len() <= alloc_len (alloc_len is code.len() rounded up to page
        // size). code.as_ptr() is valid for code.len() bytes. The regions do
        // not overlap (mmap returns fresh memory, code is on the heap/stack).
        unsafe {
            ptr::copy_nonoverlapping(code.as_ptr(), ptr, code.len());
        }

        // Switch back to execute mode and flush I-cache.
        #[cfg(target_arch = "aarch64")]
        // SAFETY: pthread_jit_write_protect_np(1) re-enables execute protection,
        // making the MAP_JIT pages executable and non-writable on this thread.
        // sys_icache_invalidate flushes the instruction cache for the written
        // region so the CPU fetches the newly-written code, not stale I-cache.
        // Both calls require the ptr to be within a valid MAP_JIT mapping, which
        // it is (mmap succeeded above and ptr has not been munmap'd).
        unsafe {
            pthread_jit_write_protect_np(1); // Read+execute only
            sys_icache_invalidate(ptr as *mut c_void, code.len());
        }

        Ok(Self {
            ptr,
            len: alloc_len,
        })
    }

    #[cfg(target_os = "linux")]
    fn alloc_linux(code: &[u8], alloc_len: usize) -> Result<Self, JitError> {
        // SAFETY: mmap called with valid arguments: null addr, page-aligned
        // alloc_len, RW permissions (no exec yet — added via mprotect after
        // code is written), MAP_PRIVATE|MAP_ANON, fd=-1, offset=0. Result
        // checked for MAP_FAILED before use.
        let ptr = unsafe {
            mmap(
                ptr::null_mut(),
                alloc_len,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };

        if ptr == usize::MAX as *mut c_void {
            return Err(JitError::MmapFailed);
        }

        let ptr = ptr as *mut u8;

        // SAFETY: ptr is a valid, writable mmap'd region of alloc_len bytes.
        // code.len() <= alloc_len. Regions do not overlap (mmap returns fresh
        // memory). See macOS path for the same invariant.
        unsafe {
            ptr::copy_nonoverlapping(code.as_ptr(), ptr, code.len());
        }

        // Switch from W to X: remove write, add execute.
        // SAFETY: ptr is page-aligned (from mmap), alloc_len is page-aligned.
        // The mmap'd region is still valid (not yet munmap'd). On success, the
        // region becomes read+execute, enforcing W^X. On failure, we clean up
        // with munmap.
        let rc = unsafe { mprotect(ptr as *mut c_void, alloc_len, PROT_READ | PROT_EXEC) };
        if rc != 0 {
            // SAFETY: ptr is a valid mmap'd region of alloc_len bytes. munmap
            // releases it back to the OS. This is the error cleanup path —
            // mprotect failed, so we must release the allocation.
            unsafe {
                munmap(ptr as *mut c_void, alloc_len);
            }
            return Err(JitError::MmapFailed);
        }

        Ok(Self {
            ptr,
            len: alloc_len,
        })
    }

    /// Base pointer to the executable code region.
    pub(crate) fn as_ptr(&self) -> *const u8 {
        self.ptr
    }
}

impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        if !self.ptr.is_null() && self.len > 0 {
            // SAFETY: self.ptr was returned by mmap with self.len bytes. It
            // has not been munmap'd before (Drop runs at most once, and no
            // other code path calls munmap on a successfully constructed
            // ExecutableMemory). The null/len checks above guard the empty case.
            unsafe {
                munmap(self.ptr as *mut c_void, self.len);
            }
        }
    }
}
