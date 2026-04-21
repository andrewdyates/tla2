// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Low-level system interfaces for Z4.
//!
//! This crate provides safe wrappers around OS-specific system calls for memory
//! measurement. It is the only crate in the z4 workspace that permits `unsafe`
//! code, keeping FFI boundaries minimal and auditable.
//!
//! ## Why this crate exists
//!
//! All other z4 crates use `#![forbid(unsafe_code)]`. Memory measurement
//! requires FFI calls (`getrusage`, `sysctlbyname`, `sysconf`), so the unsafe
//! code is isolated here behind safe public APIs.

use std::sync::atomic::{AtomicUsize, Ordering};

/// Process-wide memory limit in bytes. 0 = no limit.
static PROCESS_MEMORY_LIMIT: AtomicUsize = AtomicUsize::new(0);

/// Set the process-wide memory limit in bytes.
///
/// All subsequent calls to [`process_memory_exceeded`] will check against this
/// limit. Set to 0 to disable the limit.
///
/// Intended to be called once from `main()`.
pub fn set_process_memory_limit(bytes: usize) {
    PROCESS_MEMORY_LIMIT.store(bytes, Ordering::SeqCst);
}

/// Get the current process-wide memory limit in bytes. 0 = no limit.
pub fn get_process_memory_limit() -> usize {
    PROCESS_MEMORY_LIMIT.load(Ordering::Relaxed)
}

/// Check if the process has exceeded its memory limit.
///
/// Returns `false` if no limit is set (limit == 0) or if measurement fails.
/// This is cheap to call (single syscall, no subprocess).
pub fn process_memory_exceeded() -> bool {
    let limit = PROCESS_MEMORY_LIMIT.load(Ordering::Relaxed);
    if limit == 0 {
        return false;
    }
    let current = current_rss_bytes();
    current > 0 && current > limit
}

/// Returns the peak resident set size (RSS) of this process in bytes.
///
/// Uses `getrusage(RUSAGE_SELF)` — a single syscall with no subprocess
/// overhead. Returns peak RSS, which closely tracks current RSS for a
/// continuously-growing process (Rust's allocator does not aggressively
/// return memory to the OS).
///
/// Returns 0 if measurement fails or on unsupported platforms.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub fn current_rss_bytes() -> usize {
    // SAFETY: `libc::rusage` is a plain old data struct and zero-init is valid
    // before passing it to `getrusage`, which fills all output fields.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    // SAFETY: `usage` points to valid writable memory for the duration of the call.
    let ret = unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut usage) };
    if ret != 0 {
        return 0;
    }
    // macOS: ru_maxrss is in bytes.
    // Linux: ru_maxrss is in kilobytes.
    #[cfg(target_os = "macos")]
    {
        usage.ru_maxrss as usize
    }
    #[cfg(target_os = "linux")]
    {
        (usage.ru_maxrss as usize) * 1024
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn current_rss_bytes() -> usize {
    0
}

/// Returns the total physical memory of the system in bytes.
///
/// Returns 0 if detection fails or on unsupported platforms.
#[cfg(target_os = "macos")]
pub fn physical_memory_bytes() -> usize {
    let mut size: u64 = 0;
    let mut len = size_of::<u64>();
    let name = c"hw.memsize";
    let ret = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            std::ptr::addr_of_mut!(size).cast::<libc::c_void>(),
            &raw mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if ret == 0 {
        size as usize
    } else {
        0
    }
}

#[cfg(target_os = "linux")]
pub fn physical_memory_bytes() -> usize {
    let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGE_SIZE) };
    if pages > 0 && page_size > 0 {
        (pages as usize) * (page_size as usize)
    } else {
        0
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn physical_memory_bytes() -> usize {
    0
}

/// Compute a default memory limit based on physical RAM.
///
/// Returns half of physical memory, clamped to \[2 GB, 64 GB\].
/// This leaves room for the OS, other processes, and concurrent z4 instances.
///
/// Returns 0 if physical memory cannot be detected (limit will be disabled).
pub fn default_memory_limit() -> usize {
    let phys = physical_memory_bytes();
    if phys == 0 {
        return 0;
    }
    let half = phys / 2;
    const MIN_LIMIT: usize = 2 * 1024 * 1024 * 1024; // 2 GB
    const MAX_LIMIT: usize = 64 * 1024 * 1024 * 1024; // 64 GB
    half.clamp(MIN_LIMIT, MAX_LIMIT)
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
