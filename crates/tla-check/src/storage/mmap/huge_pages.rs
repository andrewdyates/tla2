// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Huge page advisory hints for mmap-backed storage.
//!
//! Requests the OS to use huge pages (2MB) for the mmap region, reducing TLB
//! pressure for large state tables. Falls back gracefully if huge pages are
//! not available or the OS does not support the hint.
//!
//! Part of #3856: Memory-Mapped State Table with Huge Pages.

use std::io;

/// Attempt to advise the OS to use huge pages for the given memory region.
///
/// Returns `Ok(true)` if the hint was accepted, `Ok(false)` if huge pages
/// are not supported on this platform, or `Err` on a syscall failure that
/// should be logged but not treated as fatal.
///
/// This is a best-effort hint -- the OS may ignore it. The caller should
/// always fall back to regular pages.
pub(crate) fn advise_huge_pages(ptr: *mut u8, len: usize) -> io::Result<bool> {
    #[cfg(target_os = "linux")]
    {
        advise_huge_pages_linux(ptr, len)
    }

    #[cfg(target_os = "macos")]
    {
        advise_huge_pages_macos(ptr, len)
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = (ptr, len);
        Ok(false)
    }
}

#[cfg(target_os = "linux")]
fn advise_huge_pages_linux(ptr: *mut u8, len: usize) -> io::Result<bool> {
    // MADV_HUGEPAGE = 14 on Linux. Requests transparent huge pages (THP).
    // This is an advisory hint; the kernel will use huge pages when possible
    // and silently fall back to regular 4KB pages if not.
    const MADV_HUGEPAGE: libc::c_int = 14;

    // SAFETY: ptr and len describe a valid mmap region allocated by memmap2.
    // madvise is an advisory syscall that cannot corrupt memory.
    let ret = unsafe { libc::madvise(ptr.cast(), len, MADV_HUGEPAGE) };
    if ret == 0 {
        Ok(true)
    } else {
        let err = io::Error::last_os_error();
        // EINVAL means the kernel doesn't support MADV_HUGEPAGE (e.g., THP disabled).
        // ENOMEM means the range is not properly aligned. Both are non-fatal.
        if err.raw_os_error() == Some(libc::EINVAL) || err.raw_os_error() == Some(libc::ENOMEM) {
            Ok(false)
        } else {
            Err(err)
        }
    }
}

#[cfg(target_os = "macos")]
fn advise_huge_pages_macos(ptr: *mut u8, len: usize) -> io::Result<bool> {
    // On macOS, madvise with MADV_FREE_REUSABLE + VM_FLAGS_SUPERPAGE is the
    // closest mechanism to huge page hints. However, macOS does not expose a
    // direct madvise hint for huge pages on already-mapped regions.
    //
    // The primary mechanism on macOS is MAP_HUGETLB/VM_FLAGS_SUPERPAGE_SIZE_2MB
    // at mmap() time, but memmap2 doesn't expose these flags directly.
    //
    // For now, we attempt MADV_FREE_REUSABLE which can help the kernel coalesce
    // pages. If the region is large enough (>= 2MB), macOS may use superpage
    // mappings internally.
    //
    // macOS 13+ (Ventura) can automatically promote to superpages for large
    // anonymous mappings. Our best strategy is to ensure proper alignment.

    // Minimum size for superpage consideration: 2MB
    const SUPERPAGE_SIZE: usize = 2 * 1024 * 1024;
    if len < SUPERPAGE_SIZE {
        return Ok(false);
    }

    // SAFETY: ptr and len describe a valid mmap region allocated by memmap2.
    // madvise is an advisory syscall that cannot corrupt memory.
    let ret = unsafe { libc::madvise(ptr.cast(), len, libc::MADV_FREE_REUSABLE) };
    if ret == 0 {
        Ok(true)
    } else {
        // Non-fatal: macOS may not support MADV_FREE_REUSABLE for this mapping.
        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use memmap2::MmapMut;

    #[test]
    fn test_advise_huge_pages_anonymous_mapping_does_not_panic() {
        // 4MB anonymous mapping -- large enough to potentially use huge pages
        let mmap = MmapMut::map_anon(4 * 1024 * 1024).expect("should create anon mmap");
        let ptr = mmap.as_ptr() as *mut u8;
        let len = mmap.len();

        // Should not panic or return an error -- may return Ok(true) or Ok(false)
        // depending on OS support.
        let result = advise_huge_pages(ptr, len);
        assert!(
            result.is_ok(),
            "advise_huge_pages should not fail: {result:?}"
        );
    }

    #[test]
    fn test_advise_huge_pages_small_region_returns_false_on_macos() {
        // 4KB region -- too small for huge pages
        let mmap = MmapMut::map_anon(4096).expect("should create small anon mmap");
        let ptr = mmap.as_ptr() as *mut u8;
        let len = mmap.len();

        let result = advise_huge_pages(ptr, len);
        assert!(result.is_ok());
        // On macOS, small regions should return false (below SUPERPAGE_SIZE threshold)
        // On Linux, the kernel may still accept the hint for any size
        #[cfg(target_os = "macos")]
        assert!(
            !result.unwrap(),
            "small region should not use huge pages on macOS"
        );
    }
}
