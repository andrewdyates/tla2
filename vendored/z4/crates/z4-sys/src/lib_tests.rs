// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_current_rss_nonzero() {
    let rss = current_rss_bytes();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(rss > 1024 * 1024, "RSS should be at least 1MB, got {rss}");
}

#[test]
fn test_physical_memory_nonzero() {
    let phys = physical_memory_bytes();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(
        phys > 1024 * 1024 * 1024,
        "Physical memory should be at least 1GB, got {phys}"
    );
}

#[test]
fn test_default_memory_limit_reasonable() {
    let limit = default_memory_limit();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        assert!(limit >= 2 * 1024 * 1024 * 1024, "Limit should be >= 2GB");
        assert!(limit <= 64 * 1024 * 1024 * 1024, "Limit should be <= 64GB");
    }
}

#[test]
fn test_process_memory_limit_default_disabled() {
    // Default limit is 0 (disabled)
    assert!(!process_memory_exceeded());
}

#[test]
fn test_process_memory_limit_tiny() {
    // Save and restore
    let old = get_process_memory_limit();
    set_process_memory_limit(1024); // 1 KB - any running process exceeds this
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(process_memory_exceeded());
    set_process_memory_limit(old);
}

#[test]
fn test_process_memory_limit_huge() {
    let old = get_process_memory_limit();
    set_process_memory_limit(1024 * 1024 * 1024 * 1024); // 1 TB
    assert!(!process_memory_exceeded());
    set_process_memory_limit(old);
}
