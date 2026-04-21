// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates. Apache-2.0
// Author: Andrew Yates
//
// Process memory monitoring utilities (Part of #2751).
// Provides platform-specific RSS (resident set size) queries.

/// Query the current process resident set size (RSS) in bytes.
///
/// Returns `None` if the platform is unsupported or the query fails.
#[cfg(target_os = "macos")]
pub(crate) fn current_rss_bytes() -> Option<usize> {
    use std::mem;

    // MACH_TASK_BASIC_INFO = 20
    const MACH_TASK_BASIC_INFO: u32 = 20;

    #[repr(C)]
    struct MachTaskBasicInfo {
        virtual_size: u64,
        resident_size: u64,
        resident_size_max: u64,
        user_time: libc::time_value_t,
        system_time: libc::time_value_t,
        policy: i32,
        suspend_count: i32,
    }

    let mut info: MachTaskBasicInfo = unsafe { mem::zeroed() };
    let mut count = (mem::size_of::<MachTaskBasicInfo>() / mem::size_of::<libc::natural_t>())
        as libc::mach_msg_type_number_t;

    // libc deprecated mach_task_self() in favor of the mach2 crate, but the
    // underlying API is stable. Suppress to avoid pulling in mach2 for one call.
    #[allow(deprecated)]
    let port = unsafe { libc::mach_task_self() };

    let kr = unsafe {
        libc::task_info(
            port,
            MACH_TASK_BASIC_INFO,
            &mut info as *mut MachTaskBasicInfo as libc::task_info_t,
            &mut count,
        )
    };

    if kr == libc::KERN_SUCCESS {
        Some(info.resident_size as usize)
    } else {
        None
    }
}

/// Query the current process resident set size (RSS) in bytes.
///
/// Returns `None` if `/proc/self/statm` is unreadable or unparseable.
#[cfg(target_os = "linux")]
pub(crate) fn current_rss_bytes() -> Option<usize> {
    let statm = std::fs::read_to_string("/proc/self/statm").ok()?;
    // Fields: size resident shared text lib data dt (all in pages)
    let rss_pages: usize = statm.split_whitespace().nth(1)?.parse().ok()?;
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if page_size > 0 {
        Some(rss_pages * page_size as usize)
    } else {
        None
    }
}

/// Unsupported platform fallback — always returns `None`.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn current_rss_bytes() -> Option<usize> {
    None
}

/// Query total physical memory in bytes.
///
/// Used by `MemoryPolicy::from_system_default()` to auto-detect a sensible
/// memory limit without requiring the user to pass `--memory-limit`.
#[cfg(target_os = "macos")]
pub(crate) fn total_physical_memory_bytes() -> Option<usize> {
    // sysctl hw.memsize returns total physical memory as a u64.
    let mut memsize: u64 = 0;
    let mut len = std::mem::size_of::<u64>();
    let name = c"hw.memsize";
    // SAFETY: sysctl with a known key and correctly sized output buffer.
    let ret = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            (&mut memsize as *mut u64).cast::<libc::c_void>(),
            &mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if ret == 0 && memsize > 0 {
        Some(memsize as usize)
    } else {
        None
    }
}

/// Query total physical memory in bytes.
#[cfg(target_os = "linux")]
pub(crate) fn total_physical_memory_bytes() -> Option<usize> {
    let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
    for line in meminfo.lines() {
        if let Some(rest) = line.strip_prefix("MemTotal:") {
            // Format: "MemTotal:       12345678 kB"
            let kb: usize = rest.trim().strip_suffix("kB")?.trim().parse().ok()?;
            return Some(kb * 1024);
        }
    }
    None
}

/// Unsupported platform fallback.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn total_physical_memory_bytes() -> Option<usize> {
    None
}

/// Estimate the heap memory usage of a `HashMap<K, V>` in bytes.
///
/// Uses the hashbrown layout: each bucket occupies `size_of::<(K, V)>() + 1`
/// byte (control byte). The HashMap struct itself is ~56 bytes.
///
/// Applies a 15% fragmentation factor to account for allocator alignment
/// padding and hashbrown's group metadata. Empirical measurements show
/// hashbrown allocations are typically 10-20% larger than the naive
/// `buckets * entry_size` calculation due to SIMD-aligned control byte
/// groups and allocator overhead.
///
/// Part of #4080: OOM safety — internal memory accounting.
pub(crate) fn estimate_hashmap_bytes<K, V>(capacity: usize) -> usize {
    let entry_size = std::mem::size_of::<K>()
        .saturating_add(std::mem::size_of::<V>())
        .saturating_add(1); // control byte per bucket
    // hashbrown rounds capacity to next power of 2 and uses ~87.5% load factor,
    // so allocated buckets ≈ capacity.next_power_of_two(). For estimation
    // purposes, just use 2 * capacity as a conservative upper bound.
    let allocated_buckets = capacity.checked_next_power_of_two().unwrap_or(capacity);
    let raw = allocated_buckets
        .saturating_mul(entry_size)
        .saturating_add(56); // HashMap struct overhead
    // Apply 15% fragmentation factor for allocator alignment and group metadata.
    apply_fragmentation_overhead(raw)
}

/// Estimate heap memory of a `DashMap<K, V>` in bytes.
///
/// DashMap uses N shards (default: `cpus * 4`, minimum 1), each an
/// independent hashbrown table protected by an RwLock. We estimate each
/// shard's table at `capacity / shards` entries, plus per-shard overhead
/// for the RwLock (~72 bytes) and the outer DashMap bookkeeping.
///
/// Part of #4080: OOM safety — parallel checker internal memory accounting.
pub(crate) fn estimate_dashmap_bytes<K, V>(capacity: usize) -> usize {
    // DashMap default shard count: num_cpus * 4, clamped to [1, 256].
    let num_shards = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1).saturating_mul(4).clamp(1, 256);
    let per_shard_capacity = capacity / num_shards.max(1);
    let per_shard_table = estimate_hashmap_bytes::<K, V>(per_shard_capacity);
    let rwlock_overhead = 72; // parking_lot RwLock per shard
    let shard_total = per_shard_table.saturating_add(rwlock_overhead);
    let total = num_shards
        .saturating_mul(shard_total)
        .saturating_add(128); // DashMap struct + shard array overhead
    total
}

/// Estimate heap memory of a `DashMap` given entry count and raw entry size.
///
/// This variant avoids type parameters when the key/value types are not
/// directly available (e.g., `DashMap<K, ArrayState>` where ArrayState
/// is a variable-size type). The caller provides `entry_size` as
/// `size_of::<K>() + estimated_value_size`.
///
/// Part of #4080: OOM safety — parallel checker internal memory accounting.
pub(crate) fn estimate_dashmap_bytes_raw(capacity: usize, entry_size: usize) -> usize {
    let num_shards = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1).saturating_mul(4).clamp(1, 256);
    let per_shard_capacity = capacity / num_shards.max(1);
    let per_shard_entry_size = entry_size.saturating_add(1); // +1 control byte
    let allocated = per_shard_capacity
        .checked_next_power_of_two()
        .unwrap_or(per_shard_capacity);
    let per_shard_table = apply_fragmentation_overhead(
        allocated
            .saturating_mul(per_shard_entry_size)
            .saturating_add(56),
    );
    let rwlock_overhead = 72;
    let shard_total = per_shard_table.saturating_add(rwlock_overhead);
    num_shards
        .saturating_mul(shard_total)
        .saturating_add(128)
}

/// Estimate heap memory of a `VecDeque<T>` in bytes.
///
/// VecDeque allocates a power-of-2 ring buffer. The struct itself is ~24 bytes
/// (pointer + head index + len).
///
/// Part of #4080: OOM safety — BFS queue memory accounting.
pub(crate) fn estimate_vecdeque_bytes<T>(len: usize) -> usize {
    if len == 0 {
        return 24;
    }
    let capacity = len.checked_next_power_of_two().unwrap_or(len);
    let raw = capacity
        .saturating_mul(std::mem::size_of::<T>())
        .saturating_add(24); // VecDeque struct overhead
    apply_fragmentation_overhead(raw)
}

/// Apply a 15% fragmentation overhead to a raw byte estimate.
///
/// Accounts for allocator alignment padding, SIMD-aligned control byte
/// groups in hashbrown, and general allocator overhead (free-list metadata,
/// size classes, etc.). This makes estimates conservative rather than
/// optimistic, which is the right direction for OOM prevention.
///
/// Part of #4080.
pub(crate) fn apply_fragmentation_overhead(bytes: usize) -> usize {
    // 1.15x = multiply by 115 and divide by 100.
    // Using integer arithmetic to avoid floating-point in hot paths.
    bytes.saturating_mul(115) / 100
}

/// Memory pressure level returned by [`MemoryPolicy::check`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MemoryPressure {
    /// RSS below the warning threshold — no action needed.
    Normal,
    /// RSS at or above the warning threshold but below critical.
    /// Caller should trigger a checkpoint if configured.
    Warning,
    /// RSS at or above the critical threshold.
    /// Caller should stop exploration with a checkpoint and error message.
    Critical,
}

/// Configurable memory limit with two thresholds.
///
/// Part of #2751 Phase 2+3: memory-triggered checkpoint and graceful stop.
///
/// - `warning_fraction` (default 0.70): when RSS exceeds `limit * warning_fraction`,
///   trigger a checkpoint save if checkpointing is configured.
/// - `critical_fraction` (default 0.85): when RSS exceeds `limit * critical_fraction`,
///   stop exploration gracefully with a checkpoint and error message.
#[derive(Debug, Clone)]
pub(crate) struct MemoryPolicy {
    limit_bytes: usize,
    warning_fraction: f64,
    critical_fraction: f64,
}

impl MemoryPolicy {
    /// Create a new memory policy with the given limit in bytes.
    ///
    /// Uses default thresholds: warning at 70%, critical at 85%.
    ///
    /// Part of #4080: lowered from 80%/95% to trigger earlier. The previous
    /// thresholds left too little headroom — by the time RSS crossed 80%,
    /// in-memory stores had already grown past the point of graceful recovery.
    /// The lower thresholds give the BFS loop time to checkpoint and stop
    /// before the OS OOM killer intervenes.
    pub(crate) fn new(limit_bytes: usize) -> Self {
        Self {
            limit_bytes,
            warning_fraction: 0.70,
            critical_fraction: 0.85,
        }
    }

    /// Auto-detect total physical RAM and create a policy using 90% of it,
    /// divided by the number of concurrent heavy processes.
    ///
    /// Returns `None` on unsupported platforms or if detection fails.
    /// This ensures memory monitoring is active by default — users get a
    /// warning at 63% of RAM (70% of 90%) and graceful stop at 76.5% of RAM
    /// (85% of 90%) instead of an OOM kill with no warning.
    ///
    /// Heavy processes include `tla2`, `cargo`, `rustc`, and `cc` — any of
    /// these compete for memory when agents run alongside compilations.
    /// Each instance gets `(total * 0.90) / N` so they collectively fit in RAM.
    pub(crate) fn from_system_default() -> Option<Self> {
        let total = total_physical_memory_bytes()?;
        let instances = count_tla2_instances().max(1);
        // Use 90% of physical RAM divided by instance count. This leaves
        // headroom for the OS and prevents N concurrent instances from each
        // claiming 90% and triggering OOM.
        let limit = ((total as f64 * 0.90) / instances as f64) as usize;
        Some(Self::new(limit))
    }

    /// Return the number of detected instances and total physical RAM,
    /// for diagnostic logging when the limit is auto-detected.
    pub(crate) fn system_default_info() -> Option<(usize, usize, usize)> {
        let total = total_physical_memory_bytes()?;
        let instances = count_tla2_instances().max(1);
        let limit = ((total as f64 * 0.90) / instances as f64) as usize;
        Some((limit, total, instances))
    }

    /// Check current RSS against the configured thresholds.
    ///
    /// Returns `Normal` if RSS is unavailable on this platform.
    pub(crate) fn check(&self) -> MemoryPressure {
        let rss = match current_rss_bytes() {
            Some(rss) => rss,
            None => return MemoryPressure::Normal,
        };
        let critical_threshold = (self.limit_bytes as f64 * self.critical_fraction) as usize;
        let warning_threshold = (self.limit_bytes as f64 * self.warning_fraction) as usize;
        if rss >= critical_threshold {
            MemoryPressure::Critical
        } else if rss >= warning_threshold {
            MemoryPressure::Warning
        } else {
            MemoryPressure::Normal
        }
    }

    pub(crate) fn limit_bytes(&self) -> usize {
        self.limit_bytes
    }
}

/// Names of executables that consume significant memory alongside `tla2`.
///
/// When multiple `tla2` instances run in parallel on the same host, the
/// memory budget is divided by instance count. But `cargo`, `rustc`, and `cc`
/// processes from concurrent compilations also consume significant RSS and
/// should be counted to avoid overestimating the per-instance budget.
const HEAVY_PROCESS_NAMES: &[&[u8]] = &[b"tla2", b"cargo", b"rustc", b"cc"];

/// Count the number of running memory-heavy processes (tla2, cargo, rustc, cc).
///
/// Uses platform-specific process enumeration to detect sibling instances.
/// Returns 1 if enumeration fails or platform is unsupported.
///
/// Part of #4080: expanded beyond just `tla2` to also count compilation
/// processes that compete for memory when agents run alongside builds.
#[cfg(target_os = "macos")]
fn count_tla2_instances() -> usize {
    use std::ffi::c_int;

    extern "C" {
        fn proc_listpids(r#type: u32, typeinfo: u32, buffer: *mut c_int, bufsize: c_int) -> c_int;
        fn proc_pidpath(pid: c_int, buffer: *mut u8, bufsize: u32) -> c_int;
    }

    const PROC_ALL_PIDS: u32 = 1;
    const MAXPATHLEN: u32 = 1024;

    // First call: get buffer size needed.
    // SAFETY: proc_listpids with null buffer returns required size in bytes.
    let buf_size = unsafe { proc_listpids(PROC_ALL_PIDS, 0, std::ptr::null_mut(), 0) };
    if buf_size <= 0 {
        return 1;
    }

    let num_pids = buf_size as usize / std::mem::size_of::<c_int>();
    let mut pids = vec![0i32; num_pids];
    // SAFETY: buffer is correctly sized for `num_pids` entries.
    let actual_size = unsafe { proc_listpids(PROC_ALL_PIDS, 0, pids.as_mut_ptr(), buf_size) };
    if actual_size <= 0 {
        return 1;
    }

    let actual_count = actual_size as usize / std::mem::size_of::<c_int>();
    let mut heavy_count: usize = 0;
    let mut path_buf = vec![0u8; MAXPATHLEN as usize];

    for &pid in &pids[..actual_count] {
        if pid <= 0 {
            continue;
        }
        // SAFETY: path_buf is MAXPATHLEN bytes, pid is a valid process id.
        let len = unsafe { proc_pidpath(pid, path_buf.as_mut_ptr(), MAXPATHLEN) };
        if len <= 0 {
            continue;
        }
        let path = &path_buf[..len as usize];
        // Extract the executable name (last path component).
        let exe_name = if let Some(pos) = path.iter().rposition(|&b| b == b'/') {
            &path[pos + 1..]
        } else {
            path
        };
        if HEAVY_PROCESS_NAMES.iter().any(|&name| exe_name == name) {
            heavy_count += 1;
        }
    }

    heavy_count.max(1)
}

/// Count the number of running memory-heavy processes (tla2, cargo, rustc, cc).
#[cfg(target_os = "linux")]
fn count_tla2_instances() -> usize {
    let Ok(entries) = std::fs::read_dir("/proc") else {
        return 1;
    };

    let heavy_names: &[&str] = &["tla2", "cargo", "rustc", "cc"];
    let mut count: usize = 0;
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        // Only numeric directory names are PIDs.
        if !name_str.chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        let exe_path = entry.path().join("exe");
        if let Ok(target) = std::fs::read_link(&exe_path) {
            if let Some(file_name) = target.file_name() {
                if heavy_names.iter().any(|&n| file_name == n) {
                    count += 1;
                }
            }
        }
    }

    count.max(1)
}

/// Unsupported platform fallback.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn count_tla2_instances() -> usize {
    1
}

/// Log the auto-detected memory budget to stderr.
///
/// Called from the CLI runner when no explicit `--memory-limit` was passed.
pub(crate) fn log_memory_budget(limit_bytes: usize, total_bytes: usize, instances: usize) {
    let limit_mb = limit_bytes / (1024 * 1024);
    let total_gb = total_bytes / (1024 * 1024 * 1024);
    if instances > 1 {
        eprintln!(
            "Note: memory limit auto-detected: {limit_mb} MB \
             ({total_gb} GB total / {instances} instances \u{00d7} 90%)"
        );
    } else {
        eprintln!(
            "Note: memory limit auto-detected: {limit_mb} MB \
             ({total_gb} GB total \u{00d7} 90%)"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_current_rss_returns_some_on_supported_platform() {
        let rss = current_rss_bytes();
        // On macOS and Linux this should succeed; on other platforms it returns None.
        if cfg!(any(target_os = "macos", target_os = "linux")) {
            let bytes = rss.expect("RSS query should succeed on this platform");
            // Sanity: any running process uses at least 1 MB of RSS
            assert!(
                bytes > 1_000_000,
                "RSS too small ({bytes} bytes) — likely a measurement error"
            );
        }
    }

    #[test]
    fn test_memory_policy_normal_when_under_threshold() {
        // Set a limit much higher than current RSS
        let policy = MemoryPolicy::new(usize::MAX);
        assert_eq!(policy.check(), MemoryPressure::Normal);
    }

    #[test]
    fn test_memory_policy_critical_when_limit_is_tiny() {
        // Set a limit of 1 byte — any running process exceeds this
        let policy = MemoryPolicy::new(1);
        if cfg!(any(target_os = "macos", target_os = "linux")) {
            assert_eq!(policy.check(), MemoryPressure::Critical);
        }
    }

    #[test]
    fn test_memory_policy_warning_when_rss_in_warning_band() {
        if !cfg!(any(target_os = "macos", target_os = "linux")) {
            return;
        }

        let rss = current_rss_bytes().expect("RSS query should succeed on this platform");
        // Choose a limit so 70% of the limit is below the current RSS but 85%
        // still stays above it, which places the process in the Warning band.
        // 0.77 is the midpoint of (0.70, 0.85).
        let limit = (rss as f64 / 0.77) as usize;
        let policy = MemoryPolicy::new(limit);
        let warning_threshold = (limit as f64 * 0.70) as usize;
        let critical_threshold = (limit as f64 * 0.85) as usize;

        assert!(
            warning_threshold <= rss && rss < critical_threshold,
            "constructed limit should place RSS in warning band: \
             warning_threshold={warning_threshold} rss={rss} critical_threshold={critical_threshold}"
        );
        assert_eq!(
            policy.check(),
            MemoryPressure::Warning,
            "RSS ({rss} bytes) with limit ({limit} bytes) should be in warning band \
             [{warning_threshold}..{critical_threshold})"
        );
    }

    #[test]
    fn test_memory_policy_thresholds() {
        let policy = MemoryPolicy::new(1000);
        // 70% of 1000 = 700, 85% of 1000 = 850
        assert!((policy.warning_fraction - 0.70).abs() < f64::EPSILON);
        assert!((policy.critical_fraction - 0.85).abs() < f64::EPSILON);
        assert_eq!(policy.limit_bytes(), 1000);
    }

    #[test]
    fn test_total_physical_memory_returns_some_on_supported_platform() {
        let total = total_physical_memory_bytes();
        if cfg!(any(target_os = "macos", target_os = "linux")) {
            let bytes = total.expect("total physical memory query should succeed");
            // Sanity: any modern machine has at least 1 GB of RAM
            assert!(
                bytes > 1_000_000_000,
                "total RAM too small ({bytes} bytes) — likely a measurement error"
            );
        }
    }

    #[test]
    fn test_from_system_default_returns_policy_on_supported_platform() {
        if cfg!(any(target_os = "macos", target_os = "linux")) {
            let policy = MemoryPolicy::from_system_default()
                .expect("from_system_default should succeed on this platform");
            let total = total_physical_memory_bytes().unwrap();
            let max_limit = (total as f64 * 0.90) as usize;
            assert!(
                (1..=max_limit).contains(&policy.limit_bytes()),
                "policy limit should be a positive per-instance share of 90% of RAM: \
                 limit={} max_limit={max_limit}",
                policy.limit_bytes()
            );
            // Verify it doesn't trigger on a fresh process (well under per-instance limit)
            assert_eq!(policy.check(), MemoryPressure::Normal);
        }
    }

    #[test]
    fn test_count_tla2_instances_returns_at_least_one() {
        // This test process may or may not be named "tla2", but the
        // function must always return >= 1.
        let count = count_tla2_instances();
        assert!(
            count >= 1,
            "count_tla2_instances must return >= 1, got {count}"
        );
    }

    #[test]
    fn test_system_default_info_matches_policy() {
        if cfg!(any(target_os = "macos", target_os = "linux")) {
            let (limit, total, instances) = MemoryPolicy::system_default_info()
                .expect("system_default_info should succeed on this platform");
            assert_eq!(limit, ((total as f64 * 0.90) / instances as f64) as usize);
            assert!(MemoryPolicy::from_system_default().is_some());
            assert!(total > 0);
            assert!(instances >= 1);
        }
    }

    #[test]
    fn test_estimate_hashmap_bytes_basic() {
        // HashMap<u64, u64> with capacity 1024:
        // next_power_of_two(1024) = 1024
        // entry_size = 8 + 8 + 1 = 17
        // raw = 1024 * 17 + 56 = 17464
        // with 15% fragmentation: 17464 * 115 / 100 = 20083
        let bytes = estimate_hashmap_bytes::<u64, u64>(1024);
        let raw = 1024 * 17 + 56;
        assert_eq!(bytes, apply_fragmentation_overhead(raw));
        // Verify it's strictly larger than raw (fragmentation adds overhead)
        assert!(bytes > raw, "fragmentation overhead should increase estimate");
    }

    #[test]
    fn test_estimate_hashmap_bytes_zero_capacity() {
        let bytes = estimate_hashmap_bytes::<u64, u64>(0);
        // next_power_of_two(0) is 1 for std, but checked_next_power_of_two(0)
        // returns Some(1) for 0. The important thing is it doesn't panic.
        assert!(bytes >= 56);
    }

    #[test]
    fn test_estimate_hashmap_bytes_non_power_of_two() {
        // capacity 1000 rounds up to 1024
        let bytes = estimate_hashmap_bytes::<u64, u64>(1000);
        let raw = 1024 * 17 + 56;
        assert_eq!(bytes, apply_fragmentation_overhead(raw));
    }

    #[test]
    fn test_estimate_dashmap_bytes_nonzero() {
        let bytes = estimate_dashmap_bytes::<u64, u64>(1000);
        // Must be larger than a single HashMap of the same capacity
        // because DashMap adds per-shard overhead.
        assert!(bytes > 0, "DashMap estimate should be positive");
        // DashMap with sharding should use more memory than a single HashMap
        // due to per-shard overhead and capacity rounding per shard.
        let single_map = estimate_hashmap_bytes::<u64, u64>(1000);
        assert!(
            bytes >= single_map,
            "DashMap ({bytes}) should use at least as much as HashMap ({single_map})"
        );
    }

    #[test]
    fn test_estimate_vecdeque_bytes() {
        let bytes = estimate_vecdeque_bytes::<u64>(1000);
        // 1000 rounds up to 1024, * 8 bytes + 24 overhead, + fragmentation
        let raw = 1024 * 8 + 24;
        assert_eq!(bytes, apply_fragmentation_overhead(raw));
    }

    #[test]
    fn test_estimate_vecdeque_bytes_zero() {
        let bytes = estimate_vecdeque_bytes::<u64>(0);
        assert_eq!(bytes, 24); // just the struct overhead, no fragmentation
    }

    #[test]
    fn test_apply_fragmentation_overhead() {
        assert_eq!(apply_fragmentation_overhead(100), 115);
        assert_eq!(apply_fragmentation_overhead(1000), 1150);
        assert_eq!(apply_fragmentation_overhead(0), 0);
    }

    #[test]
    fn test_estimate_dashmap_bytes_raw() {
        let bytes = estimate_dashmap_bytes_raw(1000, 16);
        assert!(bytes > 0);
        // Should be comparable to estimate_dashmap_bytes for same-size entries
        let typed = estimate_dashmap_bytes::<u64, u64>(1000);
        // Both should be in the same ballpark (entry_size = 16 for both)
        assert!(
            (bytes as f64 / typed as f64) > 0.5
                && (bytes as f64 / typed as f64) < 2.0,
            "raw ({bytes}) and typed ({typed}) should be comparable"
        );
    }
}
