// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for disk fingerprint storage: interpolation search and invariant checks.

mod interpolation_tests {
    use crate::storage::disk_search::{interpolate_mid, IntervalKind};

    // ---- Open interval (page-level search) ----

    #[test]
    fn test_open_uniform_distribution() {
        // Uniform: 10 pages, values 0..9000 in steps of 1000.
        // Target 4500 → expect mid near index 5.
        let mid = interpolate_mid(0, 9, 0, 9000, 4500, IntervalKind::Open);
        assert!(mid.is_some());
        let m = mid.unwrap();
        assert!(m > 0 && m < 9, "mid={m} should be in (0, 9)");
        // Interpolation for uniform data: 1 + (8 * 4500) / 9000 = 1 + 4 = 5
        assert_eq!(m, 5);
    }

    #[test]
    fn test_open_narrow_interval_returns_none() {
        // Adjacent indices: no room for interior midpoint.
        assert_eq!(
            interpolate_mid(5, 6, 100, 200, 150, IntervalKind::Open),
            None
        );
    }

    #[test]
    fn test_open_equal_values_returns_none() {
        // Equal boundary values: can't interpolate.
        assert_eq!(
            interpolate_mid(0, 10, 500, 500, 500, IntervalKind::Open),
            None
        );
    }

    #[test]
    fn test_open_target_at_lo_boundary_returns_none() {
        // Target == lo_val: out of strict interior.
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 100, IntervalKind::Open),
            None
        );
    }

    #[test]
    fn test_open_target_at_hi_boundary_returns_none() {
        // Target == hi_val: out of strict interior.
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 200, IntervalKind::Open),
            None
        );
    }

    #[test]
    fn test_open_target_below_lo_returns_none() {
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 50, IntervalKind::Open),
            None
        );
    }

    #[test]
    fn test_open_target_above_hi_returns_none() {
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 250, IntervalKind::Open),
            None
        );
    }

    #[test]
    fn test_open_skewed_low() {
        // Very skewed: target near lo_val → mid should be near lo_idx + 1.
        let mid = interpolate_mid(0, 100, 0, 1_000_000, 1, IntervalKind::Open).unwrap();
        assert!(mid > 0 && mid < 100);
        assert_eq!(mid, 1, "very low target should clamp near lo_idx + 1");
    }

    #[test]
    fn test_open_skewed_high() {
        // Very skewed: target near hi_val → mid should be near hi_idx - 1.
        let mid = interpolate_mid(0, 100, 0, 1_000_000, 999_999, IntervalKind::Open).unwrap();
        assert!(mid > 0 && mid < 100);
        assert_eq!(mid, 99, "very high target should clamp near hi_idx - 1");
    }

    #[test]
    fn test_open_u64_max_values() {
        // u64 extremes: tests that u128 arithmetic avoids overflow.
        let lo_val = 0u64;
        let hi_val = u64::MAX;
        let target = u64::MAX / 2;
        let mid = interpolate_mid(0, 1000, lo_val, hi_val, target, IntervalKind::Open);
        assert!(mid.is_some());
        let m = mid.unwrap();
        assert!(m > 0 && m < 1000);
        // Expect approximately 500 (midpoint of 1..999).
        assert!(
            (450..=550).contains(&m),
            "mid={m} should be near 500 for midpoint target"
        );
    }

    #[test]
    fn test_open_progress_guarantee() {
        // With only 3 positions (lo=0, hi=2), interpolation must return 1.
        let mid = interpolate_mid(0, 2, 0, 100, 50, IntervalKind::Open).unwrap();
        assert_eq!(mid, 1);
    }

    #[test]
    fn test_open_inverted_values_returns_none() {
        // hi_val < lo_val: should return None.
        assert_eq!(
            interpolate_mid(0, 10, 200, 100, 150, IntervalKind::Open),
            None
        );
    }

    // ---- HalfOpen interval (entry-level search) ----

    #[test]
    fn test_half_open_uniform_distribution() {
        // 10 entries [0..9), values 0..9000. Target 4500 → mid near 5.
        let mid = interpolate_mid(0, 10, 0, 9000, 4500, IntervalKind::HalfOpen);
        assert!(mid.is_some());
        let m = mid.unwrap();
        assert!(m < 10, "mid={m} should be in [0, 9]");
        // Interpolation: 0 + (9 * 4500) / 9000 = 4 (integer truncation)
        assert_eq!(m, 4);
    }

    #[test]
    fn test_half_open_narrow_interval_returns_none() {
        // hi - lo <= 2: too narrow for interpolation to improve over midpoint.
        assert_eq!(
            interpolate_mid(5, 7, 100, 200, 150, IntervalKind::HalfOpen),
            None
        );
        assert_eq!(
            interpolate_mid(5, 6, 100, 200, 150, IntervalKind::HalfOpen),
            None
        );
    }

    #[test]
    fn test_half_open_equal_values_returns_none() {
        assert_eq!(
            interpolate_mid(0, 10, 500, 500, 500, IntervalKind::HalfOpen),
            None
        );
    }

    #[test]
    fn test_half_open_target_at_boundaries_returns_none() {
        // Target at or beyond boundaries: can't interpolate.
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 100, IntervalKind::HalfOpen),
            None
        );
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 200, IntervalKind::HalfOpen),
            None
        );
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 50, IntervalKind::HalfOpen),
            None
        );
        assert_eq!(
            interpolate_mid(0, 10, 100, 200, 250, IntervalKind::HalfOpen),
            None
        );
    }

    #[test]
    fn test_half_open_skewed_low() {
        // Target near lo_val → mid clamped to lo.
        let mid = interpolate_mid(0, 100, 0, 1_000_000, 1, IntervalKind::HalfOpen).unwrap();
        assert!(mid < 100);
        assert_eq!(mid, 0, "very low target should clamp to lo");
    }

    #[test]
    fn test_half_open_skewed_high() {
        // Target near hi_val → mid near hi - 1.
        // HalfOpen: 0 + (99 * 999_999 / 1_000_000) = 98 (integer truncation).
        let mid = interpolate_mid(0, 100, 0, 1_000_000, 999_999, IntervalKind::HalfOpen).unwrap();
        assert!(mid < 100);
        assert_eq!(mid, 98, "very high target near hi - 1");
    }

    #[test]
    fn test_half_open_u64_max_values() {
        // u64 extremes with HalfOpen.
        let lo_val = 0u64;
        let hi_val = u64::MAX;
        let target = u64::MAX / 2;
        let mid = interpolate_mid(0, 1000, lo_val, hi_val, target, IntervalKind::HalfOpen);
        assert!(mid.is_some());
        let m = mid.unwrap();
        assert!(m < 1000);
        // Expect approximately 499 (0 + 999 * 0.5 = 499).
        assert!(
            (449..=549).contains(&m),
            "mid={m} should be near 499 for midpoint target"
        );
    }

    #[test]
    fn test_half_open_progress_guarantee() {
        // With hi - lo == 4, interpolation should return a valid position.
        let mid = interpolate_mid(0, 4, 0, 100, 50, IntervalKind::HalfOpen).unwrap();
        assert!(mid < 4, "mid={mid} should be in [0, 3]");
    }

    #[test]
    fn test_half_open_inverted_values_returns_none() {
        assert_eq!(
            interpolate_mid(0, 10, 200, 100, 150, IntervalKind::HalfOpen),
            None
        );
    }

    // ---- Cross-interval consistency ----

    #[test]
    fn test_open_vs_half_open_same_arithmetic() {
        // Both should use the same u128 arithmetic core. Verify they agree
        // on the proportional position for the same inputs (adjusted for interval offset).
        let open = interpolate_mid(0, 100, 0, 1000, 500, IntervalKind::Open).unwrap();
        let half = interpolate_mid(0, 100, 0, 1000, 500, IntervalKind::HalfOpen).unwrap();
        // Open: 1 + 98 * 500/1000 = 1 + 49 = 50
        assert_eq!(open, 50);
        // HalfOpen: 0 + 99 * 500/1000 = 0 + 49 = 49
        assert_eq!(half, 49);
        // The +1 offset in Open accounts for excluding the lower boundary.
    }
}

mod check_invariant_tests {
    use crate::state::Fingerprint;
    use crate::storage::disk::DiskFingerprintSet;

    fn make_disk_fpset(capacity: usize) -> (tempfile::TempDir, DiskFingerprintSet) {
        let dir = tempfile::tempdir().unwrap();
        let fpset = DiskFingerprintSet::new(capacity, dir.path()).unwrap();
        (dir, fpset)
    }

    #[test]
    fn test_check_invariant_empty_set() {
        let (_dir, fpset) = make_disk_fpset(1024);
        assert!(fpset.check_invariant_impl().unwrap());
    }

    #[test]
    fn test_check_invariant_after_eviction() {
        // Small primary (64 slots) so eviction triggers quickly.
        let (_dir, fpset) = make_disk_fpset(64);

        // Insert enough to trigger at least one eviction.
        for i in 1u64..=200 {
            fpset.insert_checked(Fingerprint(i));
        }

        assert!(
            fpset.eviction_count() > 0,
            "should have evicted at least once"
        );
        assert!(fpset.check_invariant_impl().unwrap());
    }

    #[test]
    fn test_check_invariant_detects_corrupt_sort_order() {
        let (_dir, fpset) = make_disk_fpset(64);

        // Insert enough to trigger eviction.
        for i in 1u64..=200 {
            fpset.insert_checked(Fingerprint(i));
        }
        assert!(fpset.eviction_count() > 0);

        // Corrupt the disk file: swap two adjacent FPs to break sort order.
        {
            let mut data = std::fs::read(&fpset.disk_path).unwrap();
            // Swap the first two 8-byte entries.
            if data.len() >= 16 {
                let (first, second) = data.split_at_mut(8);
                let mut tmp = [0u8; 8];
                tmp.copy_from_slice(&first[..8]);
                first[..8].copy_from_slice(&second[..8]);
                second[..8].copy_from_slice(&tmp);
                std::fs::write(&fpset.disk_path, data).unwrap();
            }
        }

        // Invariant check should detect the corruption.
        assert!(!fpset.check_invariant_impl().unwrap());
    }

    #[test]
    fn test_check_invariant_detects_count_mismatch() {
        let (_dir, fpset) = make_disk_fpset(64);

        for i in 1u64..=200 {
            fpset.insert_checked(Fingerprint(i));
        }
        assert!(fpset.eviction_count() > 0);

        // Corrupt disk_count to be wrong.
        let actual = fpset.disk_count.load(std::sync::atomic::Ordering::Relaxed);
        fpset
            .disk_count
            .store(actual + 100, std::sync::atomic::Ordering::Relaxed);

        assert!(!fpset.check_invariant_impl().unwrap());

        // Restore to avoid panic in drop.
        fpset
            .disk_count
            .store(actual, std::sync::atomic::Ordering::Relaxed);
    }
}
