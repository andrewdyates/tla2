// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprint-based state deduplication for BFS exploration.
//!
//! Stores a 128-bit hash of each packed marking instead of the full marking
//! bytes, reducing per-state memory from `packed_size + 48` bytes to ~32 bytes
//! regardless of net size. Collision probability is approximately N²/2^129,
//! which is <10^-20 for N < 10^9 states.
//!
//! Adapted from the tla2 `tla-check` fingerprint storage pattern using
//! double SipHash for 128-bit independence.

use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hasher};
use std::sync::OnceLock;

/// Two independent `RandomState` seeds, initialized once per process.
static SEEDS: OnceLock<(RandomState, RandomState)> = OnceLock::new();

fn seeds() -> &'static (RandomState, RandomState) {
    SEEDS.get_or_init(|| (RandomState::new(), RandomState::new()))
}

/// Compute a 128-bit fingerprint of a packed marking for deduplication.
///
/// Uses two independent SipHash instances (different random seeds) to produce
/// a 128-bit fingerprint. Collision probability for N states is approximately
/// N²/2^129, which is negligible for MCC-scale explorations (< 10^8 states).
pub(crate) fn fingerprint_marking(packed: &[u8]) -> u128 {
    let (s1, s2) = seeds();
    let h1 = {
        let mut h = s1.build_hasher();
        h.write(packed);
        h.finish()
    };
    let h2 = {
        let mut h = s2.build_hasher();
        h.write(packed);
        h.finish()
    };
    (h1 as u128) << 64 | (h2 as u128)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fingerprint_deterministic_within_process() {
        let packed = vec![1u8, 2, 3, 4, 5];
        let fp1 = fingerprint_marking(&packed);
        let fp2 = fingerprint_marking(&packed);
        assert_eq!(fp1, fp2, "same input must produce same fingerprint");
    }

    #[test]
    fn test_fingerprint_different_for_different_inputs() {
        let a = vec![1u8, 0, 0, 0];
        let b = vec![0u8, 1, 0, 0];
        let fp_a = fingerprint_marking(&a);
        let fp_b = fingerprint_marking(&b);
        assert_ne!(
            fp_a, fp_b,
            "different markings should produce different fingerprints"
        );
    }

    #[test]
    fn test_fingerprint_empty_input() {
        let empty: Vec<u8> = vec![];
        let fp = fingerprint_marking(&empty);
        // Should produce a deterministic fingerprint even for empty input
        // (empty marking = net with 0 packed places)
        let fp2 = fingerprint_marking(&empty);
        assert_eq!(
            fp, fp2,
            "empty input must produce a deterministic fingerprint"
        );
        // Empty input should produce a different fingerprint than non-empty
        let non_empty = vec![1u8];
        let fp_non_empty = fingerprint_marking(&non_empty);
        assert_ne!(
            fp, fp_non_empty,
            "empty input fingerprint should differ from non-empty input"
        );
    }

    #[test]
    fn test_fingerprint_uses_full_128_bits() {
        let packed = vec![42u8; 100];
        let fp = fingerprint_marking(&packed);
        let hi = (fp >> 64) as u64;
        let lo = fp as u64;
        // Both halves should be non-zero for a non-trivial input
        assert_ne!(hi, 0, "upper 64 bits should be non-zero");
        assert_ne!(lo, 0, "lower 64 bits should be non-zero");
    }
}
