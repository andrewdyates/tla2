// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-compatible FP64 polynomial rolling hash (Rabin fingerprint)
//!
//! This module implements the same fingerprinting algorithm as TLC's FP64.java,
//! enabling incremental fingerprint computation. Instead of hashing entire values
//! from scratch, fingerprints can be extended one component at a time.
//!
//! This is critical for performance in specs like `bosco` where operations like
//! `[rcvd EXCEPT ![self] = newRcvd]` repeatedly modify large functions. With
//! incremental fingerprinting, we can cache the base fingerprint and only extend
//! with the modified entry, achieving O(1) instead of O(n) per modification.
//!
//! # Algorithm
//!
//! FP64 is a polynomial rolling hash over GF(2^64). It uses an irreducible
//! polynomial as the modulus and precomputes a 256-entry table for byte-at-a-time
//! extension. The specific polynomial is from TLC's FP64.java <code>Polys\[0\]</code>.
//!
//! # Reference
//!
//! - TLC source: `tlatools/org.lamport.tlatools/src/tlc2/util/FP64.java`
//! - Original authors: Allan Heydon and Marc Najork (Compaq, 1999)

use crate::Value;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// Irreducible polynomial used as the initial fingerprint value.
/// This is <code>Polys\[0\]</code> from TLC's FP64.java.
pub const FP64_INIT: u64 = 0x911498AE0E66BAD6;

/// Internal constants for table computation
const ONE: u64 = 0x8000000000000000;
const X63: u64 = 0x1;

/// Precomputed byte mod table for polynomial rolling hash.
/// This table is computed at compile time from the irreducible polynomial.
/// Each entry ByteModTable_7[b] represents the contribution of byte b to the fingerprint.
///
/// Note: Uses const fn instead of OnceLock to avoid ptr_mask intrinsic that
/// blocks Kani verification. See #169.
static BYTE_MOD_TABLE: [u64; 256] = compute_byte_mod_table(FP64_INIT);

/// Get the byte mod table.
/// Zero runtime cost - table is computed at compile time.
#[inline]
fn get_byte_mod_table() -> &'static [u64; 256] {
    &BYTE_MOD_TABLE
}

/// Compute the ByteModTable_7 from TLC's FP64.java Init() method.
/// This precomputes the polynomial contributions for all 256 byte values.
///
/// Note: Uses index-based while loops (not iterators) for const fn compatibility.
const fn compute_byte_mod_table(irred_poly: u64) -> [u64; 256] {
    // Maximum power needed: 127 - 7*8 = 71, so we need 72 entries
    const PLENGTH: usize = 72;
    let mut power_table = [0u64; PLENGTH];

    // Build power table: power_table[i] = x^i mod IrredPoly
    // Uses while loop instead of for/iter_mut for const fn compatibility
    let mut t = ONE;
    let mut i = 0;
    while i < PLENGTH {
        power_table[i] = t;
        // t = t * x (multiplication in GF(2^64))
        let mask = if (t & X63) != 0 { irred_poly } else { 0 };
        t = (t >> 1) ^ mask;
        i += 1;
    }

    // Compute ByteModTable_7: the 7th iteration of ByteModTable initialization
    // This is what TLC uses for byte-at-a-time extension
    // Uses while loops instead of for/enumerate for const fn compatibility
    let mut table = [0u64; 256];
    let mut j = 0;
    while j < 256 {
        let mut v = 0u64;
        let mut k = 0;
        while k <= 7 {
            if (j & (1usize << k)) != 0 {
                v ^= power_table[127 - 7 * 8 - k];
            }
            k += 1;
        }
        table[j] = v;
        j += 1;
    }
    table
}

/// Extend a fingerprint by one byte.
///
/// This is the core operation of FP64. It corresponds to TLC's:
/// ```java
/// fp = ((fp >>> 8) ^ (mod[(b ^ ((int)fp)) & 0xFF]));
/// ```
#[inline]
pub fn fp64_extend_byte(fp: u64, b: u8) -> u64 {
    let table = get_byte_mod_table();
    let idx = ((b as u64) ^ fp) as usize & 0xFF;
    (fp >> 8) ^ table[idx]
}

/// Extend a fingerprint by an i32 (4 bytes, little-endian).
/// Corresponds to TLC's `FP64.Extend(fp, int)`.
#[inline]
pub fn fp64_extend_i32(mut fp: u64, x: i32) -> u64 {
    let bytes = x.to_le_bytes();
    for &b in &bytes {
        fp = fp64_extend_byte(fp, b);
    }
    fp
}

/// Extend a fingerprint by an i64/long (8 bytes, little-endian).
/// Corresponds to TLC's `FP64.Extend(fp, long)`.
#[inline]
pub fn fp64_extend_i64(mut fp: u64, x: i64) -> u64 {
    let bytes = x.to_le_bytes();
    for &b in &bytes {
        fp = fp64_extend_byte(fp, b);
    }
    fp
}

/// Extend a fingerprint by a string.
/// Corresponds to TLC's `FP64.Extend(fp, String)`.
///
/// Note: TLC uses Java's charAt which returns UTF-16 code units.
/// For ASCII strings (common in TLA+), this is equivalent to bytes.
/// For non-ASCII, we use the same UTF-16 encoding as TLC.
#[inline]
pub(crate) fn fp64_extend_str(mut fp: u64, s: &str) -> u64 {
    // Iterate over UTF-16 code units to match Java's behavior
    for c in s.encode_utf16() {
        // Java's char is 16-bit, but FP64.Extend(fp, char) only uses lower 8 bits
        // Looking at TLC source: fp = ((fp >>> 8) ^ (mod[(((int)c) ^ ((int)fp)) & 0xFF]))
        // It masks with 0xFF, so only the low byte of each char is used
        fp = fp64_extend_byte(fp, (c & 0xFF) as u8);
    }
    fp
}

/// Extend a fingerprint by a BigInt.
///
/// TLC fingerprints integers by extending with their byte representation.
/// For consistency with IntValue.fingerPrint in TLC, we use the value as i32 when it fits,
/// otherwise as i64.
#[inline]
pub(crate) fn fp64_extend_bigint(fp: u64, n: &BigInt) -> u64 {
    // Try to fit in i32 first (matches TLC's IntValue which uses int)
    if let Some(i) = n.to_i32() {
        return fp64_extend_i32(fp, i);
    }
    // Fall back to i64 for larger values
    if let Some(i) = n.to_i64() {
        return fp64_extend_i64(fp, i);
    }
    // For very large BigInts, use the signed bytes representation
    let bytes = n.to_signed_bytes_le();
    let mut fp = fp;
    for &b in &bytes {
        fp = fp64_extend_byte(fp, b);
    }
    fp
}

/// TLC Value type constants for fingerprinting.
/// These match TLC's ValueConstants.java exactly.
///
/// When fingerprinting a value, we first extend with its type tag,
/// then with its contents. This ensures different value types with
/// the same content produce different fingerprints.
pub mod value_tags {
    // TLC value type tags for fingerprinting (tlc2.value.impl.Value)
    // Only tags used in value_fingerprint.rs are included; unused tags (REALVALUE=2,
    // RECORDVALUE=4, TUPLEVALUE=7, OPRCDVALUE=11, METHODVALUE=12, INTERVALVALUE=23,
    // UNDEFVALUE=24, LAZYVALUE=25, DUMMYVALUE=26) can be added back from TLC source.
    pub const BOOLVALUE: i64 = 0;
    pub const INTVALUE: i64 = 1;
    pub const STRINGVALUE: i64 = 3;
    pub const SETENUMVALUE: i64 = 5;
    pub const SETPREDVALUE: i64 = 6;
    pub const FCNLAMBDAVALUE: i64 = 8;
    pub const FCNRCDVALUE: i64 = 9;
    pub const OPLAMBDAVALUE: i64 = 10;
    pub const SETOFFCNSVALUE: i64 = 13;
    pub const SETOFRCDSVALUE: i64 = 14;
    pub const SETOFTUPLESVALUE: i64 = 15;
    pub const SUBSETVALUE: i64 = 16;
    pub const SETDIFFVALUE: i64 = 17;
    pub const SETCAPVALUE: i64 = 18;
    pub const SETCUPVALUE: i64 = 19;
    pub const UNIONVALUE: i64 = 20;
    pub const MODELVALUE: i64 = 21;
    pub const USERVALUE: i64 = 22;
}

// ============================================================================
// Precomputed FP64 fingerprints for primitive values
// ============================================================================

/// Precomputed FP64 fingerprint of `Value::Bool(true)` starting from `FP64_INIT`.
///
/// Part of #3805: eliminates 9 byte-at-a-time hash operations per Bool fingerprint
/// on the state dedup hot path. Bool values appear in nearly every TLA+ state.
///
/// Computed as: fp64_extend_byte(fp64_extend_i64(FP64_INIT, BOOLVALUE), b't')
pub static FP64_BOOL_TRUE: u64 = {
    let fp = const_fp64_extend_i64(FP64_INIT, value_tags::BOOLVALUE);
    const_fp64_extend_byte(fp, b't')
};

/// Precomputed FP64 fingerprint of `Value::Bool(false)` starting from `FP64_INIT`.
pub static FP64_BOOL_FALSE: u64 = {
    let fp = const_fp64_extend_i64(FP64_INIT, value_tags::BOOLVALUE);
    const_fp64_extend_byte(fp, b'f')
};

/// Range of precomputed SmallInt FP64 fingerprints.
///
/// Covers integers -256..1024 (1280 entries, ~10KB). This range captures:
/// - 1-indexed sequence/tuple/record keys (1..N for typical N < 1000)
/// - Common counter values, process IDs, and boolean-encoded flags
/// - Negative values in specs like clock diffs and offsets
///
/// Part of #3805: replaces 12 byte-at-a-time hash operations per SmallInt fingerprint
/// with a single array lookup. SmallInt is the most common leaf value type.
const SMALLINT_FP_TABLE_MIN: i64 = -256;
const SMALLINT_FP_TABLE_MAX: i64 = 1023; // inclusive
const SMALLINT_FP_TABLE_LEN: usize = (SMALLINT_FP_TABLE_MAX - SMALLINT_FP_TABLE_MIN + 1) as usize;

/// Precomputed FP64 fingerprints for SmallInt values in [-256, 1023].
///
/// Index formula: table[(n - SMALLINT_FP_TABLE_MIN) as usize]
static SMALLINT_FP_TABLE: [u64; SMALLINT_FP_TABLE_LEN] = {
    let mut table = [0u64; SMALLINT_FP_TABLE_LEN];
    let mut i = 0usize;
    while i < SMALLINT_FP_TABLE_LEN {
        let n = (i as i64) + SMALLINT_FP_TABLE_MIN;
        let fp = const_fp64_extend_i64(FP64_INIT, value_tags::INTVALUE);
        // Values that fit in i32 use fp64_extend_i32, others use fp64_extend_i64
        table[i] = if n >= (i32::MIN as i64) && n <= (i32::MAX as i64) {
            const_fp64_extend_i32(fp, n as i32)
        } else {
            const_fp64_extend_i64(fp, n)
        };
        i += 1;
    }
    table
};

/// Look up the precomputed FP64 fingerprint for a SmallInt value.
///
/// Returns `Some(fp)` if `n` is in the precomputed range [-256, 1023],
/// `None` otherwise (caller must fall back to byte-at-a-time computation).
///
/// Part of #3805: This is the primary fast path for state fingerprinting.
/// Called millions of times per model checking run.
#[inline(always)]
pub fn fp64_smallint_lookup(n: i64) -> Option<u64> {
    if n >= SMALLINT_FP_TABLE_MIN && n <= SMALLINT_FP_TABLE_MAX {
        // SAFETY: bounds checked above
        Some(SMALLINT_FP_TABLE[(n - SMALLINT_FP_TABLE_MIN) as usize])
    } else {
        None
    }
}

/// Look up the precomputed FP64 fingerprint for a Bool value.
///
/// Part of #3805: eliminates byte-at-a-time computation for the most common
/// leaf value type alongside SmallInt.
#[inline(always)]
pub fn fp64_bool_lookup(b: bool) -> u64 {
    if b {
        FP64_BOOL_TRUE
    } else {
        FP64_BOOL_FALSE
    }
}

// Const-fn versions of fp64_extend for compile-time table computation.
// These mirror the runtime versions but use const-compatible operations.

#[inline]
const fn const_fp64_extend_byte(fp: u64, b: u8) -> u64 {
    let idx = ((b as u64) ^ fp) as usize & 0xFF;
    (fp >> 8) ^ BYTE_MOD_TABLE[idx]
}

#[inline]
const fn const_fp64_extend_i32(mut fp: u64, x: i32) -> u64 {
    let bytes = x.to_le_bytes();
    let mut i = 0;
    while i < 4 {
        fp = const_fp64_extend_byte(fp, bytes[i]);
        i += 1;
    }
    fp
}

#[inline]
const fn const_fp64_extend_i64(mut fp: u64, x: i64) -> u64 {
    let bytes = x.to_le_bytes();
    let mut i = 0;
    while i < 8 {
        fp = const_fp64_extend_byte(fp, bytes[i]);
        i += 1;
    }
    fp
}

/// Compute the fingerprint of a single value.
///
/// This is useful for TLCExt!TLCFP which returns the fingerprint of a value.
/// Uses TLC-compatible FP64 polynomial rolling hash for deterministic fingerprinting.
///
/// Part of #3285: FP64 per-value caches removed to reduce working set. FP64 is now
/// recomputed on demand each time, matching TLC which does not cache per-value FP64.
/// The additive (commutative) fingerprint is still cached for state-level dedup.
///
/// Returns `FingerprintError` if a value exceeds TLC-compatible limits (e.g.,
/// a set with more than 2^31 elements).
pub fn value_fingerprint(value: &Value) -> crate::value::value_fingerprint::FingerprintResult<u64> {
    value.fingerprint_extend(FP64_INIT)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{FuncValue, IntIntervalFunc, SeqValue, Value};
    use std::sync::Arc;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_byte_mod_table_initialization() {
        // Ensure the table initializes without panicking
        let table = get_byte_mod_table();
        // Table should have 256 entries
        assert_eq!(table.len(), 256);
        // Entry 0 should be 0 (no bits set)
        assert_eq!(table[0], 0);

        // Spot-check known TLC-compatible entries.
        assert_eq!(table[1], 0x3adc71408edceae1);
        assert_eq!(table[2], 0x75b8e2811db9d5c2);
        assert_eq!(table[3], 0x4f6493c193653f23);
        assert_eq!(table[7], 0xa41556c3a81694a7);
        assert_eq!(table[31], 0x9b63aa770aa586e5);
        assert_eq!(table[63], 0x2e3214f2875a9286);
        assert_eq!(table[64], 0x488a4c5707335d6b);
        assert_eq!(table[127], 0x66b858a58069cfed);
        assert_eq!(table[128], FP64_INIT);
        assert_eq!(table[255], 0xf7acc00b8e0f753b);

        // Table should be fully populated and collision-free for byte inputs.
        assert_eq!(table.iter().filter(|&&x| x != 0).count(), 255);
        let unique: std::collections::HashSet<u64> = table.iter().copied().collect();
        assert_eq!(unique.len(), 256);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fp64_extend_byte() {
        // Start with the initial fingerprint
        let fp = FP64_INIT;
        // Extending with 0 should change the fingerprint
        let fp2 = fp64_extend_byte(fp, 0);
        assert_ne!(fp, fp2);
        // Same input should give same output
        let fp3 = fp64_extend_byte(fp, 0);
        assert_eq!(fp2, fp3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fp64_extend_deterministic() {
        // Fingerprinting should be deterministic
        let fp1 = fp64_extend_str(FP64_INIT, "hello");
        let fp2 = fp64_extend_str(FP64_INIT, "hello");
        assert_eq!(fp1, fp2);

        // Different strings should (usually) produce different fingerprints
        let fp3 = fp64_extend_str(FP64_INIT, "world");
        assert_ne!(fp1, fp3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fp64_extend_i64() {
        let fp = FP64_INIT;
        // Extending with the same value twice should give the same result
        let fp1 = fp64_extend_i64(fp, 42);
        let fp2 = fp64_extend_i64(fp, 42);
        assert_eq!(fp1, fp2);

        // Different values should give different results
        let fp3 = fp64_extend_i64(fp, 43);
        assert_ne!(fp1, fp3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_type_tags_match_tlc() {
        // Verify our type tags match TLC's ValueConstants
        use value_tags::*;
        assert_eq!(BOOLVALUE, 0);
        assert_eq!(INTVALUE, 1);
        assert_eq!(STRINGVALUE, 3);
        assert_eq!(SETENUMVALUE, 5);
        assert_eq!(FCNRCDVALUE, 9);
        assert_eq!(MODELVALUE, 21);
    }

    /// Part of #3285: FP64 caches removed, verify deterministic recomputation.
    #[test]
    fn fp64_func_deterministic_without_cache() {
        let value = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(2), Value::Bool(false)),
        ])));

        let fp1 = value_fingerprint(&value).expect("function fingerprint should succeed");
        let fp2 =
            value_fingerprint(&value).expect("function fingerprint should stay deterministic");

        assert_eq!(fp1, fp2);
    }

    #[test]
    fn fp64_int_func_deterministic_without_cache() {
        let value = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![Value::Bool(true), Value::Bool(false)],
        )));

        let fp1 = value_fingerprint(&value).expect("int function fingerprint should succeed");
        let fp2 =
            value_fingerprint(&value).expect("int function fingerprint should stay deterministic");

        assert_eq!(fp1, fp2);
    }

    #[test]
    fn fp64_set_deterministic_without_cache() {
        let value = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);

        let fp1 = value_fingerprint(&value).expect("set fingerprint should succeed");
        let fp2 = value_fingerprint(&value).expect("set fingerprint should stay deterministic");

        assert_eq!(fp1, fp2);
    }

    #[test]
    fn fp64_seq_deterministic_without_cache() {
        let value = Value::Seq(Arc::new(SeqValue::from(vec![
            Value::Bool(true),
            Value::Bool(false),
        ])));

        let fp1 = value_fingerprint(&value).expect("sequence fingerprint should succeed");
        let fp2 =
            value_fingerprint(&value).expect("sequence fingerprint should stay deterministic");

        assert_eq!(fp1, fp2);
    }

    #[test]
    fn fp64_record_deterministic_without_cache() {
        let value = Value::record([("x", Value::Bool(true)), ("y", Value::Bool(false))]);

        let fp1 = value_fingerprint(&value).expect("record fingerprint should succeed");
        let fp2 = value_fingerprint(&value).expect("record fingerprint should stay deterministic");

        assert_eq!(fp1, fp2);
    }

    // Part of #3805: Tests for precomputed fingerprint lookup tables.

    #[test]
    fn precomputed_bool_true_matches_fp64() {
        let fp_computed = {
            let fp = fp64_extend_i64(FP64_INIT, value_tags::BOOLVALUE);
            crate::fingerprint::fp64_extend_byte(fp, b't')
        };
        assert_eq!(
            FP64_BOOL_TRUE, fp_computed,
            "precomputed Bool(true) FP must match byte-at-a-time FP64"
        );
        assert_eq!(
            fp64_bool_lookup(true),
            fp_computed,
            "fp64_bool_lookup(true) must match byte-at-a-time FP64"
        );
    }

    #[test]
    fn precomputed_bool_false_matches_fp64() {
        let fp_computed = {
            let fp = fp64_extend_i64(FP64_INIT, value_tags::BOOLVALUE);
            crate::fingerprint::fp64_extend_byte(fp, b'f')
        };
        assert_eq!(
            FP64_BOOL_FALSE, fp_computed,
            "precomputed Bool(false) FP must match byte-at-a-time FP64"
        );
        assert_eq!(
            fp64_bool_lookup(false),
            fp_computed,
            "fp64_bool_lookup(false) must match byte-at-a-time FP64"
        );
    }

    #[test]
    fn precomputed_smallint_table_matches_fp64_for_sample_values() {
        // Test a representative sample of values across the precomputed range.
        let test_values: Vec<i64> = vec![
            -256, -255, -128, -1, 0, 1, 2, 3, 10, 100, 255, 256, 500, 1000, 1023,
        ];
        for n in test_values {
            let fp_computed = {
                let fp = fp64_extend_i64(FP64_INIT, value_tags::INTVALUE);
                if i32::try_from(n).is_ok() {
                    fp64_extend_i32(fp, n as i32)
                } else {
                    fp64_extend_i64(fp, n)
                }
            };
            let fp_lookup = fp64_smallint_lookup(n)
                .unwrap_or_else(|| panic!("SmallInt({n}) should be in precomputed range"));
            assert_eq!(
                fp_lookup, fp_computed,
                "precomputed SmallInt({n}) FP must match byte-at-a-time FP64"
            );
        }
    }

    #[test]
    fn precomputed_smallint_out_of_range_returns_none() {
        assert!(
            fp64_smallint_lookup(-257).is_none(),
            "-257 is below precomputed range"
        );
        assert!(
            fp64_smallint_lookup(1024).is_none(),
            "1024 is above precomputed range"
        );
        assert!(
            fp64_smallint_lookup(i64::MAX).is_none(),
            "i64::MAX is above precomputed range"
        );
        assert!(
            fp64_smallint_lookup(i64::MIN).is_none(),
            "i64::MIN is below precomputed range"
        );
    }

    #[test]
    fn precomputed_smallint_table_has_no_collisions() {
        // Verify no two different integers in the table produce the same fingerprint.
        let unique: std::collections::HashSet<u64> = SMALLINT_FP_TABLE.iter().copied().collect();
        assert_eq!(
            unique.len(),
            SMALLINT_FP_TABLE_LEN,
            "precomputed SmallInt table should have no collisions ({} unique out of {})",
            unique.len(),
            SMALLINT_FP_TABLE_LEN,
        );
    }

    #[test]
    fn precomputed_smallint_matches_value_fingerprint() {
        // Verify that the precomputed lookup produces the same result as
        // the full value_fingerprint() path.
        for n in [-256i64, -1, 0, 1, 42, 100, 1023] {
            let via_lookup = fp64_smallint_lookup(n).unwrap();
            let via_value = value_fingerprint(&Value::SmallInt(n))
                .expect("SmallInt fingerprint should succeed");
            assert_eq!(
                via_lookup, via_value,
                "precomputed SmallInt({n}) must match value_fingerprint()"
            );
        }
    }

    #[test]
    fn precomputed_bool_matches_value_fingerprint() {
        let via_lookup_true = fp64_bool_lookup(true);
        let via_value_true =
            value_fingerprint(&Value::Bool(true)).expect("Bool fingerprint should succeed");
        assert_eq!(
            via_lookup_true, via_value_true,
            "precomputed Bool(true) must match value_fingerprint()"
        );

        let via_lookup_false = fp64_bool_lookup(false);
        let via_value_false =
            value_fingerprint(&Value::Bool(false)).expect("Bool fingerprint should succeed");
        assert_eq!(
            via_lookup_false, via_value_false,
            "precomputed Bool(false) must match value_fingerprint()"
        );
    }
}
