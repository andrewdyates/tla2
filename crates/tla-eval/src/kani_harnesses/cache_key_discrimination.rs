// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kani proofs for NaryOpCacheKey discrimination soundness.
//!
//! Verifies that the operator result cache correctly discriminates between
//! different evaluation contexts. Each field in `NaryOpCacheKey` exists to
//! prevent a specific class of cache collision bug:
//!
//! - `instance_subs_id`: Different INSTANCE substitutions (#3024)
//! - `local_ops_id`: Different LET-scoped operator environments (#3024)
//! - `param_args_hash`: Different parametrized INSTANCE arguments (#2986)
//! - `args_hash`: Different operator arguments (#3020)
//! - `is_next_state`: Current vs primed evaluation context (#295)
//!
//! Properties verified:
//! - P1: Keys differing in instance_subs_id are not equal
//! - P2: Keys differing in local_ops_id are not equal
//! - P3: Keys differing in param_args_hash are not equal
//! - P4: Keys differing in is_next_state are not equal
//! - P5: Keys differing in op_name are not equal
//! - P6: Keys differing in def_loc are not equal
//! - P7: Keys differing in args_hash are not equal
//! - P8: Equal keys have equal hashes (Hash-Eq consistency)
//! - P9: Reflexivity — a key equals itself

#[cfg(kani)]
mod kani_proofs {
    use crate::cache::op_result_cache::{hash_args, NaryOpCacheKey};
    use crate::value::Value;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use tla_core::name_intern::NameId;

    /// Create a baseline cache key with deterministic field values.
    fn baseline_key() -> NaryOpCacheKey {
        let args = [Value::Bool(true)];
        NaryOpCacheKey {
            shared_id: 1,
            local_ops_id: 100,
            instance_subs_id: 200,
            op_name: NameId(1),
            def_loc: 42,
            is_next_state: false,
            args_hash: hash_args(&args),
            param_args_hash: 0,
        }
    }

    fn hash_key(key: &NaryOpCacheKey) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    // =========================================================================
    // P1: Different instance_subs_id → different keys
    // Bug fix #3024: Without this, different INSTANCE contexts share results.
    // =========================================================================

    #[kani::proof]
    fn cache_key_different_instance_subs() {
        let id1: u64 = kani::any();
        let id2: u64 = kani::any();
        kani::assume(id1 != id2);

        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.instance_subs_id = id1;
        k2.instance_subs_id = id2;

        assert_ne!(
            k1, k2,
            "different instance_subs_id must produce different keys"
        );
    }

    // =========================================================================
    // P2: Different local_ops_id → different keys
    // Bug fix #3024: Without this, different LET scopes share results.
    // =========================================================================

    #[kani::proof]
    fn cache_key_different_local_ops() {
        let id1: u64 = kani::any();
        let id2: u64 = kani::any();
        kani::assume(id1 != id2);

        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.local_ops_id = id1;
        k2.local_ops_id = id2;

        assert_ne!(k1, k2, "different local_ops_id must produce different keys");
    }

    // =========================================================================
    // P3: Different param_args_hash → different keys
    // Bug fix #2986: Without this, P(Succ)!Op and P(Pred)!Op share results.
    // =========================================================================

    #[kani::proof]
    fn cache_key_different_param_args_hash() {
        let h1: u64 = kani::any();
        let h2: u64 = kani::any();
        kani::assume(h1 != h2);

        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.param_args_hash = h1;
        k2.param_args_hash = h2;

        assert_ne!(
            k1, k2,
            "different param_args_hash must produce different keys"
        );
    }

    // =========================================================================
    // P4: Different is_next_state → different keys
    // Bug fix #295: Without this, primed and unprimed contexts share results.
    // =========================================================================

    #[kani::proof]
    fn cache_key_different_next_state() {
        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.is_next_state = false;
        k2.is_next_state = true;

        assert_ne!(k1, k2, "current vs next-state must produce different keys");
    }

    // =========================================================================
    // P5: Different op_name → different keys
    // =========================================================================

    #[kani::proof]
    fn cache_key_different_op_name() {
        let n1: u32 = kani::any();
        let n2: u32 = kani::any();
        kani::assume(n1 != n2);

        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.op_name = NameId(n1);
        k2.op_name = NameId(n2);

        assert_ne!(k1, k2, "different op_name must produce different keys");
    }

    // =========================================================================
    // P6: Different def_loc → different keys
    // =========================================================================

    #[kani::proof]
    fn cache_key_different_def_loc() {
        let loc1: u32 = kani::any();
        let loc2: u32 = kani::any();
        kani::assume(loc1 != loc2);

        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.def_loc = loc1;
        k2.def_loc = loc2;

        assert_ne!(k1, k2, "different def_loc must produce different keys");
    }

    // =========================================================================
    // P7: Different args_hash → different keys
    // Part of #3020: args_hash replaced Arc<[Value]> args field.
    // =========================================================================

    #[kani::proof]
    fn cache_key_different_args_hash() {
        let h1: u64 = kani::any();
        let h2: u64 = kani::any();
        kani::assume(h1 != h2);

        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.args_hash = h1;
        k2.args_hash = h2;

        assert_ne!(k1, k2, "different args_hash must produce different keys");
    }

    // =========================================================================
    // P8: Hash-Eq consistency — equal keys must have equal hashes
    // =========================================================================

    #[kani::proof]
    fn cache_key_hash_eq_consistency() {
        let k1 = baseline_key();
        let k2 = baseline_key();

        if k1 == k2 {
            assert_eq!(
                hash_key(&k1),
                hash_key(&k2),
                "equal keys must have equal hashes"
            );
        }
    }

    // =========================================================================
    // P9: Reflexivity — a key equals itself
    // =========================================================================

    #[kani::proof]
    fn cache_key_eq_reflexive() {
        let k = baseline_key();
        assert_eq!(k, k, "a key must equal itself");
    }
}

// =========================================================================
// Test mirrors: verify the same properties using #[test] for fast CI feedback
// =========================================================================

#[cfg(test)]
mod tests {
    use crate::cache::op_result_cache::{hash_args, NaryOpCacheKey};
    use crate::value::Value;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use tla_core::name_intern::NameId;

    fn baseline_key() -> NaryOpCacheKey {
        let args = [Value::Bool(true)];
        NaryOpCacheKey {
            shared_id: 1,
            local_ops_id: 100,
            instance_subs_id: 200,
            op_name: NameId(1),
            def_loc: 42,
            is_next_state: false,
            args_hash: hash_args(&args),
            param_args_hash: 0,
        }
    }

    fn hash_key(key: &NaryOpCacheKey) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_different_instance_subs_not_equal() {
        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.instance_subs_id = 100;
        k2.instance_subs_id = 200;
        assert_ne!(k1, k2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_different_local_ops_not_equal() {
        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.local_ops_id = 100;
        k2.local_ops_id = 200;
        assert_ne!(k1, k2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_different_param_args_hash_not_equal() {
        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.param_args_hash = 111;
        k2.param_args_hash = 222;
        assert_ne!(k1, k2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_different_next_state_not_equal() {
        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.is_next_state = false;
        k2.is_next_state = true;
        assert_ne!(k1, k2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_different_args_hash_not_equal() {
        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.args_hash = 111;
        k2.args_hash = 222;
        assert_ne!(k1, k2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_hash_eq_consistency() {
        let k1 = baseline_key();
        let k2 = baseline_key();
        assert_eq!(k1, k2);
        assert_eq!(hash_key(&k1), hash_key(&k2));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_different_op_name_not_equal() {
        let mut k1 = baseline_key();
        let mut k2 = baseline_key();
        k1.op_name = NameId(10);
        k2.op_name = NameId(20);
        assert_ne!(k1, k2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_reflexive() {
        let k = baseline_key();
        assert_eq!(k, k.clone());
    }
}
