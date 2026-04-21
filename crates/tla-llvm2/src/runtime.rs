// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Runtime helper function signatures for LLVM2-compiled code.
//!
//! Compound TLA+ operations (set membership, record access, function
//! application, sequence ops) are lowered to calls to runtime helper
//! functions defined in [`tla_jit::abi`]. This module catalogs the
//! helper function signatures so the LLVM2 backend can declare and
//! resolve them at link time.
//!
//! # Architecture
//!
//! ```text
//! tMIR (Call @helper) --[LLVM2]--> native call instruction
//!                                        |
//!                                        v
//!                             runtime helper (Rust extern "C")
//! ```
//!
//! The helpers are `#[no_mangle] pub extern "C"` functions. LLVM2-compiled
//! code references them by symbol name and the native linker resolves them
//! at load time (dlopen/dlsym for AOT, or direct address for JIT).

use tmir::ty::Ty;

/// Description of a runtime helper function available to compiled code.
#[derive(Debug, Clone)]
pub struct RuntimeHelper {
    /// Symbol name (must match the `#[no_mangle]` Rust function name).
    pub symbol: &'static str,
    /// Parameter types.
    pub params: &'static [Ty],
    /// Return type.
    pub ret: Ty,
}

/// All runtime helper functions that LLVM2-compiled TLA+ code may call.
///
/// These correspond to the `jit_*` functions in `tla_jit::abi` and
/// `tla_jit::bfs_step`.
pub static RUNTIME_HELPERS: &[RuntimeHelper] = &[
    RuntimeHelper {
        symbol: "jit_pow_i64",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_set_contains_i64",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_record_get_i64",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_func_apply_i64",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_compound_count",
        params: &[Ty::Ptr],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_seq_get_i64",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_func_set_membership_check",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_record_new_scalar",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_set_diff_i64",
        params: &[Ty::Ptr, Ty::Ptr],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_seq_tail",
        params: &[Ty::Ptr],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_seq_append",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_set_union_i64",
        params: &[Ty::Ptr, Ty::Ptr],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_xxh3_fingerprint_64",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "jit_xxh3_fingerprint_128",
        params: &[Ty::Ptr, Ty::I64],
        ret: Ty::Void,
    },
];

/// Look up a runtime helper by symbol name.
pub fn find_helper(symbol: &str) -> Option<&'static RuntimeHelper> {
    RUNTIME_HELPERS.iter().find(|h| h.symbol == symbol)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_helper_exists() {
        let h = find_helper("jit_pow_i64").expect("jit_pow_i64 should exist");
        assert_eq!(h.params.len(), 2);
        assert_eq!(h.ret, Ty::I64);
    }

    #[test]
    fn test_find_helper_missing() {
        assert!(find_helper("nonexistent").is_none());
    }

    #[test]
    fn test_all_helpers_have_symbols() {
        for h in RUNTIME_HELPERS {
            assert!(!h.symbol.is_empty(), "helper has empty symbol name");
            assert!(
                h.symbol.starts_with("jit_"),
                "helper '{}' does not start with jit_",
                h.symbol,
            );
        }
    }
}
