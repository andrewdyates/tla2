// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Runtime helper function signatures for LLVM2-compiled code.
//!
//! Compound TLA+ operations (set membership, record access, function
//! application, sequence ops) are lowered to calls to runtime helper
//! functions implemented in `tla-llvm2-runtime`. This module catalogs the
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
/// These are implemented as `#[no_mangle] pub extern "C"` helpers in the
/// LLVM2 runtime library, mirroring the historical `jit_*` helper ABI.
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
        ret: Ty::Unit,
    },
    // ========================================================================
    // tla_* runtime ABI (Option B, R27, #4318)
    //
    // Handle-based FFI for Phase 3/5 aggregate opcodes. All helpers take
    // `TlaHandle` (i64) operands and return a `TlaHandle` — see
    // `runtime_abi::tla_ops::handle` for the encoding. Boolean-valued
    // predicates (`tla_set_in`, `tla_set_subseteq`) return i64 1/0 and
    // use `NIL_HANDLE` as a "fall back to interpreter" sentinel.
    // ========================================================================
    // tla_handle_nil — NIL sentinel constructor, no operands.
    RuntimeHelper {
        symbol: "tla_handle_nil",
        params: &[],
        ret: Ty::I64,
    },
    // clear_tla_arena — action-boundary arena reset.
    RuntimeHelper {
        symbol: "clear_tla_arena",
        params: &[],
        ret: Ty::Unit,
    },
    // clear_tla_iter_arena — iteration-boundary quantifier-iter arena reset.
    // Paired with `tla_quantifier_iter_*` to release per-iteration handles
    // without dropping the surrounding action arena. Registered alongside
    // `clear_tla_arena` in `register_tla_ops_symbols` (#4318 Phase 5).
    RuntimeHelper {
        symbol: "clear_tla_iter_arena",
        params: &[],
        ret: Ty::Unit,
    },
    // tla_set_enum_N — N-element set literal. N = 0..=8.
    RuntimeHelper {
        symbol: "tla_set_enum_0",
        params: &[],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_1",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_2",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_3",
        params: &[Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_4",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_5",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_6",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_7",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_enum_8",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_set_in — elem ∈ set. Returns i64 1/0, or NIL on error.
    RuntimeHelper {
        symbol: "tla_set_in",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_set_{union,intersect,diff} — binary set algebra.
    RuntimeHelper {
        symbol: "tla_set_union",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_intersect",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_set_diff",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_set_subseteq — ⊆ predicate. Returns i64 1/0, or NIL on error.
    RuntimeHelper {
        symbol: "tla_set_subseteq",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_set_powerset — SUBSET s. Returns handle or NIL.
    RuntimeHelper {
        symbol: "tla_set_powerset",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // tla_set_big_union — UNION s. Flatten set-of-sets.
    RuntimeHelper {
        symbol: "tla_set_big_union",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // tla_set_range — lo..hi. `lo` and `hi` are raw i64 scalars.
    RuntimeHelper {
        symbol: "tla_set_range",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_set_ksubset — k-element subsets of base. `k` is raw i64.
    RuntimeHelper {
        symbol: "tla_set_ksubset",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // ========================================================================
    // tla_tuple_* — Option B tuple family (R27, #4318).
    //
    // Nine N-arity monomorphs for tuple literals `<<e_1, …, e_N>>` with
    // N = 0..=8, plus `tla_tuple_get` for 1-indexed element access.
    // Returns `NIL_HANDLE` on out-of-range / non-tuple operands.
    // ========================================================================
    // tla_tuple_new_N — N-element tuple literal. N = 0..=8.
    RuntimeHelper {
        symbol: "tla_tuple_new_0",
        params: &[],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_1",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_2",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_3",
        params: &[Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_4",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_5",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_6",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_7",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tuple_new_8",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_tuple_get — `tup[idx]` 1-indexed. `idx` is a raw i64 scalar.
    RuntimeHelper {
        symbol: "tla_tuple_get",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // ========================================================================
    // tla_quantifier_* — Option B quantifier iterator family (R27, #4318).
    //
    // tir_lower emits a three-step loop skeleton for Phase 5 Forall/Exists/
    // Choose over a set domain (see `tmir_lower.rs:1813-2145`):
    //   iter_new(domain_handle) -> iter_handle     (once per quantifier)
    //   iter_done(iter_handle)  -> i64  (0 or 1)   (before each yield)
    //   iter_next(iter_handle)  -> elem_handle     (fetch + advance)
    // `tla_quantifier_runtime_error()` is the CHOOSE-runtime-error marker —
    // it never returns (aborts) and the emitted IR places `unreachable`
    // immediately after the call.
    //
    // Iteration order matches the interpreter's canonical set order
    // (`Value::iter_set`) — soundness contract §7.1 R2.
    //
    // Iterator handles are raw i64 arena indices (NOT tag-encoded), so the
    // helper signatures use i64 instead of TlaHandle-pattern for clarity.
    // ========================================================================
    RuntimeHelper {
        symbol: "tla_quantifier_iter_new",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_quantifier_iter_done",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_quantifier_iter_next",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // tla_quantifier_runtime_error — never-returns helper. Typed as
    // `Ty::Unit` because Ty has no `!` / Noreturn variant; tir_lower pairs
    // every emitted call with an `unreachable` instruction so the return
    // slot is never read.
    RuntimeHelper {
        symbol: "tla_quantifier_runtime_error",
        params: &[],
        ret: Ty::Unit,
    },
    // ========================================================================
    // tla_record_get / tla_func_apply / tla_domain — Option B record_func
    // family (R27, #4318).
    //
    // Three helpers covering record field access, function application, and
    // `DOMAIN f` across every eager function-like Value variant
    // (Func / IntFunc / Seq / Tuple / Record). `field_idx` in
    // `tla_record_get` is a raw i64 whose low 32 bits decode to an interned
    // `NameId` (same scalar convention as `lo`/`hi` in `tla_set_range`).
    // Each helper returns `NIL_HANDLE` when it cannot compute the result
    // (non-record, non-callable, out-of-domain, out-of-bounds, LazyFunc on
    // apply) so tir_lower can fall back to the interpreter.
    // ========================================================================
    RuntimeHelper {
        symbol: "tla_record_get",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_func_apply",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_domain",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // ========================================================================
    // tla_load_const / builtin family — Option B const_builtin (R27, #4318).
    //
    // `tla_load_const` resolves `LoadConst { idx }` against a per-worker
    // constant pool populated by the BFS driver. `tla_cardinality`,
    // `tla_is_finite_set`, and `tla_tostring` are thin FFI wrappers around
    // the corresponding `tla_value::Value` APIs. All return `NIL_HANDLE`
    // when they cannot compute the result (so tir_lower can fall back to
    // the interpreter).
    // ========================================================================
    RuntimeHelper {
        symbol: "tla_load_const",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_cardinality",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_is_finite_set",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_tostring",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // ========================================================================
    // tla_seq_* — Option B sequence family (R27, #4318).
    //
    // Nine N-arity monomorphs for sequence literals `<<e_1, …, e_N>>` with
    // N = 0..=8, plus 7 opcode helpers (`concat`, `len`, `head`, `tail`,
    // `append`, `subseq`, `set`). All helpers accept `TlaHandle` (i64) args,
    // return `TlaHandle` (or raw i64 for `tla_seq_len`), and fall back to
    // `NIL_HANDLE` on non-sequence / out-of-range operands so `tir_lower`
    // can route to the interpreter.
    // ========================================================================
    // tla_seq_new_N — N-element sequence literal. N = 0..=8.
    RuntimeHelper {
        symbol: "tla_seq_new_0",
        params: &[],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_1",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_2",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_3",
        params: &[Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_4",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_5",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_6",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_7",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    RuntimeHelper {
        symbol: "tla_seq_new_8",
        params: &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_seq_concat — `s1 \o s2` sequence concatenation.
    RuntimeHelper {
        symbol: "tla_seq_concat",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_seq_len — `Len(s)`. Returns raw i64 scalar, or NIL on error.
    RuntimeHelper {
        symbol: "tla_seq_len",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // tla_seq_head — `Head(s)`. First element. NIL on empty/non-seq.
    RuntimeHelper {
        symbol: "tla_seq_head",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // tla_seq_tail — `Tail(s)`. Drop first. NIL on empty/non-seq.
    RuntimeHelper {
        symbol: "tla_seq_tail",
        params: &[Ty::I64],
        ret: Ty::I64,
    },
    // tla_seq_append — `Append(s, x)`. Add element at the end.
    RuntimeHelper {
        symbol: "tla_seq_append",
        params: &[Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_seq_subseq — `SubSeq(s, lo, hi)` 1-indexed inclusive slice.
    // `lo`, `hi` are raw i64 scalars.
    RuntimeHelper {
        symbol: "tla_seq_subseq",
        params: &[Ty::I64, Ty::I64, Ty::I64],
        ret: Ty::I64,
    },
    // tla_seq_set — `Seq(S)`. Lazy `SeqSet` constructor.
    RuntimeHelper {
        symbol: "tla_seq_set",
        params: &[Ty::I64],
        ret: Ty::I64,
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
            // Helpers use two namespaces:
            // - `jit_*` for flat-state pointer ABI (historical)
            // - `tla_*` / `clear_tla_arena` for handle-based ABI (R27 Option B)
            assert!(
                h.symbol.starts_with("jit_")
                    || h.symbol.starts_with("tla_")
                    || h.symbol == "clear_tla_arena",
                "helper '{}' does not start with jit_/tla_ or match clear_tla_arena",
                h.symbol,
            );
        }
    }

    #[test]
    fn test_tla_set_helpers_registered() {
        // Foundation for R27 Option B — 18 tla_set_* entries plus the
        // shared lifecycle helpers (`tla_handle_nil`, `clear_tla_arena`).
        // Ensures tir_lower can resolve every tla_set_* emit site at link
        // time. If the count drifts, the tla_ops::set module added or
        // removed an entry without updating RUNTIME_HELPERS.
        let tla_set_count = RUNTIME_HELPERS
            .iter()
            .filter(|h| h.symbol.starts_with("tla_set_"))
            .count();
        assert_eq!(tla_set_count, 18, "expected 18 tla_set_* helpers");
        assert!(find_helper("tla_handle_nil").is_some());
        assert!(find_helper("clear_tla_arena").is_some());
    }

    #[test]
    fn test_tla_record_func_helpers_registered() {
        // R27 Option B record_func family — 3 helpers covering
        // `rec.field`, `f[arg]`, and `DOMAIN f`. Ensures tir_lower can
        // resolve the emit sites at link time. If any of these is missing
        // the JIT linker will fail at compile time for specs using the
        // corresponding opcodes.
        let get = find_helper("tla_record_get")
            .expect("missing RuntimeHelper entry for tla_record_get");
        assert_eq!(get.params.len(), 2, "tla_record_get takes (rec, field_idx)");
        assert_eq!(get.params[0], Ty::I64);
        assert_eq!(get.params[1], Ty::I64);
        assert_eq!(get.ret, Ty::I64);

        let apply = find_helper("tla_func_apply")
            .expect("missing RuntimeHelper entry for tla_func_apply");
        assert_eq!(apply.params.len(), 2, "tla_func_apply takes (f, arg)");
        assert_eq!(apply.params[0], Ty::I64);
        assert_eq!(apply.params[1], Ty::I64);
        assert_eq!(apply.ret, Ty::I64);

        let dom =
            find_helper("tla_domain").expect("missing RuntimeHelper entry for tla_domain");
        assert_eq!(dom.params.len(), 1, "tla_domain takes (f)");
        assert_eq!(dom.params[0], Ty::I64);
        assert_eq!(dom.ret, Ty::I64);
    }

    #[test]
    fn test_tla_const_builtin_helpers_registered() {
        // R27 Option B const_builtin family — 4 helpers.
        // Ensures tir_lower can resolve each emit site at link time.
        for sym in [
            "tla_load_const",
            "tla_cardinality",
            "tla_is_finite_set",
            "tla_tostring",
        ] {
            let h = find_helper(sym)
                .unwrap_or_else(|| panic!("missing RuntimeHelper entry for {sym}"));
            assert_eq!(h.params.len(), 1, "{sym} takes one i64 argument");
            assert_eq!(h.params[0], Ty::I64);
            assert_eq!(h.ret, Ty::I64);
        }
    }

    #[test]
    fn test_tla_tuple_helpers_registered() {
        // R27 Option B tuple family (#4318) — 9 N-arity monomorphs for
        // `<<e_1, …, e_N>>` literals plus `tla_tuple_get` for 1-indexed
        // element access. Total 10 tla_tuple_* entries.
        let tla_tuple_count = RUNTIME_HELPERS
            .iter()
            .filter(|h| h.symbol.starts_with("tla_tuple_"))
            .count();
        assert_eq!(tla_tuple_count, 10, "expected 10 tla_tuple_* helpers");

        // Every tuple_new_N monomorph returns i64 and takes N i64 params.
        for n in 0..=8 {
            let sym = format!("tla_tuple_new_{n}");
            let h = find_helper(&sym)
                .unwrap_or_else(|| panic!("missing RuntimeHelper entry for {sym}"));
            assert_eq!(h.params.len(), n, "{sym} should take {n} params");
            for p in h.params {
                assert_eq!(*p, Ty::I64, "{sym} params must be i64");
            }
            assert_eq!(h.ret, Ty::I64);
        }

        // tla_tuple_get(tup: TlaHandle, idx: i64) -> TlaHandle.
        let get =
            find_helper("tla_tuple_get").expect("missing RuntimeHelper entry for tla_tuple_get");
        assert_eq!(get.params.len(), 2, "tla_tuple_get takes (tup, idx)");
        assert_eq!(get.params[0], Ty::I64);
        assert_eq!(get.params[1], Ty::I64);
        assert_eq!(get.ret, Ty::I64);
    }
}
