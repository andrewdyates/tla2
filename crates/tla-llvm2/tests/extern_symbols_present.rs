// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the extern symbol map used by JIT linking.
//!
//! These tests walk the table returned by [`extern_symbol_map_for_tests`]
//! and assert that every `tla_*` runtime helper declared in
//! [`RUNTIME_HELPERS`] has a non-null address entry. On macOS, we also
//! validate that the underscored Mach-O alias resolves to the same
//! function pointer as the bare C-ABI name.
//!
//! Part of #4318 (R27 Option B handle-based runtime ABI).
//!
//! NOTE: The `jit_*` family is NOT covered here. Those are registered by
//! a separate code path tracked in #4314 (still open at time of writing).
//! If both registrations land, this file should grow a parallel
//! assertion for the `jit_*` half — see `register_jit_symbols`.

#![cfg(feature = "native")]

use tla_llvm2::{extern_symbol_map_for_tests, lower_tir_to_llvm_ir, RUNTIME_HELPERS};
use tla_tir::bytecode::{BytecodeFunction, Opcode};

/// Every `tla_*` (or `clear_tla_arena`) helper in `RUNTIME_HELPERS` must
/// have a non-null function pointer in the extern symbol map.
#[test]
fn extern_symbol_map_covers_every_tla_ops_helper() {
    let map = extern_symbol_map_for_tests();
    let tla_helpers: Vec<&str> = RUNTIME_HELPERS
        .iter()
        .map(|h| h.symbol)
        .filter(|s| s.starts_with("tla_") || *s == "clear_tla_arena")
        .collect();

    assert!(
        !tla_helpers.is_empty(),
        "no tla_* helpers registered — RUNTIME_HELPERS regressed"
    );

    for sym in &tla_helpers {
        let addr = map
            .get(*sym)
            .unwrap_or_else(|| panic!("missing extern symbol: {sym}"));
        assert!(!addr.is_null(), "extern symbol {sym} has null address");
    }
}

/// The map must include the full `tla_set_*` surface: 9 `tla_set_enum_N`
/// monomorphs plus 9 other helpers. Catches drift between the helper
/// source files and the extern registration.
#[test]
fn extern_symbol_map_contains_full_tla_set_surface() {
    let map = extern_symbol_map_for_tests();
    let expected = [
        "tla_set_enum_0",
        "tla_set_enum_1",
        "tla_set_enum_2",
        "tla_set_enum_3",
        "tla_set_enum_4",
        "tla_set_enum_5",
        "tla_set_enum_6",
        "tla_set_enum_7",
        "tla_set_enum_8",
        "tla_set_in",
        "tla_set_union",
        "tla_set_intersect",
        "tla_set_diff",
        "tla_set_subseteq",
        "tla_set_powerset",
        "tla_set_big_union",
        "tla_set_range",
        "tla_set_ksubset",
    ];
    for sym in &expected {
        assert!(
            map.contains_key(*sym),
            "extern symbol {sym} missing from extern_symbol_map"
        );
    }
}

/// On macOS, every bare C-ABI name must also be registered under its
/// underscored Mach-O alias pointing at the same function pointer.
#[cfg(target_os = "macos")]
#[test]
fn extern_symbol_map_contains_macho_underscored_aliases() {
    let map = extern_symbol_map_for_tests();
    let tla_helpers: Vec<&str> = RUNTIME_HELPERS
        .iter()
        .map(|h| h.symbol)
        .filter(|s| s.starts_with("tla_") || *s == "clear_tla_arena")
        .collect();

    for sym in &tla_helpers {
        let bare = map
            .get(*sym)
            .unwrap_or_else(|| panic!("missing bare symbol: {sym}"));
        let underscored_name = format!("_{sym}");
        let underscored = map
            .get(&underscored_name)
            .unwrap_or_else(|| panic!("missing underscored symbol: {underscored_name}"));
        assert_eq!(
            *bare as usize, *underscored as usize,
            "macho alias {underscored_name} points to different function than {sym}"
        );
    }
}

/// End-to-end audit: every `@tla_*` symbol declared by the tir_lower
/// IR emitter for a non-trivial function must resolve via the extern map.
///
/// Part of #4318 Step 6 (Option B unused-symbol audit guard). Complements
/// the `extern_symbol_map_*` tests above by walking the *actual* IR text
/// produced by `lower_tir_to_llvm_ir` instead of the runtime helper table,
/// which catches drift where tir_lower invents a `@tla_*` name that no
/// registration covers (e.g. a typo in the emit-site format string, or a
/// helper renamed in runtime.rs but not in tmir_lower.rs).
///
/// The test function exercises multiple Option B helper families so one
/// regression in any of them surfaces as a dedicated failure:
///
/// - `tla_set_enum_N` / `tla_set_union` / `tla_set_in` (set ABI)
///
/// If `tmir_lower` adds a new helper emit site (say, `@tla_foo_bar`) and
/// forgets to register it in `register_tla_ops_symbols`, this test flags
/// the drift at its root. In debug builds the `debug_assert_tla_symbols_resolve`
/// guard inside `lower_tir_to_llvm_ir` will already have panicked — this
/// test provides a second safety net that runs in release profile too.
#[test]
fn test_tir_lower_declares_match_extern_map() {
    // Build a small function that exercises several Option B helper
    // emit sites. The function does not need to be executable — we only
    // inspect the textual IR.
    let mut func = BytecodeFunction::new("audit_harness".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::LoadImm { rd: 2, value: 3 });
    // tla_set_enum_3
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 0,
        count: 3,
    });
    // tla_set_enum_2
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 0,
        count: 2,
    });
    // tla_set_union
    func.emit(Opcode::SetUnion { rd: 5, r1: 3, r2: 4 });
    // tla_set_in
    func.emit(Opcode::SetIn {
        rd: 6,
        elem: 0,
        set: 5,
    });
    func.emit(Opcode::Ret { rs: 5 });

    let result =
        lower_tir_to_llvm_ir(&func, "audit_harness_test").expect("audit_harness should lower");
    let ir = &result.llvm_ir;

    // Mirror of `compile::audit_declared_tla_symbols` — replicated here
    // because the helper is `pub(crate)` to keep the public surface
    // narrow. The scan is intentionally small.
    let map = extern_symbol_map_for_tests();
    let mut missing: Vec<String> = Vec::new();
    for line in ir.lines() {
        let trimmed = line.trim_start();
        if !trimmed.starts_with("declare ") {
            continue;
        }
        let Some(at_pos) = trimmed.find("@tla_") else {
            continue;
        };
        let after_at = &trimmed[at_pos + 1..];
        let end = after_at
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(after_at.len());
        let symbol = &after_at[..end];
        if !map.contains_key(symbol) {
            missing.push(symbol.to_string());
        }
    }
    missing.sort();
    missing.dedup();

    assert!(
        missing.is_empty(),
        "tir_lower declared `@tla_*` symbols not in extern map: {missing:?}\n\n\
         Register them in `register_tla_ops_symbols` (compile.rs) and\n\
         `RUNTIME_HELPERS` (runtime.rs). Emitted IR:\n{ir}"
    );

    // Positive check: we actually exercised Option B helpers. This guards
    // against a future refactor that accidentally stops emitting @tla_*
    // calls and so renders the audit vacuous.
    assert!(
        ir.contains("@tla_set_enum_3"),
        "expected @tla_set_enum_3 declaration in IR:\n{ir}"
    );
    assert!(
        ir.contains("@tla_set_union"),
        "expected @tla_set_union declaration in IR:\n{ir}"
    );
}

/// Sanity check: the map size equals `(linux count) + (macos aliases)`.
#[test]
fn extern_symbol_map_size_matches_runtime_helpers() {
    let map = extern_symbol_map_for_tests();
    // Count all tla_ops-registered helpers: `tla_*` plus the two
    // `clear_tla_*` lifecycle entries registered alongside them in
    // `register_tla_ops_symbols`.
    let tla_helper_count = RUNTIME_HELPERS
        .iter()
        .filter(|h| {
            h.symbol.starts_with("tla_")
                || h.symbol == "clear_tla_arena"
                || h.symbol == "clear_tla_iter_arena"
        })
        .count();

    #[cfg(target_os = "macos")]
    let expected = tla_helper_count * 2;
    #[cfg(not(target_os = "macos"))]
    let expected = tla_helper_count;

    // Filter the map down to only tla_ops-owned entries (bare + Mach-O
    // underscored aliases) to avoid coupling to the `jit_*` registration.
    let present: usize = map
        .keys()
        .filter(|k| {
            k.starts_with("tla_")
                || k.starts_with("_tla_")
                || *k == "clear_tla_arena"
                || *k == "_clear_tla_arena"
                || *k == "clear_tla_iter_arena"
                || *k == "_clear_tla_iter_arena"
        })
        .count();
    assert_eq!(
        present, expected,
        "extern symbol map has {present} tla_* entries but expected {expected}"
    );
}
