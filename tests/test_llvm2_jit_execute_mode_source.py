# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Source guards for LLVM2 JIT execute-mode setup."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).parent.parent


def _source(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def _assert_guard_before(
    source: str,
    needle: str,
    guard: str,
    *,
    span: int = 420,
) -> None:
    idx = source.index(needle)
    window = source[max(0, idx - span) : idx]
    assert guard in window, (needle, window)


def test_tla_llvm2_exports_execute_mode_wrapper() -> None:
    source = _source("crates/tla-llvm2/src/lib.rs")
    wrapper_start = source.index("pub fn ensure_jit_execute_mode()")
    wrapper = source[wrapper_start : source.index("pub use bfs_level", wrapper_start)]

    assert source.count("pub fn ensure_jit_execute_mode()") == 1
    assert '#[cfg(feature = "native")]' in wrapper
    assert "llvm2_codegen::ensure_jit_execute_mode();" in wrapper


def test_tla_llvm2_bfs_level_calls_enter_execute_mode_before_jit_calls() -> None:
    source = _source("crates/tla-llvm2/src/bfs_level.rs")

    _assert_guard_before(source, "(action.func)(", "crate::ensure_jit_execute_mode();")
    _assert_guard_before(
        source,
        "(self.entrypoint)(&parent_abi, &mut successor_abi)",
        "crate::ensure_jit_execute_mode();",
    )
    _assert_guard_before(
        source,
        "(invariant.func)(&mut call_out, state.as_ptr(), state_len_u32);",
        "crate::ensure_jit_execute_mode();",
    )


def test_tla_llvm2_compiled_liveness_enters_execute_mode() -> None:
    source = _source("crates/tla-llvm2/src/compiled_liveness.rs")

    _assert_guard_before(
        source,
        "f(state_buf.as_ptr(), state_buf.len() as u32)",
        "crate::ensure_jit_execute_mode();",
    )
    _assert_guard_before(
        source,
        "f(\n                    current_buf.as_ptr(),",
        "crate::ensure_jit_execute_mode();",
    )


def test_tla_check_native_dispatch_enters_execute_mode() -> None:
    source = _source("crates/tla-check/src/check/model_checker/llvm2_dispatch.rs")

    _assert_guard_before(
        source,
        "fn_ptr(\n                &mut out,",
        "tla_llvm2::ensure_jit_execute_mode();",
    )
    _assert_guard_before(
        source,
        "fn_ptr(&mut out, state.as_ptr(), state_len);",
        "tla_llvm2::ensure_jit_execute_mode();",
    )
    _assert_guard_before(
        source,
        "action_fn(\n                    &mut out,",
        "tla_llvm2::ensure_jit_execute_mode();",
    )
    _assert_guard_before(
        source,
        "invariant_fn(&mut inv_out, state_out.as_ptr(), state_len_u32);",
        "tla_llvm2::ensure_jit_execute_mode();",
    )
