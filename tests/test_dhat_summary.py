# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Focused tests for scripts/dhat_summary.py."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))

import dhat_summary


def test_frame_symbol_strips_address_and_source_location() -> None:
    frame = "0x1015c86d0: tla_check::foo::bar (src/foo.rs:12:34)"

    assert dhat_summary.normalize_frame(frame) == "tla_check::foo::bar (src/foo.rs:12:34)", (
        f"expected address prefix to be stripped from {frame!r}"
    )
    assert dhat_summary.frame_symbol(frame) == "tla_check::foo::bar", (
        f"expected symbol-only frame for {frame!r}"
    )


def test_classify_family_prefers_workspace_frame_over_runtime_frames() -> None:
    frames = (
        "0x1: <alloc::alloc::Global as core::alloc::Allocator>::allocate (alloc/src/alloc.rs:1:1)",
        "0x2: alloc::sync::Arc<T>::new (alloc/src/sync.rs:1:1)",
        "0x3: tla_check::binding_chain::BindingChain::cons (src/binding_chain.rs:1:1)",
        "0x4: std::thread::spawn (std/src/thread/mod.rs:1:1)",
    )

    assert dhat_summary.classify_family(frames) == "tla_check::binding_chain::BindingChain::cons", (
        f"expected workspace frame to win for {frames!r}"
    )


def test_summarize_profile_groups_samples_by_family() -> None:
    data = {
        "cmd": "target/worker_1/profiling/tla2 check ...",
        "ftbl": [
            "[root]",
            "0x1: alloc::sync::Arc<T>::new (alloc/src/sync.rs:1:1)",
            "0x2: tla_check::binding_chain::BindingChain::cons (src/binding_chain.rs:10:20)",
            "0x3: tla_value::value::except::apply (src/value.rs:20:30)",
            "0x4: hashbrown::raw::RawTable<T>::reserve (hashbrown/src/raw/mod.rs:1:1)",
        ],
        "pps": [
            {"tbk": 10, "tb": 1000, "fs": [1, 2]},
            {"tbk": 6, "tb": 600, "fs": [1, 2]},
            {"tbk": 9, "tb": 900, "fs": [1, 3]},
            {"tbk": 4, "tb": 400, "fs": [1, 4]},
        ],
    }

    summary = dhat_summary.summarize_profile(data, top=3)

    assert summary.total_blocks == 29, f"expected 29 total blocks, got {summary.total_blocks!r}"
    assert summary.total_bytes == 2900, f"expected 2900 total bytes, got {summary.total_bytes!r}"
    assert summary.total_samples == 4, (
        f"expected 4 summarized program points, got {summary.total_samples!r}"
    )
    assert summary.top_families[0].family == "tla_check::binding_chain::BindingChain::cons", (
        f"expected binding-chain family first, got {summary.top_families!r}"
    )
    assert summary.top_families[0].tbk == 16, (
        f"expected binding-chain family to aggregate 16 blocks, got {summary.top_families[0]!r}"
    )
    assert summary.top_families[1].family == "tla_value::value::except::apply", (
        f"expected value-except family second, got {summary.top_families!r}"
    )
    assert summary.top_families[1].tbk == 9, (
        f"expected value-except family to aggregate 9 blocks, got {summary.top_families[1]!r}"
    )
    assert summary.top_families[2].family == "hashbrown::raw::RawTable<T>::reserve", (
        f"expected fallback external family third, got {summary.top_families!r}"
    )
    assert summary.top_families[2].tbk == 4, (
        f"expected fallback external family to aggregate 4 blocks, got {summary.top_families[2]!r}"
    )


def test_render_summary_includes_trimmed_exemplar_stack() -> None:
    data = {
        "cmd": "target/worker_1/profiling/tla2 check ...",
        "ftbl": [
            "[root]",
            "0x1: alloc::sync::Arc<T>::new (alloc/src/sync.rs:1:1)",
            "0x2: tla_check::binding_chain::BindingChain::cons (src/binding_chain.rs:10:20)",
            "0x3: tla_check::compiled_guard::quantifier (src/guard.rs:20:30)",
            "0x4: tla_check::checker::run (src/checker.rs:30:40)",
        ],
        "pps": [
            {"tbk": 10, "tb": 1000, "fs": [1, 2, 3, 4]},
        ],
    }

    rendered = dhat_summary.render_summary(
        dhat_summary.summarize_profile(data, top=1),
        stack_limit=2,
    )

    assert "Top families by allocation blocks:" in rendered, (
        f"expected family heading in rendered summary, got {rendered!r}"
    )
    assert "tla_check::binding_chain::BindingChain::cons" in rendered, (
        f"expected grouped family in rendered summary, got {rendered!r}"
    )
    assert (
        "stack: tla_check::binding_chain::BindingChain::cons -> tla_check::compiled_guard::quantifier"
        in rendered
    ), f"expected focused exemplar stack in rendered summary, got {rendered!r}"
