# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

import check_current_doc_routing


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def test_check_guard_content_normalizes_whitespace() -> None:
    guard = check_current_doc_routing.DocTextGuard(
        path="ignored.md",
        required_substrings=("foo bar baz",),
        forbidden_patterns=(r"forbidden phrase",),
    )

    failures = check_current_doc_routing.check_guard_content(
        "foo\n bar\tbaz\nsafe text\n",
        guard,
    )

    assert failures == [], f"Expected normalized content to satisfy guard, got {failures!r}"


def test_current_doc_routing_guards() -> None:
    failures = check_current_doc_routing.check_doc_text_guards(_repo_root())
    assert not failures, "\n".join(failures)
