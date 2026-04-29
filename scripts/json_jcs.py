# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import hashlib
import json
import math
from typing import Any


def _format_float_jcs(value: float) -> str:
    if not math.isfinite(value):
        raise ValueError(f"non-finite float not allowed in canonical JSON: {value!r}")
    if value == 0.0:
        return "0"

    s = repr(value)
    if "e" in s or "E" in s:
        mantissa, exp = s.lower().split("e", 1)
        sign = ""
        if exp and exp[0] in "+-":
            sign, exp = exp[0], exp[1:]
        exp = exp.lstrip("0") or "0"
        return f"{mantissa}e{sign}{exp}"

    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return s


def _dumps_canonical(value: Any) -> str:
    if value is None:
        return "null"
    if value is True:
        return "true"
    if value is False:
        return "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, float):
        return _format_float_jcs(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
    if isinstance(value, (list, tuple)):
        return "[" + ",".join(_dumps_canonical(v) for v in value) + "]"
    if isinstance(value, dict):
        items: list[tuple[str, Any]] = []
        for k, v in value.items():
            if not isinstance(k, str):
                raise TypeError(f"canonical JSON requires string keys, got {type(k).__name__}")
            items.append((k, v))
        items.sort(key=lambda kv: kv[0])
        return (
            "{"
            + ",".join(
                json.dumps(k, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
                + ":"
                + _dumps_canonical(v)
                for k, v in items
            )
            + "}"
        )
    raise TypeError(f"unsupported type for canonical JSON: {type(value).__name__}")


def sha256_jcs(value: Any) -> str:
    canonical = _dumps_canonical(value).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()

