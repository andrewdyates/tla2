#!/usr/bin/env bash
# Copyright 2026 Dropbox
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# Part of #4372. Runs the bounded MCL-sized native fused BFS canary.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-240}"

if [[ -n "${TIMEOUT_BIN:-}" ]]; then
    timeout_bin="$TIMEOUT_BIN"
elif [[ -x /opt/homebrew/bin/timeout ]]; then
    timeout_bin=/opt/homebrew/bin/timeout
elif command -v timeout >/dev/null 2>&1; then
    timeout_bin="$(command -v timeout)"
else
    echo "error: set TIMEOUT_BIN or install timeout" >&2
    exit 2
fi

cd "$ROOT"
exec env CARGO_NET_GIT_FETCH_WITH_CLI="${CARGO_NET_GIT_FETCH_WITH_CLI:-true}" \
    "$timeout_bin" "$TIMEOUT_SECONDS" \
    --example native_bfs_mcl_canary -- "$@"
