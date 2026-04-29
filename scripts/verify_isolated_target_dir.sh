#!/bin/bash
# verify_isolated_target_dir.sh - Verify isolated clones share a single cargo target dir
#
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# This is a safety/perf check for isolated clones (see #934). It verifies that
# two separate clones can run `cargo check` while sharing a single
# `CARGO_TARGET_DIR` under `~/repos/<project>/_target/`.
#
# Usage:
#   ./scripts/verify_isolated_target_dir.sh
#
# Notes:
# - Uses `git clone --shared` to avoid network / extra disk usage.
# - Does not modify the current checkout.
#   serialization behavior matches real looper sessions.

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
project_name="$(basename "$repo_root")"

# If run from inside an existing per-role clone (layout
# ~/repos/<project>/<role>[-<id>]/), use the parent directory name for shared
# dirs like _target and _verify_isolated_target_dir.
if [[ "$repo_root" == "$HOME/repos/"* ]]; then
    rel_path="${repo_root#"$HOME/repos/"}"
    repo_name="${rel_path%%/*}"
    role_dir="${rel_path#*/}"
    if [[ -n "$repo_name" ]] && [[ "$role_dir" =~ ^(worker|prover|researcher|manager)(-[0-9]+)?$ ]]; then
        project_name="$repo_name"
    fi
fi

target_dir="$HOME/repos/$project_name/_target"
work_dir="$HOME/repos/$project_name/_verify_isolated_target_dir"
clone_a="$work_dir/clone-a"
clone_b="$work_dir/clone-b"

echo "[verify_isolated_target_dir] repo_root=$repo_root" >&2
echo "[verify_isolated_target_dir] work_dir=$work_dir" >&2
echo "[verify_isolated_target_dir] target_dir=$target_dir" >&2

echo "[verify_isolated_target_dir] spawn_session.sh --dry-run sanity..." >&2
    echo "[verify_isolated_target_dir] ERROR: spawn_session.sh did not set expected CARGO_TARGET_DIR" >&2
    exit 1
fi

rm -rf "$work_dir"
mkdir -p "$work_dir"
mkdir -p "$target_dir"

echo "[verify_isolated_target_dir] cloning (shared)..." >&2
git clone --shared "$repo_root" "$clone_a" >/dev/null
git clone --shared "$repo_root" "$clone_b" >/dev/null

export CARGO_TARGET_DIR="$target_dir"

echo "[verify_isolated_target_dir] cargo check (clone-a)..." >&2

echo "[verify_isolated_target_dir] cargo check (clone-b)..." >&2

if [[ -d "$clone_a/target" || -d "$clone_b/target" ]]; then
    echo "[verify_isolated_target_dir] ERROR: per-clone target/ exists; expected shared CARGO_TARGET_DIR only" >&2
    echo "[verify_isolated_target_dir] clone_a_target_exists=$([[ -d "$clone_a/target" ]] && echo yes || echo no)" >&2
    echo "[verify_isolated_target_dir] clone_b_target_exists=$([[ -d "$clone_b/target" ]] && echo yes || echo no)" >&2
    exit 1
fi

echo "[verify_isolated_target_dir] OK: cargo artifacts stored in $target_dir" >&2
