#!/usr/bin/env bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# bump_z4_version.sh - Update z4 dependency pin to latest HEAD
#
# Usage:
#   ./scripts/bump_z4_version.sh           # bump to latest HEAD
#   ./scripts/bump_z4_version.sh <commit>  # bump to specific commit

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
Z4_REPO="https://github.com/andrewdyates/z4"
CARGO_TOML="$REPO_ROOT/Cargo.toml"

# Get target commit
if [[ $# -ge 1 ]]; then
    NEW_REV="$1"
    echo "Bumping z4 to specified commit: $NEW_REV"
else
    echo "Fetching latest z4 HEAD..."
    NEW_REV=$(git ls-remote "$Z4_REPO" HEAD | cut -f1)
    if [[ -z "$NEW_REV" ]]; then
        echo "ERROR: Failed to fetch z4 HEAD" >&2
        exit 1
    fi
    echo "Latest z4 commit: $NEW_REV"
fi

if [[ ! "$NEW_REV" =~ ^[0-9a-f]{40}$ ]]; then
    echo "ERROR: expected z4 rev to be a 40-hex git commit, got: $NEW_REV" >&2
    exit 2
fi

if [[ ! -f "$CARGO_TOML" ]]; then
    echo "ERROR: missing $CARGO_TOML" >&2
    exit 1
fi

echo "Updating Cargo.toml (workspace.dependencies)..."
IFS=$'\t' read -r CURRENT_REV ACTION Z4_DEPS_CSV < <(
    python3 - "$CARGO_TOML" "$NEW_REV" <<'PY'
import re
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python 3.11+ in normal use
    import tomli as tomllib

cargo_toml = Path(sys.argv[1])
new_rev = sys.argv[2]
canonical_repo = "https://github.com/andrewdyates/z4"
allowed_repo_ids = set([
    "github.com/andrewdyates/z4",
    "github.com/andrewdyates/z4",
])

text = cargo_toml.read_text(encoding="utf-8")
data = tomllib.loads(text)
workspace_deps = data.get("workspace", dict()).get("dependencies", dict())
if not isinstance(workspace_deps, dict):
    raise SystemExit("ERROR: workspace.dependencies missing from Cargo.toml")

def normalize_repo_identity(url: str) -> str | None:
    base = re.split(r"[?#]", url, maxsplit=1)[0]
    patterns = (
        r"^https://github\.com/([^/]+)/([^/]+?)(?:\.git)?/?$",
        r"^ssh://git@github\.com/([^/]+)/([^/]+?)(?:\.git)?/?$",
        r"^git@github\.com:([^/]+)/([^/]+?)(?:\.git)?/?$",
    )
    for pattern in patterns:
        match = re.match(pattern, base)
        if match:
            owner, repo = match.groups()
            return f"github.com/{owner}/{repo}"
    return None

def is_z4_dep(name: str) -> bool:
    return name == "z4" or name.startswith("z4-")

deps: dict[str, dict[str, str]] = dict()
bad_specs = []
bad_urls = []
invalid_revs = []
needs_url_canonicalization = False
for name, spec in workspace_deps.items():
    if not is_z4_dep(name):
        continue
    if not isinstance(spec, dict):
        bad_specs.append(name)
        continue
    git_url = spec.get("git")
    rev = spec.get("rev")
    if not isinstance(git_url, str):
        bad_specs.append(name)
        continue
    repo_id = normalize_repo_identity(git_url)
    if repo_id not in allowed_repo_ids:
        bad_urls.append(f"{name}={git_url!r}")
    if git_url != canonical_repo:
        needs_url_canonicalization = True
    if not isinstance(rev, str) or re.fullmatch(r"[0-9a-f]{40}", rev) is None:
        invalid_revs.append(f"{name}={rev!r}")
        continue
    deps[name] = dict(git=git_url, rev=rev)

if bad_specs:
    raise SystemExit(f"ERROR: invalid z4 dependency table(s): {', '.join(sorted(bad_specs))}")
if bad_urls:
    raise SystemExit(f"ERROR: unsupported z4 git url(s): {', '.join(sorted(bad_urls))}")
if invalid_revs:
    raise SystemExit(f"ERROR: invalid z4 rev(s): {', '.join(sorted(invalid_revs))}")
if not deps:
    raise SystemExit("ERROR: missing workspace z4 deps in Cargo.toml")

dep_names = ",".join(sorted(deps))
revs = {spec["rev"] for spec in deps.values()}
if len(revs) != 1:
    detail = ", ".join(f"{name}={spec['rev'][:8]}" for name, spec in sorted(deps.items()))
    raise SystemExit(f"ERROR: mismatched z4 revs in Cargo.toml: {detail}")

(current_rev,) = tuple(revs)

if current_rev == new_rev and not needs_url_canonicalization:
    print(f"{current_rev}\tnoop\t{dep_names}")
    raise SystemExit(0)

def rewrite_dep_line(source: str, dep_name: str) -> str:
    line_pat = re.compile(
        rf'^(?P<prefix>{re.escape(dep_name)}\s*=\s*\{{)(?P<body>[^}}]*)(?P<suffix>\}}\s*(?:#.*)?)$',
        re.MULTILINE,
    )

    def repl(match: re.Match[str]) -> str:
        body = match.group("body")
        if re.search(r'\bgit\s*=\s*"[^"]+"', body) is None:
            raise SystemExit(f"ERROR: missing git url for {dep_name} in Cargo.toml")
        if re.search(r'\brev\s*=\s*"[0-9a-f]{40}"', body) is None:
            raise SystemExit(f"ERROR: missing git rev for {dep_name} in Cargo.toml")
        body = re.sub(r'(\bgit\s*=\s*")[^"]+(")', rf'\g<1>{canonical_repo}\2', body, count=1)
        body = re.sub(r'(\brev\s*=\s*")[0-9a-f]{40}(")', rf'\g<1>{new_rev}\2', body, count=1)
        return f"{match.group('prefix')}{body}{match.group('suffix')}"

    updated_text, count = line_pat.subn(repl, source, count=1)
    if count != 1:
        raise SystemExit(f"ERROR: unable to rewrite {dep_name} in Cargo.toml")
    return updated_text

updated = text
for dep_name in sorted(deps):
    updated = rewrite_dep_line(updated, dep_name)
cargo_toml.write_text(updated, encoding="utf-8")
print(f"{current_rev}\tupdated\t{dep_names}")
PY
)

echo "Current z4 pin: $CURRENT_REV"

if [[ "${ACTION:-}" == "noop" ]]; then
    echo "Already at target revision. No changes needed."
    exit 0
fi

# Refresh Cargo.lock
echo "Refreshing Cargo.lock..."
cd "$REPO_ROOT"
rm -f "$REPO_ROOT/Cargo.lock"
IFS=',' read -r -a Z4_DEPS <<< "${Z4_DEPS_CSV:-}"
for dep in "${Z4_DEPS[@]}"; do
    cargo update -p "$dep" --precise "$NEW_REV"
done

echo ""
echo "Done! z4 bumped: $CURRENT_REV -> $NEW_REV"
echo ""
echo "Next steps:"
echo "  1. cargo check -p tla-z4"
echo "  2. cargo test -p tla-z4"
echo "  3. Run z4-related regression tests"
echo "  4. Commit with a message referencing the z4 bump"
