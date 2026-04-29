#!/usr/bin/env bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/compare_tlc.sh SPEC.tla [SPEC.cfg]

Environment:
  TLC_JAR            Path to tla2tools.jar (default: ~/tlaplus/tla2tools.jar)
  COMMUNITY_MODULES  Path to CommunityModules.jar (default: ~/tlaplus/CommunityModules.jar)
  TLA2_BIN           Path to `tla` binary (default: uses `cargo run --profile release-canary -p tla-cli --`)
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

spec=${1:?missing SPEC.tla}
config=${2:-${spec%.tla}.cfg}

if [[ ! -f "$spec" ]]; then
  echo "error: spec not found: $spec" >&2
  exit 2
fi
if [[ ! -f "$config" ]]; then
  echo "error: config not found: $config" >&2
  exit 2
fi

tlc_jar=${TLC_JAR:-"$HOME/tlaplus/tla2tools.jar"}
if [[ ! -f "$tlc_jar" ]]; then
  echo "error: TLC_JAR not found: $tlc_jar" >&2
  exit 2
fi

# Build classpath with CommunityModules if available
community_modules="${COMMUNITY_MODULES:-$HOME/tlaplus/CommunityModules.jar}"
if [[ -f "$community_modules" ]]; then
  TLC_CP="$tlc_jar:$community_modules"
else
  TLC_CP="$tlc_jar"
fi

tlc_meta=$(mktemp -d)
trap 'rm -rf "$tlc_meta"' EXIT

out_dir=${OUT_DIR:-/tmp}
tlc_out=${TLC_OUT:-"$out_dir/tlc_output.txt"}
tla2_out=${TLA2_OUT:-"$out_dir/tla2_output.txt"}

if [[ -n "${TLA2_BIN:-}" ]]; then
  tla2_cmd=("$TLA2_BIN")
else
  tla2_cmd=(cargo run --profile release-canary -p tla-cli --)
fi

echo "=== Running TLC ==="
set +e
java -cp "$TLC_CP" tlc2.TLC \
  -metadir "$tlc_meta" \
  -teSpecOutDir "$tlc_meta" \
  -config "$config" \
  "$spec" 2>&1 | tee "$tlc_out"
tlc_rc=${PIPESTATUS[0]}
set -e

echo
echo "=== Running TLA2 ==="
set +e
"${tla2_cmd[@]}" check "$spec" --config "$config" 2>&1 | tee "$tla2_out"
tla2_rc=${PIPESTATUS[0]}
set -e

echo
echo "=== Summary (best effort grep) ==="
echo "TLC:"
grep -E "states generated|distinct states|States found|State space|Model checking completed" "$tlc_out" || true
echo
echo "TLA2:"
grep -E "states|States|distinct|Model checking|Invariant" "$tla2_out" || true

echo
echo "Full outputs saved:"
echo "  TLC:  $tlc_out"
echo "  TLA2: $tla2_out"

echo
echo "Exit codes:"
echo "  TLC:  $tlc_rc"
echo "  TLA2: $tla2_rc"
exit 0
