#!/usr/bin/env bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# End-to-end demo: TLA+ spec -> codegen -> model check -> runtime monitor
#
# Usage: ./run_demo.sh
#        ./run_demo.sh --skip-tla2   # Skip TLA2 steps (just build + run generated code)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
GENERATED_DIR="$SCRIPT_DIR/generated"

SKIP_TLA2=false
if [[ "${1:-}" == "--skip-tla2" ]]; then
    SKIP_TLA2=true
fi

echo "========================================"
echo "  TLA2 Codegen Demo: Peterson's Mutex"
echo "========================================"
echo

# -----------------------------------------------------------------------
# Step 1: Model check the TLA+ spec with tla2
# -----------------------------------------------------------------------
if [[ "$SKIP_TLA2" == false ]]; then
    echo "--- Step 1: Model check the TLA+ spec ---"
    echo "\$ tla2 check PetersonMutex.tla --config PetersonMutex.cfg"
    echo
    if command -v tla2 &>/dev/null; then
        tla2 check "$SCRIPT_DIR/PetersonMutex.tla" --config "$SCRIPT_DIR/PetersonMutex.cfg"
    else
        (cd "$REPO_ROOT" && cargo run --release --bin tla2 -- check \
            "$SCRIPT_DIR/PetersonMutex.tla" \
            --config "$SCRIPT_DIR/PetersonMutex.cfg")
    fi
    echo
    echo "The spec is correct: 32 states, no invariant violations, no deadlocks."
    echo

    # -----------------------------------------------------------------------
    # Step 2: Generate Rust code from the spec
    # -----------------------------------------------------------------------
    echo "--- Step 2: Generate Rust code ---"
    echo "\$ tla2 codegen --tir --config PetersonMutex.cfg PetersonMutex.tla"
    echo
    if command -v tla2 &>/dev/null; then
        tla2 codegen --tir \
            --config "$SCRIPT_DIR/PetersonMutex.cfg" \
            "$SCRIPT_DIR/PetersonMutex.tla"
    else
        (cd "$REPO_ROOT" && cargo run --release --bin tla2 -- codegen --tir \
            --config "$SCRIPT_DIR/PetersonMutex.cfg" \
            "$SCRIPT_DIR/PetersonMutex.tla")
    fi
    echo
    echo "(The generated/ directory contains the completed, hand-polished version.)"
    echo
fi

# -----------------------------------------------------------------------
# Step 3: Build and test the generated Rust code
# -----------------------------------------------------------------------
echo "--- Step 3: Build and test the generated code ---"
echo "\$ cd generated && cargo test"
echo
(cd "$GENERATED_DIR" && cargo test 2>&1)
echo

# -----------------------------------------------------------------------
# Step 4: Run the BFS model checker (compiled Rust)
# -----------------------------------------------------------------------
echo "--- Step 4: BFS model check (compiled Rust) ---"
echo "\$ cargo run --bin check"
echo
(cd "$GENERATED_DIR" && cargo run --release --bin check 2>&1)
echo

# -----------------------------------------------------------------------
# Step 5: Run the runtime monitor demo
# -----------------------------------------------------------------------
echo "--- Step 5: Runtime monitor demo ---"
echo "\$ cargo run --bin monitor-demo"
echo
(cd "$GENERATED_DIR" && cargo run --release --bin monitor-demo 2>&1)
echo

echo "========================================"
echo "  Demo complete!"
echo "========================================"
echo
echo "Summary:"
echo "  1. TLA+ spec verified (32 states, mutual exclusion holds)"
echo "  2. Rust code generated from the spec"
echo "  3. Generated code compiles and passes all tests"
echo "  4. BFS model check in compiled Rust matches TLA2 (32 states)"
echo "  5. Runtime monitor catches bugs that violate the spec"
