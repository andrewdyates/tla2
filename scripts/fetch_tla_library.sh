#!/bin/bash
# Copyright 2026 Dropbox.
# Licensed under the Apache License, Version 2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Fetch TLA+ library modules required for running all specs.
# Run this after cloning the repo to ensure all dependencies are available.

set -eo pipefail

LIB_DIR="test_specs/tla_library"
mkdir -p "$LIB_DIR"

echo "Fetching TLA+ library modules..."

# TLAPM modules (theorem proving support)
TLAPM_BASE="https://raw.githubusercontent.com/tlaplus/tlapm/main/library"
TLAPM_MODULES=(
    "FiniteSetTheorems.tla"
    "NaturalsInduction.tla"
    "WellFoundedInduction.tla"
    "FunctionsFork.tla"
    "SequenceTheorems.tla"
    "TLAPS.tla"
)

for mod in "${TLAPM_MODULES[@]}"; do
    if [ ! -f "$LIB_DIR/$mod" ]; then
        echo "  Downloading $mod from TLAPM..."
        curl -sL "$TLAPM_BASE/$mod" -o "$LIB_DIR/$mod"
    else
        echo "  $mod already exists"
    fi
done

# Apalache module (for Einstein and other Apalache-compatible specs)
APALACHE_URL="https://raw.githubusercontent.com/informalsystems/apalache/main/src/tla/Apalache.tla"
if [ ! -f "$LIB_DIR/Apalache.tla" ]; then
    echo "  Downloading Apalache.tla..."
    curl -sL "$APALACHE_URL" -o "$LIB_DIR/Apalache.tla"
else
    echo "  Apalache.tla already exists"
fi

echo ""
echo "Done. Library modules available in $LIB_DIR"
echo ""
echo "To use with TLA2:"
echo "  TLA_PATH=$LIB_DIR cargo run --bin tla2 -- check spec.tla"
echo ""
echo "To use with TLC:"
echo "  Copy needed modules to spec directory, or use -DTLA-Library flag"
