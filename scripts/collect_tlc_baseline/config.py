# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Shared constants and path definitions for baseline collection."""

import sys
from pathlib import Path

# Ordered keys for deterministic JSON output
STATS_KEY_ORDER = (
    "tlc_pass",
    "tlc_error",
    "tlc_timeout",
    "tla2_match",
    "tla2_mismatch",
    "tla2_fail",
    "tla2_untested",
)
CATEGORIES_KEY_ORDER = ("small", "medium", "large", "xlarge", "skip", "unknown")
TLC_ENTRY_KEY_ORDER = ("status", "states", "runtime_seconds", "error_type", "error")
TLA2_ENTRY_KEY_ORDER = ("status", "states", "error_type", "last_run", "git_commit")
SPEC_ENTRY_KEY_ORDER = (
    "tlc",
    "tla2",
    "verified_match",
    "issue",
    "category",
    "source",
)

EXAMPLES_DIR = Path.home() / "tlaplus-examples" / "specifications"
TLA2TOOLS = Path.home() / "tlaplus" / "tla2tools.jar"
COMMUNITY_MODULES = Path.home() / "tlaplus" / "CommunityModules.jar"
TLAPLUS_DIR = Path.home() / "tlaplus"
EXAMPLES_BASE_DIR = Path.home() / "tlaplus-examples"
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
OUTPUT_FILE = PROJECT_ROOT / "tests" / "tlc_comparison" / "spec_baseline.json"
EXPECTED_RESULTS = PROJECT_ROOT / "tests" / "tlc_comparison" / "expected_results.json"

# Extended timeout for baseline collection
TIMEOUT = 600  # 10 minutes

# Schema version for provenance tracking
SCHEMA_VERSION = 3

# Import ALL_SPECS from spec_catalog
sys.path.insert(0, str(PROJECT_ROOT / "tests" / "tlc_comparison"))
from spec_catalog import ALL_SPECS  # noqa: E402

__all__ = [
    "STATS_KEY_ORDER",
    "CATEGORIES_KEY_ORDER",
    "TLC_ENTRY_KEY_ORDER",
    "TLA2_ENTRY_KEY_ORDER",
    "SPEC_ENTRY_KEY_ORDER",
    "EXAMPLES_DIR",
    "TLA2TOOLS",
    "COMMUNITY_MODULES",
    "TLAPLUS_DIR",
    "EXAMPLES_BASE_DIR",
    "PROJECT_ROOT",
    "OUTPUT_FILE",
    "EXPECTED_RESULTS",
    "TIMEOUT",
    "SCHEMA_VERSION",
    "ALL_SPECS",
]
