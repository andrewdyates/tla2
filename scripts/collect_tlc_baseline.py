#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
Collect TLC baseline data for all specs.

Thin shim — all logic lives in collect_tlc_baseline/ package.
"""

from collect_tlc_baseline.cli import main


if __name__ == "__main__":
    raise SystemExit(main())
