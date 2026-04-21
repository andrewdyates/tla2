<!--
Author: Andrew Yates <andrewyates.name@gmail.com>
-->

# TLC comparison tests

This directory contains pytest-based integration tests that compare `tla2` against the Java TLC
baseline.

The baseline is generated with CommunityModules.jar on the classpath, enabling specs that depend
on IOUtils, CSV, TLCExt, etc. Provenance is tracked in `spec_baseline.json` (see #1012).

## Running

These tests use `pytest`. Run them from the repo root:

```bash
python -m pytest -q tests/tlc_comparison/test_init_eval_error_1004.py
```

## Artifacts (failure logs)

To save full stdout/stderr logs for each TLC/TLA2 run, set:

`TLA2_TLC_COMPARISON_ARTIFACTS_DIR=<path>`

`<path>` may be absolute or repo-relative. When set, failing assertions should include a `Log: ...`
path pointing at the captured output file.

## Puzzle Specs (Expected Invariant Violations)

Some specs are designed to find solutions by checking for invariant violations. These include:

- DieHard, MCDieHarder - Find 4 gallons solution
- MissionariesAndCannibals - Find safe crossing
- SlidingPuzzles, tower_of_hanoi_M1 - Find winning sequence

For these specs, both TLC and TLA2 correctly report `error_type=invariant`. This is expected behavior,
not a bug. The `verified_match` field in `spec_baseline.json` confirms both tools satisfy the same
baseline contract: matching error classification and, where directly comparable, matching state
counts.

## Simulation-mode specs

Some specs only run under `simulate` rather than ordinary state-space checking. For these entries,
`verified_match: true` means both TLC and TLA2 completed the simulation-mode run successfully under
the recorded execution mode. State-count parity is not required for these specs because the
simulation contract is completion-based rather than BFS-state-comparison-based.

## Execution Mode: continue-on-error vs first-error

`tla2 diagnose` defaults to running each spec with `--continue-on-error`, which explores the full
state space even after finding an error. However, some TLC baselines were collected at first-error
(without TLC's `-continue` flag), so the state counts reflect only the states explored up to the
first invariant violation.

The `continue_on_error` field in `spec_baseline.json` controls this per-spec:

- **`true` (default)**: spec runs with `--continue-on-error`. Omitted from JSON when true.
- **`false`**: spec runs at first-error (no `--continue-on-error`). Must be explicit in JSON.

Currently only `sunder_cargo_lock_with_toctou` uses first-error mode (11,285 states at first
invariant violation vs 10M+ states with continue-on-error).

When adding new baseline entries or refreshing existing ones:

1. Check how the TLC baseline was collected — if TLC was run without `-continue`, set
   `"continue_on_error": false` in the spec's baseline entry.
2. The `--update-baseline` flag preserves existing `continue_on_error` overrides via
   read-modify-write on the raw JSON (implemented in the `baseline_update` module of `tla-cli`).
3. A regression test (`test_sunder_cargo_lock_with_toctou_baseline_has_first_error_mode`)
   asserts the exact set of first-error specs to prevent accidental changes.
