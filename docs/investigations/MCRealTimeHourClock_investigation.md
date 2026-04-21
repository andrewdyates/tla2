# MCRealTimeHourClock Investigation Notes

**Date:** 2026-01-08
**Issue:** #14
**Status:** Investigation in progress

## Problem Summary

TLA2 finds only 72 states while TLC finds 216 states for MCRealTimeHourClock spec.
TLC also detects a liveness violation that TLA2 misses.

## Key Observations

1. **Initial states match**: Both TLA2 and TLC find 72 initial states
2. **Successor exploration differs**: TLC explores and finds 144 more states; TLA2 doesn't

## Spec Analysis

The spec uses `[A]_v` stuttering patterns:
```
BigNext == /\ [NowNext]_now
           /\ [HCnxt]_hr
           /\ TNext
           /\ HCnxt => t >= SecondsPerHour - Rho
           /\ t' <= SecondsPerHour + Rho
```

Where `TNext == t' = IF HCnxt THEN 0 ELSE t+(now'-now)`

## Root Cause Analysis

The issue is that TNext's IF condition uses `HCnxt`, which is an action predicate (`hr' = ...`):
- To compute `t'`, we need to know if `HCnxt` is true
- `HCnxt` depends on what `hr'` is
- `hr'` is determined by which branch of `[HCnxt]_hr` we take

## Testing Notes

- Simple `[A]_x /\ [B]_y` patterns work correctly (test_tiny: TLA2=9, TLC=9)
- `IF Action THEN ... ELSE ...` with action predicate conditions also works (test_if_action2: TLA2=15, TLC=15)
- The bug is specific to the MCRealTimeHourClock pattern with the constraint `HCnxt => t >= 1`

## Reproduction

Created minimal reproduction `/tmp/test_stub.tla`:
- TLC: 252 states from 72 initial
- TLA2: 72 states (348 transitions but all to known states)

The fact that TLA2 finds 348 transitions suggests successor enumeration IS happening,
but successors are being fingerprinted as identical to initial states. This may indicate
`t` is not being properly updated in the successor state.

## Update (2026-01-08, Iteration 7)

### Related Fix: JSON Output Variable Collection

Fixed a separate cosmetic bug: JSON output was not collecting variables from extended modules.
The CLI now correctly shows `["hr", "now", "t"]` in the JSON output's `specification.variables` field.
(File: crates/tla-cli/src/main.rs)

### Confirmed: Variables ARE Collected Correctly

Added debug output to check.rs and confirmed:
- Model checker correctly collects all 3 variables: `hr` (from HourClock), `now`, `t`
- The `unqualified_modules` set correctly includes "HourClock"
- Extended module loading and variable collection are working

### Remaining Issue: State Enumeration

The core state enumeration bug remains:
- TLA2 finds 72 states (= TLC's initial states)
- TLC finds 216 total distinct states
- TLA2 reports 348 transitions but all lead to existing states

The `IF HCnxt THEN 0 ELSE t+(now'-now)` pattern creates a dependency:
1. Computing `t'` requires knowing if `HCnxt` is true
2. `HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1` contains primed variables
3. TLA2 must enumerate both branches of `[HCnxt]_hr` (action vs unchanged)
4. Then evaluate the IF condition with the appropriate `hr'` value for each case

Hypothesis: The enumeration algorithm evaluates `IF HCnxt THEN ...` before `hr'` is bound,
resulting in incorrect successor state computation (all successors have same `t'` value).

## Next Steps

1. Debug `enumerate_next_rec_inner` for the specific BigNext pattern
2. Check how `[HCnxt]_hr` (which becomes `HCnxt \/ UNCHANGED hr`) interacts with `IF HCnxt`
3. The fix likely requires ensuring primed variables from `[A]_v` patterns are bound before
   evaluating IF conditions that reference action predicates
