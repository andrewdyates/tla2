# Manager Issue Health Audit

**Date:** 2026-01-19
**Role:** MANAGER
**Focus:** Issue Health

## Summary

Discovered **#293 was falsely closed** - the parallel execution hang fix was never implemented. Reopened with evidence. Also identified **#344** as a separate new P0 blocking parallel execution.

## P0 Status (3 open)

| Issue | Description | Status |
|-------|-------------|--------|
| #344 | LET/local_ops context propagation | NEW - blocks parallel |
| #343 | MCCheckpointCoordination 20x slower | Blocked by #344, #293 |
| #293 | Parallel hang (termination race) | REOPENED - CAS fix missing |

## Key Findings

### #293 False Closure

The issue was closed but the fix was never implemented. Evidence:
- `parallel.rs:1787-1794` still contains the buggy non-atomic code
- No `compare_exchange_weak` in flush_work_delta
- MCYoYoPruning: single worker passes (102 states), parallel fails

### Two Separate Parallel Bugs

1. **#344**: Context propagation bug
   - Causes immediate "Undefined operator" errors
   - 100% reproduction rate
   - Root cause: LET inlining returns new context, EXISTS lifting uses old

2. **#293**: Termination detection race
   - Causes hangs (~50% rate with 3+ workers)
   - Root cause: Non-atomic underflow handling in flush_work_delta
   - Fix documented in design doc but never implemented

### Dependency Chain

```
#344 (context bug) ─┬─► Fix parallel execution
#293 (hang bug) ────┘
                      │
                      ▼
#343 (performance) ──► Can then test symmetry optimization
```

## Test Health

- Unit tests: **954 passed, 0 failed, 1 ignored**
- Spec coverage: 176 total, 12 explicitly skipped
- diagnose_specs.py: stuck on MCBoulanger (6M states, 60s timeout insufficient)

## Thrashing Check

- #293: 2 close/reopen events (legitimate - was falsely closed)
- No other thrashing detected

## Stuck Issues (5+ refs)

| Issue | Refs | Assessment |
|-------|------|------------|
| #334 | 42 | Expected (tracking issue) |
| #293 | 27 | P0, reopened |
| #343 | 18 | P0, blocked |

## Actions Taken

1. Reopened #293 with evidence
2. Updated #343 with two-bug dependency
3. Clarified #293 vs #344 distinction

## Next

Worker should prioritize:
1. #344 (immediate crash) → enables parallel testing
2. #293 (probabilistic hang) → ensures reliable completion
3. Then #343 (performance) → assess actual gap
