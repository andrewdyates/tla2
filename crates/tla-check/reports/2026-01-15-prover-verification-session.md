# Prover Verification Session

**Date:** 2026-01-15
**Author:** PROVER
**Related Issues:** #131, #135, #126

## Summary

Verification session focusing on EXISTS/ArrayState performance gap analysis and formal verification status.

## Verified Findings

### 1. Performance Gap Root Cause (#131)

**Verified Claim:** MCBakery N=3 benchmark times out (>9 min vs TLC 65s).

**Root Cause Identified:** The EXISTS handler at line 3615 works correctly, but:
1. EXISTS body `p(self)` is an `Apply` expression (operator call)
2. `enumerate_next_rec_array` does NOT handle `Apply` - falls back at line 3748
3. Every domain value triggers State-based fallback

```
EXISTS (array): var=self, domain_size=2
EXISTS (array): fallback for one domain value, using State-based path  ← EVERY value
```

**Fix Required:** Add `Expr::Apply` handler to `enumerate_next_rec_array`:
- Inline the operator body (get definition, substitute args)
- Recurse into the inlined body
- This would allow EXISTS to reach the OR partial fallback inside p(self)

### 2. Test Coverage Verification

| Module | Tests | Status |
|--------|-------|--------|
| tla-check | 931 | PASS |
| Bug #174 (closure capture) | 1 regression test | PASS |
| Bug #175 (bind/unbind mode) | 4 tests | PASS |

### 3. Formal Verification Status (#135)

**Kani Infrastructure:** OPERATIONAL

```bash
cargo kani --harness verify_bool_fingerprint_deterministic
# VERIFICATION:- SUCCESSFUL (29156 checks, 0 failures)
```

**Available Harnesses:** 30+ proofs covering:
- Value fingerprint determinism
- Equality reflexivity/symmetry
- State fingerprint consistency
- Type discrimination

## Recommendations

1. **P1:** Implement `Expr::Apply` handler in `enumerate_next_rec_array` to close MCBakery performance gap
2. **P2:** Continue expanding kani proofs per designs/2026-01-14-formal-verification-strategy.md

## Issue Updates

- Commented on #131 with Apply fallback root cause
