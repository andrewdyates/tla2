<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
# TLA2 Next Steps (2026-04-02)

## Current State

- **160/160 TLC parity** (100%) + 23/24 xlarge specs
- **Apalache parity** complete — all 13 gaps closed
- **CDEMC** (cooperative BFS + symbolic) is the default checking strategy
- **Bytecode VM** default ON with interpreter fallback
- **JIT** (Cranelift) wired into BFS hot paths but 0% dispatch hit rate on next-state
- **AIGER/BTOR2** hardware model checking frontends complete (594/594 + 330/330 parse)
- **35 open issues** across 4 epics

## Active Epics

### 1. HN Launch (#3951, P0)
Ship TLA2 as a public release. The README, CDEMC demo, and benchmark report are done.
Remaining:
- [ ] Package codegen demo: examples/mutex-monitor end-to-end (#3952)
- [ ] CDEMC demo with BFS-impossible state space where PDR wins (#3957)
- [ ] Get "faster than TLC" benchmark numbers on 3+ specs (#3955)

### 2. JIT & Compilation (#3933/#3904, P1)
Close the 2-8x sequential performance gap vs TLC.
Current blocker: **JIT dispatch 0% hit rate for next-state evaluation.**
- [ ] Fix action next-state JIT dispatch pipeline (#3958)
- [ ] Wire TierManager into BFS loop (#3910)
- [ ] Codegen parity: INSTANCE + RECURSIVE (#3911)
- [ ] Re-benchmark after JIT dispatch fix (#3946)
- [ ] Call opcode support for real invariants (#3948)

### 3. HWMCC'26 (#3940, P0)
SAT-based IC3/PDR engine for bit-level hardware verification.
Four phases:
- [ ] Phase 1: SAT foundation — cnf.rs, transys.rs (#3941)
- [ ] Phase 2: Core IC3/PDR algorithm (#3942)
- [ ] Phase 3: BMC + k-induction portfolio (#3943)
- [ ] Phase 4: Beat supercar 330/330 (#3944)

### 4. Supremacy Plan (#3775, P0)
10-pillar plan to be strictly superior to TLC and Apalache.
Key remaining dimensions:
- Performance (JIT, see epic 2)
- GPU fingerprinting (#3956)
- Proofs (lean4 certificates — not started)
- Production runtime guards (not started)

## Priority Order

1. **JIT dispatch fix** — This is the highest-leverage work. Fixing the 0% hit rate turns the JIT from a net negative into the path to TLC parity.
2. **HN launch polish** — Codegen demo + BFS-impossible CDEMC demo.
3. **HWMCC IC3 Phase 1-2** — SAT foundation enables competition entry.
4. **MCNanoMedium algorithm investigation** — 10x slower than TLC with 530K states suggests an algorithm bug, not interpreter overhead.

## Blocked Issues

- #3893: EXISTS ctx.clone() — mark/restore unsound with LET
- #3894: Guard redundancy — canary failures

## Key Findings from JIT Benchmark (2026-04-02)

The benchmark revealed the JIT is currently a **net negative** (3.0x vs TLC with JIT, 2.5x without). Root cause: compiled native code exists but the dispatch pipeline never routes to it for next-state evaluation. Compiled action artifacts existed, but dispatch still reported `not_compiled=1,519,619` calls.

Fixing this single issue would make the JIT path viable. The compiled code exists — it's just not being called.

## Performance Quick Wins

From the CPU profile (MCLamportMutex, 1 worker):
- `eval_dispatch` (6.1%) + `eval_ident` (2.9%) + `binding_chain::resolve` (1.7%) = 10.7% — eliminated by JIT
- `_tlv_get_addr` (2.2%) — reduce TLS accesses (~25 thread_locals in eval path)
- `has_lazy_state_value` (0.9%) — skip when spec has no lazy-producing operators
