# CDEMC Demo: Cooperative Decision-Enhanced Model Checking

## What is CDEMC?

Traditional model checkers use a single strategy: either **explicit-state BFS** (enumerate every reachable state) or **symbolic reasoning** (prove properties via SAT/SMT).  Each has fundamental limitations:

- **BFS** is complete but exhaustive. A spec with N processes has O(4^N) states. At N=12, that's ~17 million states. At N=20, it's a trillion.
- **Symbolic engines** (BMC, PDR, k-induction) reason about *all states at once* using constraint solvers, but they can fail on complex specs or produce false results without cross-validation.

**CDEMC fuses four verification engines into a single cooperative system.** They run in parallel, share information at runtime, and the first to reach a definitive answer wins:

```
  ┌─────────┐  frontier samples  ┌─────────┐
  │  Lane 1 │ ─────────────────> │  Lane 2 │
  │   BFS   │                    │   BMC   │
  └────┬────┘                    └─────────┘
       │         ┌─────────┐
       │<───────│  Lane 3 │  proved invariants
                │   PDR   │
                └─────────┘
                 ┌─────────┐
                 │  Lane 4 │  inductive proofs
                 │  k-Ind  │
                 └─────────┘
```

The cooperation is bidirectional:
- **BFS → BMC**: BFS sends concrete frontier states to seed symbolic exploration, letting BMC start from realistic states deep in the search tree instead of only from Init.
- **PDR → BFS**: When PDR proves an invariant symbolically, BFS skips checking it on every state — a significant speedup for multi-invariant specs.
- **k-Induction**: Attempts to prove safety via bounded inductive arguments. If the invariant is k-inductive (holds for k steps implies it holds for k+1), k-induction proves it for *all* reachable states without enumeration.
- **Oracle routing**: An adaptive oracle monitors each action's branching factor at runtime and routes high-branching actions to the symbolic engine while keeping low-branching actions in BFS. The oracle self-tunes via Thompson sampling.

## The Demo Spec: Token-Ring Mutual Exclusion

`TokenRing.tla` models a classic distributed protocol: N processes arranged in a ring pass a token. Only the token holder may enter the critical section.

This is the core mechanism behind distributed lock services like Chubby, ZooKeeper, and etcd.

**The key safety property — mutual exclusion — is 1-inductive.** Entering the critical section requires holding the token, and the token is unique. Therefore, at most one process can be critical at any time. A symbolic engine can prove this in a single inductive step regardless of N.

### Files

| File | Description |
|------|-------------|
| `TokenRing.tla` | Correct protocol: all invariants hold |
| `TokenRing.cfg` | Config for N=5 processes |
| `TokenRingBuggy.tla` | **Buggy** version: process 1 enters without the token |
| `TokenRingBuggy.cfg` | Config for the buggy spec |

## Running the Demo

### Prerequisites

Build TLA2 with the z4 SMT solver enabled:

```bash
cargo build --release --bin tla2 --features z4
```

### 1. Verify the correct protocol (CDEMC)

```bash
tla2 check TokenRing.tla --config TokenRing.cfg
```

Expected output:
```
Fused mode: cooperative BFS + symbolic verification (CDEMC)

Model checking complete. No error has been found.
  320 states found.
  Resolved by: BFS (explicit-state)
```

All four lanes run cooperatively. For N=5 (320 states), BFS finishes first because the state space is small. The symbolic engines confirm safety in parallel.

### 2. Find a bug (CDEMC catches it)

```bash
tla2 check TokenRingBuggy.tla --config TokenRingBuggy.cfg
```

Expected output:
```
Error: Invariant MutualExclusion is violated.
```

The buggy version lets process 1 enter the critical section without the token. CDEMC finds the violation — BFS discovers the counterexample during breadth-first exploration, while BMC simultaneously searches for it symbolically.

### 3. Compare: BFS-only mode

```bash
tla2 check TokenRing.tla --config TokenRing.cfg --bfs-only
```

The `--bfs-only` flag disables CDEMC and runs pure explicit-state model checking (equivalent to TLC). For small N, this is faster because there's no symbolic engine overhead. The value of CDEMC emerges at scale.

## Why CDEMC Matters

### The scalability wall

| N (processes) | States | BFS time | Symbolic |
|:---:|---:|---:|:---:|
| 5 | 320 | 0.01s | instant |
| 8 | 4,096 | 18s | instant |
| 12 | ~17M | minutes | instant |
| 20 | ~1 trillion | infeasible | instant |

The mutual exclusion invariant is 1-inductive *regardless of N*. A symbolic engine proves it with a single SMT query: "assume the invariant holds now and one step is taken; prove it holds after." BFS must enumerate every single state.

### Real-world protocols

Production distributed systems — consensus protocols (Paxos, Raft), lock services, transaction coordinators — have state spaces that grow exponentially with the number of participants. CDEMC makes verification of these protocols practical by combining:

1. **BFS correctness** (ground truth, concrete counterexamples)
2. **Symbolic speed** (prove safety without enumeration)
3. **Cross-validation** (symbolic results verified against BFS evaluator)
4. **Graceful degradation** (if symbolic engines fail on unsupported constructs, BFS continues alone)

### The oracle: adaptive engine selection

Not all actions in a spec benefit from symbolic reasoning. CDEMC's oracle monitors branching factors at runtime:

- **Low branching** (< 100 successors/action): BFS is efficient, keep it in BFS
- **High branching** (> 100 successors/action): route to symbolic engine
- **SMT-incompatible**: always BFS (the symbolic engine can't handle it)

The oracle uses Thompson sampling to self-tune these thresholds during verification, learning which routing decisions produce better outcomes as the exploration progresses.

## Architecture

CDEMC is implemented as a `FusedOrchestrator` that spawns four lanes via `std::thread::scope`:

1. **BFS lane** — standard explicit-state model checker with frontier sampling
2. **BMC lane** — z4 bounded model checking, seeded by BFS wavefronts
3. **PDR lane** — z4 IC3 property-directed reachability
4. **k-Induction lane** — z4 bounded inductive safety proofs

Cross-engine communication flows through `SharedCooperativeState`, a lock-free hub using atomic operations and bounded channels. The first lane to reach a definitive verdict (safety proved or violation found) publishes to a `SharedVerdict`; all other lanes terminate on their next poll.

Source: the `FusedOrchestrator` implementation in the tla-check crate (check/fused module).
