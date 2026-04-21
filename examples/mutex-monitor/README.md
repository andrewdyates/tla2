# Peterson's Mutex: TLA2 Codegen Demo

**TLA+ specification -> verified Rust code -> runtime monitoring**

This example demonstrates TLA2's unique code generation pipeline: take a
formally verified TLA+ specification and produce Rust code that implements
the same state machine, complete with runtime invariant monitoring.

No other TLA+ tool does this.

## Quick Start

```bash
# From the tla2 repo root:
./examples/mutex-monitor/run_demo.sh

# Or skip TLA2 steps and just run the generated code:
./examples/mutex-monitor/run_demo.sh --skip-tla2
```

## What You'll See

### 1. Model check the TLA+ spec

```bash
cargo run --release --bin tla2 -- check \
    examples/mutex-monitor/PetersonMutex.tla \
    --config examples/mutex-monitor/PetersonMutex.cfg
```

Output:
```
Model checking complete: No errors found (exhaustive).
States found: 32
```

All 32 reachable states explored. `MutualExclusion` holds in every one.

### 2. Generate Rust code

```bash
cargo run --release --bin tla2 -- codegen --tir \
    --config examples/mutex-monitor/PetersonMutex.cfg \
    examples/mutex-monitor/PetersonMutex.tla
```

This generates a Rust `StateMachine` implementation: state struct, `init()`,
`next()`, and invariant checks. The `generated/` directory contains the
completed version with hand-polished Next actions.

### 3. Test the generated code

```bash
cd examples/mutex-monitor/generated && cargo test
```

7 tests verify: invariants hold on all init states, all successors,
exhaustive BFS finds no violations, no deadlocks, and the state space is
exactly 32 states (matching TLA2).

### 4. BFS model check in compiled Rust

```bash
cargo run --release --bin check
```

```
Peterson's Mutex -- compiled BFS model checker
================================================

Distinct states: 32
States explored: 32

Model check complete: no errors found.
Safety verified: MutualExclusion holds across all 32 states.
```

Same result as the TLA2 model checker, but running as compiled Rust.

### 5. Runtime monitor demo

```bash
cargo run --release --bin monitor-demo
```

This is the key demo. It shows `MonitoredStateMachine` in action:

**Correct execution:** The monitor wraps the Peterson mutex and checks
`MutualExclusion` on every single state transition. All transitions are safe.

**Catching a bug:** A "broken" version of the mutex removes the wait
condition (the check that prevents both processes from entering the critical
section). The monitor catches the violation immediately:

```
  >>> VIOLATION DETECTED! <<<
  State: pc=[critical, critical] flag=[true, true] turn=0
  Both processes are in the critical section!
  Violated: MutualExclusion

  In production, this alert fires BEFORE any data corruption.
```

**Exhaustive BFS of the broken version:** The model checker explores all 16
reachable states of the broken protocol and confirms the violation exists in
the full state space.

## Files

```
PetersonMutex.tla     -- TLA+ specification (source of truth)
PetersonMutex.cfg     -- Model checker configuration
run_demo.sh           -- One-command end-to-end demo
generated/
  Cargo.toml          -- Standalone Cargo project
  src/
    lib.rs            -- Module re-exports
    peterson_mutex.rs -- Generated state machine (from tla2 codegen)
    main.rs           -- BFS model checker binary
    monitor_demo.rs   -- Runtime monitoring demo binary
```

## Architecture

```
  PetersonMutex.tla          tla2 codegen         peterson_mutex.rs
  (formal spec)     ---------------------------> (Rust StateMachine)
        |                                               |
        | tla2 check                                    | cargo test
        v                                               v
  "32 states, no errors"                       "all invariants hold"
                                                        |
                                                        | MonitoredStateMachine
                                                        v
                                                 runtime invariant
                                                   checking in
                                                  production code
```

## Sample Terminal Output

Running `cargo run --release --bin monitor-demo` produces:

```
TLA2 Runtime Monitor Demo: Peterson's Mutex
============================================

--- Demo 1: Correct Execution (monitored) ---

Initial state:
  pc[0]=idle       pc[1]=idle       flag=[false, false] turn=0

Scenario: both processes contend for the critical section.
The monitor checks invariants on every transition.

  Step  1: Process 0: SetFlag (announce interest)
           pc=[set_flag, idle] flag=[true, false] turn=0
  Step  2: Process 1: SetFlag (announce interest)
           pc=[set_flag, set_flag] flag=[true, true] turn=0
  Step  3: Process 0: SetTurn (defer to process 1)
           pc=[set_turn, set_flag] flag=[true, true] turn=1
  Step  4: Process 1: SetTurn (defer to process 0)
           pc=[set_turn, set_turn] flag=[true, true] turn=0
  Step  5: Process 0: CheckWait
           pc=[wait, set_turn] flag=[true, true] turn=0
  Step  6: Process 1: CheckWait
           pc=[wait, wait] flag=[true, true] turn=0
  Step  7: Process 0: Enter critical (turn=0, p0 wins)
           pc=[critical, wait] flag=[true, true] turn=0
  Step  8: Process 0: Exit critical section
           pc=[idle, wait] flag=[false, true] turn=0
  Step  9: Process 1: Enter critical (p0 flag=false)
           pc=[idle, critical] flag=[false, true] turn=0
  Step 10: Process 1: Exit critical section
           pc=[idle, idle] flag=[false, false] turn=0

All 10 transitions safe. MutualExclusion holds throughout.

--- Demo 2: Catching a Bug (monitored) ---

A 'broken' mutex removes Peterson's wait condition. The correct
protocol requires a process to wait until the other is not
interested OR it's our turn. The broken version lets both enter.

  Step  1: Process 0: SetFlag
           pc=[set_flag, idle] flag=[true, false] turn=0
  Step  2: Process 1: SetFlag
           pc=[set_flag, set_flag] flag=[true, true] turn=0
  Step  3: Process 0: Skip to Wait (no turn set)
           pc=[wait, set_flag] flag=[true, true] turn=0
  Step  4: Process 1: Skip to Wait (no turn set)
           pc=[wait, wait] flag=[true, true] turn=0
  Step  5: Process 0: Enter critical (no wait condition)
           pc=[critical, wait] flag=[true, true] turn=0
  Step  6: Process 1: Enter critical (BUG: both in critical!)

  >>> VIOLATION DETECTED! <<<
  State: pc=[critical, critical] flag=[true, true] turn=0
  Both processes are in the critical section!
  Violated: MutualExclusion

  In production, this alert fires BEFORE any data corruption.

--- Demo 3: BFS Model Check of the Broken Mutex ---

Exhaustively exploring ALL reachable states of the broken mutex...

States explored: 16
Distinct states: 16

VIOLATION FOUND:
  pc[0] = critical
  pc[1] = critical
  flag  = [true, true]
  turn  = 0

  Both processes in the critical section -- MutualExclusion VIOLATED.
  The broken protocol is UNSAFE.

For comparison, BFS model check of the CORRECT Peterson mutex:
  States: 32, Violations: none, Deadlocks: none
  The correct protocol is SAFE.
```

## Why This Matters

1. **Spec-first development**: Write the algorithm in TLA+, prove it correct,
   then generate the implementation. The spec is the source of truth.

2. **Cross-validation**: TLA+ model checker and Rust BFS agree on 32 states.

3. **Runtime monitoring**: `MonitoredStateMachine` checks invariants on every
   transition in production. Catch bugs before they cause damage.

4. **The path**: TLA+ spec -> model check -> codegen -> test -> deploy with
   runtime monitors. Formal methods all the way to production.
