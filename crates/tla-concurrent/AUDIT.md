# tla-concurrent Audit Report

Researcher audit of crate `tla-concurrent` implementation quality and correctness.

Audit scope: all files in `src/generate/`, `src/model.rs`, `src/transition.rs`,
`src/property.rs`, `src/check.rs`, `src/output.rs`, `tests/`.

Date: 2026-04-11 | Auditor: Researcher agent | HEAD at time of audit.

---

## 1. Bugs Found

### BUG-1: AtomicStore, AtomicRmw, CasOk declare `updated_vars` but generate NO state updates (P1)

**File:** `src/generate/actions.rs:372-381` (generate_transition_body) and `:992-997` (generate_transition_updates)

`generate_transition_body()` correctly adds the `variable` name to the `updated_vars` list for
`AtomicStore`, `AtomicRmw`, and `CasOk`. This means the UNCHANGED clause will NOT cover these
variables, which is correct. However, `generate_transition_updates()` at lines 992-997 matches
all three variants in the "No state updates needed" arm and emits ZERO update expressions.

**Result:** The generated TLA+ action says `variable` is NOT unchanged (it IS in `updated_vars`),
but also provides no update expression for the primed variable. In TLA+, this means the primed
value is completely unconstrained -- the variable can nondeterministically become ANY value. This
is semantically wrong: it over-approximates the behavior. For `AtomicStore`, the variable should
be set to the stored value. For `AtomicRmw`, it should apply the operation. For `CasOk`, it
should be set to the `new_value` from `CasInfo`.

Under sequential consistency (Phase 1), the correct updates would be:
- `AtomicStore`: `variable' = new_value`
- `AtomicRmw`: `variable' = Op(variable, operand)` (e.g., Add, Sub, Swap)
- `CasOk`: `variable' = cas_info.new_value` (with guard `variable = cas_info.expected`)

**Severity:** P1 -- atomic operations are the primary synchronization mechanism in lock-free
concurrent data structures. Without correct updates, any model with atomics will have
nondeterministic behavior and cannot detect real bugs.

**Suggested fix:** Add update arms in `generate_transition_updates()` for these three variants.
Also add a guard to `CasOk` in `generate_transition_body()` checking
`variable = cas_info.expected`.

### BUG-2: CasOk has no guard checking expected value (P1)

**File:** `src/generate/actions.rs:380`

`CasOk` returns `(None, vec![variable.clone()])` -- no guard. A successful CAS should guard on
`variable = expected`. Without this, CasOk is enabled in ANY state, meaning a
compare-and-swap can "succeed" even when the current value does not match the expected value.
This is unsound.

### BUG-3: Panic with MutexExclusive guard does not update `locks_held` in `generate_transition_updates` (P2)

**File:** `src/generate/actions.rs:916-983` (generate_transition_updates for Panic)

The `Panic` arm in `generate_transition_body()` correctly adds `locks_held` to `updated_vars`
when a MutexExclusive guard is present. The `Panic` arm in `generate_transition_updates()` sets
`mutex_owner` to NoOwner and `mutex_poisoned` to TRUE, but does NOT update `locks_held` to
remove the mutex from the panicking process's held set.

**Result:** `locks_held` is declared as updated (not in UNCHANGED), but no update expression is
generated. Like BUG-1, this leaves `locks_held'` unconstrained. In most cases this would cause
spurious state space explosion rather than missed bugs, but it could mask deadlock detection
(a process appears to hold locks it doesn't).

**Suggested fix:** Add `locks_held' = [locks_held EXCEPT ![pid] = locks_held[pid] \ {sync_id}]`
for each MutexExclusive panic guard.

### BUG-4: JoinCompleteness generates a state predicate but is classified as temporal (P2)

**File:** `src/property.rs` (line 51: not in `is_safety()`) and `src/generate/properties.rs:177-192`

`JoinCompleteness` is NOT in `is_safety()`, so `build_config()` adds it to `config.properties`
(temporal), not `config.invariants`. But the generated formula body is:

```tla
\A p \in Processes : pc["main"] \in TerminalStates => alive[p] = FALSE
```

This is a plain state predicate, not a temporal formula. When the checker wraps it in `[]`, it
becomes ``, which is semantically equivalent to an invariant. So it works
*accidentally*, but:

1. Temporal property checking is more expensive than invariant checking.
2. The classification is misleading -- code inspecting `is_safety()` will get the wrong answer.

**Suggested fix:** Either add `JoinCompleteness` to `is_safety()`, or change the generated body
to a temporal formula like `<>(\A p \in Processes : alive[p] = FALSE)`.

---

## 2. Correctness Gaps

### GAP-1: Shared variable initial values are always 0 regardless of `initial_value` field

**File:** `src/generate/init.rs:154-159`

```rust
let init_val = var
    .initial_value
    .as_deref()
    .map_or_else(|| int_lit(0), |_v| int_lit(0)); // TODO: parse initial value expressions
```

The `initial_value` field from the model is completely ignored. Both branches return `int_lit(0)`.
This means shared variables like booleans, strings, or non-zero integers are always initialized
to 0, which could cause false positives (init violation) or false negatives (missed bugs that
only occur with certain initial values).

### GAP-2: Channel sender count is always 1 regardless of model

**File:** `src/generate/init.rs:136-142`

```rust
.map(|s| (str_lit(&s.id), int_lit(1))) // default 1 sender
```

All channels are initialized with `senders_alive = 1`. In an MPSC model with N sender threads,
this should be N. The `ConcurrentModel` / `SyncKind::Channel` does not carry a sender count
field, so this needs both a model extension and init fix.

### GAP-3: ChannelSend does not check bounded channel capacity

**File:** `src/generate/actions.rs:393-398`

The `ChannelSend` guard only checks `receiver_alive[ch] = TRUE`. For bounded channels
(`SyncKind::Channel { capacity: Some(n) }`), the guard should also check
`Len(channel_buf[ch]) < capacity`. Without this, bounded channels behave identically to
unbounded ones, and buffer overflow bugs will never be detected.

### GAP-4: LockOrderConsistency is always TRUE (placeholder)

**File:** `src/generate/properties.rs:94-106`

The `generate_lock_order_consistency()` function returns `bool_lit(true)` unconditionally.
The comment says "rely on deadlock detection to catch lock order violations", but deadlock
detection and lock order consistency are different properties:
- Deadlock: a state with no successors (detected by the checker's built-in mechanism)
- Lock order violation: two threads acquire the same two locks in different orders, even if
  no deadlock occurs in the explored state space (e.g., because one thread is faster)

A schedule-dependent lock order violation can exist without causing deadlock in the explored
traces. This property is fundamentally incomplete.

### GAP-5: DataRaceFreedom does not condition on program counter state

**File:** `src/generate/properties.rs:114-163`

The generated invariant checks that guards are held unconditionally for all states. But the
`access_sites` are only active when a process is at the specific program counter state where
the access occurs. The current implementation requires the guard to be held in EVERY reachable
state, not just the states where the access happens. This causes false positives: a process
that releases a lock and later re-acquires it will violate the invariant even if the access
only occurs while the lock is held.

The fix is to add a pc-state predicate to each conjunct:
```tla
pc[process] = "state_where_access_occurs" => guard_held
```

But `AccessSite` does not currently carry a `state_id` field to enable this.

### GAP-6: ScopeEnd has no guard checking that scoped threads have terminated

**File:** `src/generate/actions.rs:131-133`

`ScopeEnd` returns `(None, vec![])` -- no guard and no updates. The comment says "Guard: all
scoped threads have terminated", but no such guard is generated. This means a scope can "end"
while scoped threads are still running, violating the core safety guarantee of `thread::scope`.

The fix requires tracking which processes belong to each scope and generating:
```tla
\A p \in scope_processes : pc[p] \in TerminalStates
```

### GAP-7: BarrierWait, OnceCallOnce, OnceLockSet, Park, Unpark are complete no-ops

**File:** `src/generate/actions.rs:582-598`

These five TransitionKind variants generate no guards, no updated vars, and no state updates.
They only advance the program counter. While marked as "TODO: barrier counting" etc., any model
using these primitives will have incorrect behavior:

- `BarrierWait`: should block until N threads arrive (requires `barrier_count` state variable)
- `OnceCallOnce`: should ensure exactly-once execution (requires `once_done` state variable)
- `OnceLockSet`: same as above
- `Park`: should block the thread until `Unpark` (requires `parked` state variable)
- `Unpark`: should unpark the target (requires `parked` state variable)

### GAP-8: NotifyOne should be nondeterministic, not a no-op

**File:** `src/generate/actions.rs:552-558`

`NotifyOne` generates no updates. In the current two-transition condvar model, WaitReacquire is
always enabled when the process is in the wait set and the mutex is free, so NotifyOne being a
no-op is *technically* sound because wakeups are already nondeterministic.

However, if the model ever gains a `notified` flag to restrict spurious wakeups (for more
precise modeling), NotifyOne would need to nondeterministically select one process from the
wait set and set its `notified` flag. This is a latent correctness gap.

### GAP-9: TryLockOk does not check `mutex_poisoned`

**File:** `src/generate/actions.rs:158-170`

`TryLockOk` only guards on `mutex_owner[m] = NoOwner`. It does NOT check
`mutex_poisoned[m] = FALSE`. In Rust, `Mutex::try_lock()` on a poisoned mutex returns
`Err(TryLockError::Poisoned(...))`, not `Ok(guard)`. The model allows acquiring a poisoned
mutex via `try_lock`, which is incorrect unless there's a `TryLockPoisonOk` variant (there
isn't).

In contrast, `Lock` correctly checks `NOT poisoned` (line 144).

---

## 3. Missing Test Coverage

### Tested patterns (2 tests in checker_integration.rs, 5 in serde_roundtrip.rs):
- Correct mutex (2 threads, 1 mutex, no deadlock)
- ABBA deadlock (2 threads, 2 mutexes, opposite lock order)
- Serde round-trip for ConcurrentModel
- TLA+ module generation structure (operators exist, extends correct)
- Source map lookup
- Property classification
- Assumptions default values

### NOT tested (critical gaps):

1. **RwLock patterns** -- zero tests. No reader-writer concurrency, no upgrade/downgrade, no
   try_read/try_write.

2. **Channel patterns** -- zero tests. No producer-consumer, no disconnection, no bounded
   channel, no try_recv.

3. **Condvar patterns** -- zero tests. No wait/notify, no spurious wakeup, no wait_timeout.

4. **Atomic operations** -- zero tests. No AtomicStore, AtomicRmw, CAS. This means BUG-1 and
   BUG-2 have gone undetected.

5. **Spawn/Join lifecycle** -- zero tests. No thread spawn, no join success/failure, no
   JoinCompleteness property.

6. **Panic semantics** -- zero tests. No mutex poisoning, no guard release on panic.

7. **Data race detection** -- zero tests. No shared variable with guarded/unguarded access.

8. **Fairness/liveness** -- zero tests. No WeakFairness, no StrongFairness, no Termination
   property.

9. **Multiple sync primitive types in one model** -- zero tests. Real programs mix mutexes,
   channels, and atomics.

10. **Model validation** -- zero tests for `validate_model()`. No test for empty processes,
    missing sync IDs, etc.

11. **Counterexample trace mapping** -- zero tests. All `check_result_to_report` TODO items
    (source mapping, distinct states, duration) are unverified.

---

## 4. Design Observations (Non-Blocking)

### OBS-1: Spawn transition does not set child's initial pc

The `Spawn` transition in `generate_transition_updates()` only sets `alive'[child] = TRUE`. It
does NOT set `pc'[child] = child.initial_state`. The child's pc is set in Init to
`child.initial_state`, and since `pc` is not in the Spawn's `updated_vars`, it appears in
UNCHANGED. This means the child process starts alive at `initial_state` from the very beginning
(from Init), and the Spawn transition just flips its `alive` flag.

This works correctly for the current model where all processes exist from Init but are gated by
`alive[p] = TRUE` in every action guard. But it means the "spawn" is not really a spawn -- it's
an "enable". This is a valid modeling choice but diverges from the Rust semantics where a spawned
thread's state machine does not exist until `thread::spawn` is called. It could cause false
positives if a child thread's initial transitions reference state that hasn't been set up by the
parent yet.

### OBS-2: All processes start alive in Init

`init.rs:43-48` initializes `alive = [p \in Processes |-> TRUE]` for ALL processes. Combined
with OBS-1, this means all processes (including spawned threads) are immediately alive and
executing from the initial state. The `alive` check in action guards prevents pre-spawn
execution only if every spawned process's transition graph requires `alive = TRUE`.

For correct spawn semantics, spawned processes should start with `alive[child] = FALSE`, and
the `Spawn` transition should flip it to `TRUE`. The current Init sets all to TRUE.

Wait -- re-reading the code: the `Spawn` guard checks `alive[child] = FALSE`. So if Init sets
all `alive` to TRUE, the Spawn guard is never satisfied, and the child is alive from the start.
This is either:
(a) A bug: spawned children are never actually spawned (they run from Init), OR
(b) Intentional: the model doesn't distinguish pre-spawn vs post-spawn for simplicity.

If (a), it means `Spawn` transitions are dead code. If (b), it should be documented. Either way,
this interacts poorly with `JoinCompleteness` which checks `alive[p] = FALSE` for all processes
when main terminates.

### OBS-3: `func_literal()` fallback format is `Debug` representation

**File:** `src/generate/init.rs:179`

```rust
_ => format!("{k:?}"),
```

If the key expression is neither `Expr::String` nor `Expr::Ident`, it falls back to Rust's
`Debug` format, producing something like `Expr::Int(BigInt { ... })` as a record field name.
This would create an invalid TLA+ record. Defensive, but should be a panic or error instead
of silently producing garbage.

### OBS-4: `check_result_to_report` uses `distinct_states = states_found`

**File:** `src/output.rs:70`

```rust
distinct_states: stats.states_found, // TODO: extract distinct from CheckStats
```

This means the stats are always reported as if every state is distinct, which could be
misleading for models with significant state duplication.

### OBS-5: `emit_tla` uses Debug format, not TLA+ syntax

**File:** `src/check.rs:94`

```rust
Some(format!("{module:?}")) // TODO: proper TLA+ pretty-printing
```

The `--emit-tla` option produces Rust Debug output, not valid TLA+ syntax. This is useless for
debugging the generated spec against a TLA+ reference implementation.

### OBS-6: `Termination` is a default property

`property.rs:86`: `Termination` is in `is_default()`, meaning it's auto-generated. But
`Termination { process }` requires a specific process name. How does the model know which
processes should have termination properties? The model builder (tRust) would need to add them.
If it forgets, no termination check happens. If it adds them for all processes including
background/daemon threads, it creates false liveness violations.

### OBS-7: Strong fairness uses SF for all actions

**File:** `src/generate/fairness.rs:48-64`

The `StrongFairness` mode generates `SF_vars(Next)` for the entire Next relation, not per-action.
The comment says "SF for condvar and channel actions, WF for the rest" but the implementation
just does SF for all. This is an over-specification of fairness that could hide liveness bugs.

### OBS-8: `Expr::Tuple(vec![])` for empty sequence

**File:** `src/generate/helpers.rs:205`

`empty_seq()` returns `Expr::Tuple(vec![])`. In TLA+, `<<>>` is indeed a 0-length sequence,
and tuples and sequences share syntax. This is correct but worth noting: the evaluator must
handle the empty tuple case consistently as a sequence for `Len()`, `Append()`, and `Tail()`
operations used in channel transitions.

---

## Summary

| Category | Count | Severity |
|----------|-------|----------|
| Bugs | 4 | 2x P1, 2x P2 |
| Correctness gaps | 9 | Mix of blocking and non-blocking |
| Missing test patterns | 11 | Critical coverage gaps |
| Design observations | 8 | Informational |

**Most critical items:**
1. BUG-1 + BUG-2: Atomic operations are fundamentally broken (no updates, no CAS guard)
2. GAP-5: DataRaceFreedom invariant is too strong (no pc conditioning)
3. GAP-6: ScopeEnd has no guard (violates thread::scope safety)
4. OBS-2: All processes start alive in Init, potentially making Spawn transitions dead code
5. Test coverage is minimal -- only mutex patterns are tested
