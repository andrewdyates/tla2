// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kani proof-of-concept for verified code generation.
//!
//! This module demonstrates the pattern for verifying that Rust code generated
//! from TLA+ specifications preserves invariants. It contains a hand-written
//! example equivalent to the code that [`crate::emit`] and [`crate::z4_codegen`]
//! would produce from the following TLA+ spec:
//!
//! ```text
//! ---- MODULE ModularCounter ----
//! VARIABLE x
//! Init == x = 0
//! Next == x' = (x + 1) % 10
//! Inv  == x >= 0 /\ x < 10
//! ====
//! ```
//!
//! # Verification Strategy
//!
//! The harnesses follow the standard inductive invariant proof scheme:
//!
//! 1. **Base case** (`prove_init_satisfies_inv`):
//!    For every state satisfying `Init`, `Inv` holds.
//!
//! 2. **Inductive step** (`prove_next_preserves_inv`):
//!    For every state satisfying `Inv`, every successor via `Next` also
//!    satisfies `Inv`.
//!
//! Together these prove that `Inv` holds in every reachable state, for
//! *all* execution depths — not just a bounded prefix.
//!
//! 3. **Bounded model check** (`prove_bounded_k_steps`):
//!    Explore all states reachable within `K` steps and verify `Inv` at each.
//!    This is a weaker check (bounded) but catches bugs where `Inv` is not
//!    actually inductive and the base+inductive proof would need strengthening.
//!
//! # Running
//!
//! With Kani installed:
//! ```bash
//! cargo kani -p tla-codegen --harness prove_init_satisfies_inv
//! cargo kani -p tla-codegen --harness prove_next_preserves_inv
//! cargo kani -p tla-codegen --harness prove_bounded_k_steps
//! ```
//!
//! Without Kani, the same logic runs as standard `#[test]` functions:
//! ```bash
//! cargo test -p tla-codegen -- kani_demo
//! ```

/// State type generated from `VARIABLE x`.
///
/// In the real code generator, this struct is emitted by
/// [`crate::emit::RustEmitter`] with one field per TLA+ `VARIABLE`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ModularCounterState {
    pub(crate) x: i64,
}

/// Generated `Init` predicate: `x = 0`.
pub(crate) fn init() -> Vec<ModularCounterState> {
    vec![ModularCounterState { x: 0 }]
}

/// Generated `Next` action: `x' = (x + 1) % 10`.
///
/// Returns all possible successor states. For this deterministic spec there
/// is exactly one successor per state.
pub(crate) fn next(state: &ModularCounterState) -> Vec<ModularCounterState> {
    vec![ModularCounterState {
        x: (state.x + 1) % 10,
    }]
}

/// Generated invariant check: `x >= 0 /\ x < 10`.
pub(crate) fn check_inv(state: &ModularCounterState) -> bool {
    state.x >= 0 && state.x < 10
}

// ---------------------------------------------------------------------------
// Kani harnesses (active only under `cargo kani`)
// ---------------------------------------------------------------------------

/// Base case: every initial state satisfies `Inv`.
#[cfg(kani)]
#[kani::proof]
fn prove_init_satisfies_inv() {
    let states = init();
    for state in &states {
        kani::assert(check_inv(state), "Inv violated in initial state");
    }
}

/// Inductive step: if `Inv` holds in state `s`, then `Inv` holds in every
/// successor `next(s)`.
///
/// We use `kani::any()` to let the verifier explore *all* possible `i64`
/// values for `x`, constrained by `kani::assume` to those satisfying `Inv`.
/// This proves the inductive step universally — no bounded unrolling needed.
#[cfg(kani)]
#[kani::proof]
fn prove_next_preserves_inv() {
    let x: i64 = kani::any();
    // Constrain to states satisfying the invariant (inductive hypothesis).
    let state = ModularCounterState { x };
    kani::assume(check_inv(&state));

    // Every successor must also satisfy the invariant.
    let successors = next(&state);
    for ns in &successors {
        kani::assert(check_inv(ns), "Inv violated after transition");
    }
}

/// Bounded model check: explore all states reachable within K=15 steps
/// (covers more than one full cycle of the mod-10 counter) and verify `Inv`
/// at each step.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(16)]
fn prove_bounded_k_steps() {
    let init_states = init();
    if init_states.is_empty() {
        return;
    }
    // Pick a non-deterministic initial state.
    let idx: usize = kani::any();
    kani::assume(idx < init_states.len());
    let mut state = init_states[idx].clone();
    kani::assert(check_inv(&state), "Inv violated at step 0");

    // Step through K transitions.
    let k: usize = kani::any();
    kani::assume(k <= 15);
    let mut i = 0;
    while i < k {
        let succs = next(&state);
        if succs.is_empty() {
            break;
        }
        state = succs[0].clone();
        kani::assert(check_inv(&state), "Inv violated after step");
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// Standard test fallbacks (run without Kani via `cargo test`)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Test equivalent of `prove_init_satisfies_inv`.
    #[test]
    fn test_init_satisfies_inv() {
        let states = init();
        assert!(!states.is_empty(), "Init must produce at least one state");
        for state in &states {
            assert!(
                check_inv(state),
                "Inv violated in initial state: {:?}",
                state
            );
        }
    }

    /// Test equivalent of `prove_next_preserves_inv`: check the inductive
    /// step for every state in the reachable state space (which is finite
    /// for this spec: x in 0..10).
    #[test]
    fn test_next_preserves_inv() {
        for x in 0..10i64 {
            let state = ModularCounterState { x };
            assert!(check_inv(&state), "precondition: Inv holds for x={}", x);

            let successors = next(&state);
            for ns in &successors {
                assert!(
                    check_inv(ns),
                    "Inv violated after transition: {:?} -> {:?}",
                    state,
                    ns
                );
            }
        }
    }

    /// Test equivalent of `prove_bounded_k_steps`: exhaustive BFS verifying
    /// `Inv` at every reachable state.
    #[test]
    fn test_bounded_exploration() {
        use std::collections::HashSet;

        let mut seen = HashSet::new();
        let mut frontier = init();
        let mut total = 0;
        let max_states = 1000;

        while let Some(state) = frontier.pop() {
            if !seen.insert(state.clone()) {
                continue;
            }
            assert!(
                check_inv(&state),
                "Inv violated at state {:?} (step {})",
                state,
                total
            );
            total += 1;
            if total >= max_states {
                break;
            }
            frontier.extend(next(&state));
        }

        // The modular counter has exactly 10 reachable states: 0..10.
        assert_eq!(total, 10, "expected exactly 10 reachable states");
    }

    /// Verify the state space is exactly {0, 1, ..., 9}.
    #[test]
    fn test_state_space_is_complete() {
        use std::collections::HashSet;

        let mut seen = HashSet::new();
        let mut frontier = init();

        while let Some(state) = frontier.pop() {
            if !seen.insert(state.clone()) {
                continue;
            }
            frontier.extend(next(&state));
        }

        let xs: HashSet<i64> = seen.iter().map(|s| s.x).collect();
        let expected: HashSet<i64> = (0..10).collect();
        assert_eq!(xs, expected, "state space mismatch");
    }

    /// Negative test: a bad invariant IS violated by the state machine,
    /// confirming our checking methodology actually catches violations.
    #[test]
    fn test_bad_invariant_detected() {
        // Suppose someone claimed Inv == x < 5. That is violated by x=5..9.
        let bad_inv = |s: &ModularCounterState| s.x < 5;

        let mut frontier = init();
        let mut seen = std::collections::HashSet::new();
        let mut found_violation = false;

        while let Some(state) = frontier.pop() {
            if !seen.insert(state.clone()) {
                continue;
            }
            if !bad_inv(&state) {
                found_violation = true;
                break;
            }
            frontier.extend(next(&state));
        }

        assert!(
            found_violation,
            "bad invariant should have been detected as violated"
        );
    }
}
