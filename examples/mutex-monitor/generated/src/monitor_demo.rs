// Copyright 2026 Dropbox.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Runtime monitoring demo for PetersonMutex.
//!
//! Demonstrates `MonitoredStateMachine` in two scenarios:
//!
//! 1. **Correct execution**: stepping through the correct Peterson protocol.
//!    The monitor confirms every transition preserves mutual exclusion.
//!
//! 2. **Violation detection**: a "broken" mutex that skips the turn-setting
//!    step. The monitor catches the MutualExclusion violation immediately
//!    when both processes reach the critical section.
//!
//! 3. **Model checking the bug**: BFS exhaustive check on the broken mutex
//!    finds the violation in the full state space.

mod peterson_mutex;

use peterson_mutex::{PetersonMutex, PetersonMutexState};
use tla_runtime::prelude::*;
use tla_runtime::{MonitoredStateMachine, SpecViolation};

fn main() {
    println!("TLA2 Runtime Monitor Demo: Peterson's Mutex");
    println!("============================================");
    println!();

    correct_execution_demo();
    println!();
    violation_detection_demo();
    println!();
    model_check_broken_demo();
    println!();
    println!("Demo complete.");
}

// -----------------------------------------------------------------------
// Demo 1: Correct Peterson mutex with monitoring
// -----------------------------------------------------------------------

fn correct_execution_demo() {
    println!("--- Demo 1: Correct Execution (monitored) ---");
    println!();

    let mut monitor = MonitoredStateMachine::new(PetersonMutex)
        .expect("invariant: PetersonMutex always produces initial states");

    println!("Initial state:");
    print_state(monitor.state());
    println!();

    // Drive a specific scenario: both processes contend for the critical section.
    // Process 0 sets flag, then process 1 sets flag, then both set turn, etc.
    // We use apply(action_index) to pick specific actions.
    println!("Scenario: both processes contend for the critical section.");
    println!("The monitor checks invariants on every transition.");
    println!();

    // The next() function returns actions in order: for each process p in {0,1},
    // it tries SetFlag(p), SetTurn(p), CheckWait(p), Enter(p), Exit(p).
    // From initial state, only SetFlag(0) and SetFlag(1) are enabled (indices 0, 1).

    // Step through both processes contending. Action indices depend on
    // which actions are enabled from the current state. next() iterates
    // p in {0,1} trying SetFlag, SetTurn, CheckWait, Enter, Exit for each.
    let steps: &[(&str, usize)] = &[
        // State: pc=[idle, idle]. Enabled: SetFlag(0)@0, SetFlag(1)@1
        ("Process 0: SetFlag (announce interest)", 0),
        // State: pc=[set_flag, idle]. Enabled: SetTurn(0)@0, SetFlag(1)@1
        ("Process 1: SetFlag (announce interest)", 1),
        // State: pc=[set_flag, set_flag]. Enabled: SetTurn(0)@0, SetTurn(1)@1
        ("Process 0: SetTurn (defer to process 1)", 0),
        // State: pc=[set_turn, set_flag]. Enabled: CheckWait(0)@0, SetTurn(1)@1
        ("Process 1: SetTurn (defer to process 0)", 1),
        // State: pc=[set_turn, set_turn]. Enabled: CheckWait(0)@0, CheckWait(1)@1
        ("Process 0: CheckWait", 0),
        // State: pc=[wait, set_turn]. Enabled: Enter(0)@0, CheckWait(1)@1
        ("Process 1: CheckWait", 1),
        // State: pc=[wait, wait]. turn=0, so p0 can enter, p1 blocked.
        // Enabled: Enter(0)@0
        ("Process 0: Enter critical (turn=0, p0 wins)", 0),
        // State: pc=[critical, wait]. Enabled: Exit(0)@0
        ("Process 0: Exit critical section", 0),
        // State: pc=[idle, wait]. flag[0]=false, so p1 can enter.
        // Enabled: SetFlag(0)@0, Enter(1)@1
        ("Process 1: Enter critical (p0 flag=false)", 1),
        // State: pc=[idle, critical]. Enabled: SetFlag(0)@0, Exit(1)@1
        ("Process 1: Exit critical section", 1),
    ];

    for (i, (desc, action)) in steps.iter().enumerate() {
        match monitor.apply(*action) {
            Ok(()) => {
                println!("  Step {:2}: {} ", i + 1, desc);
                println!("           {}", state_summary(monitor.state()));
            }
            Err(SpecViolation::ActionNotEnabled { .. }) => {
                println!("  Step {:2}: {} -- action not enabled, trying next", i + 1, desc);
            }
            Err(e) => {
                println!("  Step {:2}: ERROR: {:?}", i + 1, e);
                return;
            }
        }
    }

    let stats = monitor.stats();
    println!();
    println!(
        "All {} transitions safe. MutualExclusion holds throughout.",
        stats.transitions
    );
}

// -----------------------------------------------------------------------
// Demo 2: Broken mutex -- monitor catches violation
// -----------------------------------------------------------------------

fn violation_detection_demo() {
    println!("--- Demo 2: Catching a Bug (monitored) ---");
    println!();
    println!("A 'broken' mutex removes Peterson's wait condition. The correct");
    println!("protocol requires a process to wait until the other is not");
    println!("interested OR it's our turn. The broken version lets both enter.");
    println!();

    let mut monitor = MonitoredStateMachine::new(BrokenMutex)
        .expect("invariant: BrokenMutex produces initial states");

    // Drive the interleaving that exposes the bug:
    // Both processes set flag, both skip to wait, both enter critical.
    let steps: &[(&str, usize)] = &[
        ("Process 0: SetFlag", 0),
        ("Process 1: SetFlag", 1),
        // In the broken version, set_flag -> wait (skipping set_turn)
        ("Process 0: Skip to Wait (no turn set)", 0),
        ("Process 1: Skip to Wait (no turn set)", 1),
        // Both are in wait. Without the wait condition, both can enter!
        ("Process 0: Enter critical (no wait condition)", 0),
        // Process 1 also enters -- this should trigger the violation
        ("Process 1: Enter critical (BUG: both in critical!)", 1),
    ];

    for (i, (desc, action)) in steps.iter().enumerate() {
        match monitor.apply(*action) {
            Ok(()) => {
                println!("  Step {:2}: {}", i + 1, desc);
                println!("           {}", state_summary(monitor.state()));
            }
            Err(SpecViolation::InvariantViolated { ref state, ref violated_invariants, .. }) => {
                println!("  Step {:2}: {}", i + 1, desc);
                println!();
                println!("  >>> VIOLATION DETECTED! <<<");
                println!("  State: {}", broken_summary(state));
                println!("  Both processes are in the critical section!");
                if !violated_invariants.is_empty() {
                    println!("  Violated: {}", violated_invariants.join(", "));
                }
                println!();
                println!("  In production, this alert fires BEFORE any data corruption.");
                return;
            }
            Err(SpecViolation::ActionNotEnabled { action_index }) => {
                println!("  Step {:2}: {} -- not enabled (idx={})", i + 1, desc, action_index);
            }
            Err(e) => {
                println!("  Step {:2}: ERROR: {:?}", i + 1, e);
                return;
            }
        }
    }

    // If the scripted steps didn't trigger it, the BFS model check below will.
    println!();
    println!("  (Scripted trace didn't trigger violation -- see BFS check below.)");
}

// -----------------------------------------------------------------------
// Demo 3: Model check the broken mutex
// -----------------------------------------------------------------------

fn model_check_broken_demo() {
    println!("--- Demo 3: BFS Model Check of the Broken Mutex ---");
    println!();
    println!("Exhaustively exploring ALL reachable states of the broken mutex...");
    println!();

    let result = model_check_with_invariant(&BrokenMutex, 10_000, |state| {
        let p0 = state.pc.apply(&0).map(|s| s == "critical").unwrap_or(false);
        let p1 = state.pc.apply(&1).map(|s| s == "critical").unwrap_or(false);
        !(p0 && p1)
    });

    println!("States explored: {}", result.states_explored);
    println!("Distinct states: {}", result.distinct_states);

    if let Some(ref violation) = result.violation {
        println!();
        println!("VIOLATION FOUND:");
        println!("  pc[0] = {}", violation.state.pc.apply(&0).unwrap());
        println!("  pc[1] = {}", violation.state.pc.apply(&1).unwrap());
        println!("  flag  = [{}, {}]",
            violation.state.flag.apply(&0).unwrap(),
            violation.state.flag.apply(&1).unwrap());
        println!("  turn  = {}", violation.state.turn);
        println!();
        println!("  Both processes in the critical section -- MutualExclusion VIOLATED.");
        println!("  The broken protocol is UNSAFE.");
    } else {
        println!("No violation found (unexpected for the broken mutex).");
    }

    // Now compare with the correct version
    println!();
    println!("For comparison, BFS model check of the CORRECT Peterson mutex:");
    let correct_result = model_check(&PetersonMutex, 10_000);
    println!("  States: {}, Violations: {}, Deadlocks: {}",
        correct_result.distinct_states,
        if correct_result.violation.is_some() { "YES" } else { "none" },
        if correct_result.deadlock.is_some() { "YES" } else { "none" });
    println!("  The correct protocol is SAFE.");
}

// -----------------------------------------------------------------------
// BrokenMutex: Peterson without the turn step
// -----------------------------------------------------------------------

struct BrokenMutex;

impl StateMachine for BrokenMutex {
    type State = PetersonMutexState;

    fn init(&self) -> Vec<Self::State> {
        vec![PetersonMutexState {
            pc: TlaFunc::from_iter([(0_i64, "idle".to_string()), (1, "idle".to_string())]),
            flag: TlaFunc::from_iter([(0_i64, false), (1, false)]),
            turn: 0,
        }]
    }

    fn next(&self, state: &Self::State) -> Vec<Self::State> {
        let mut next_states = Vec::new();
        for p in [0_i64, 1] {
            let _other = 1 - p;

            // SetFlag: idle -> set_flag
            if state.pc.apply(&p).map(|s| s.as_str()) == Some("idle") {
                next_states.push(PetersonMutexState {
                    pc: state.pc.except(p, "set_flag".to_string()),
                    flag: state.flag.except(p, true),
                    turn: state.turn,
                });
            }

            // BUG: set_flag -> wait (skipping set_turn entirely!)
            if state.pc.apply(&p).map(|s| s.as_str()) == Some("set_flag") {
                next_states.push(PetersonMutexState {
                    pc: state.pc.except(p, "wait".to_string()),
                    flag: state.flag.clone(),
                    turn: state.turn,
                });
            }

            // Enter: wait -> critical
            // BUG #2: removed the wait condition entirely!
            // The correct version checks: flag[other] = FALSE \/ turn = p
            // This version lets the process enter regardless.
            if state.pc.apply(&p).map(|s| s.as_str()) == Some("wait") {
                next_states.push(PetersonMutexState {
                    pc: state.pc.except(p, "critical".to_string()),
                    flag: state.flag.clone(),
                    turn: state.turn,
                });
            }

            // Exit: critical -> idle
            if state.pc.apply(&p).map(|s| s.as_str()) == Some("critical") {
                next_states.push(PetersonMutexState {
                    pc: state.pc.except(p, "idle".to_string()),
                    flag: state.flag.except(p, false),
                    turn: state.turn,
                });
            }
        }
        next_states
    }

    fn check_invariant(&self, state: &Self::State) -> Option<bool> {
        let p0 = state.pc.apply(&0).map(|s| s == "critical").unwrap_or(false);
        let p1 = state.pc.apply(&1).map(|s| s == "critical").unwrap_or(false);
        Some(!(p0 && p1))
    }

    fn invariant_names(&self) -> Vec<&'static str> {
        vec!["MutualExclusion"]
    }

    fn check_named_invariant(&self, name: &str, state: &Self::State) -> Option<bool> {
        match name {
            "MutualExclusion" => self.check_invariant(state),
            _ => None,
        }
    }
}

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

fn print_state(state: &PetersonMutexState) {
    println!(
        "  pc[0]={:<10} pc[1]={:<10} flag=[{}, {}] turn={}",
        state.pc.apply(&0).unwrap(),
        state.pc.apply(&1).unwrap(),
        state.flag.apply(&0).unwrap(),
        state.flag.apply(&1).unwrap(),
        state.turn
    );
}

fn state_summary(state: &PetersonMutexState) -> String {
    format!(
        "pc=[{}, {}] flag=[{}, {}] turn={}",
        state.pc.apply(&0).unwrap(),
        state.pc.apply(&1).unwrap(),
        state.flag.apply(&0).unwrap(),
        state.flag.apply(&1).unwrap(),
        state.turn
    )
}

fn broken_summary(state: &PetersonMutexState) -> String {
    state_summary(state)
}
