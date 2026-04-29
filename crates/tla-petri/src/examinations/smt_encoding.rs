// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared SMT encoding and solver helpers for reachability analyses.

use std::io::Write;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crate::petri_net::PetriNet;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

/// Maximum per-depth timeout for z4 solver invocation.
pub(super) const PER_DEPTH_TIMEOUT: Duration = Duration::from_secs(3);

/// Shared geometric depth ladder for SMT-based reachability analyses.
pub(super) const DEPTH_LADDER: &[usize] = &[1, 2, 4, 8, 16];

/// Outcome of a single property check at a given SMT depth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SolverOutcome {
    /// Solver returned `sat` — witness/counterexample exists.
    Sat,
    /// Solver returned `unsat` — the query is disproved at this depth.
    Unsat,
    /// Solver returned `unknown`, timed out, or produced unparseable output.
    Unknown,
}

/// Find z4 binary. Checks Z4_PATH, ~/z4/target/release/z4, then PATH.
pub(super) fn find_z4() -> Option<std::path::PathBuf> {
    if let Ok(path) = std::env::var("Z4_PATH") {
        let path = std::path::PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }

    if let Some(home) = home_dir() {
        let path = home.join("z4/target/release/z4");
        if path.is_file() {
            return Some(path);
        }
    }

    if let Ok(output) = Command::new("which").arg("z4").output() {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return Some(std::path::PathBuf::from(path));
            }
        }
    }

    None
}

fn home_dir() -> Option<std::path::PathBuf> {
    std::env::var("HOME").ok().map(std::path::PathBuf::from)
}

/// Encode a resolved predicate as an SMT-LIB expression at a given step.
pub(super) fn encode_predicate(pred: &ResolvedPredicate, step: usize, net: &PetriNet) -> String {
    match pred {
        ResolvedPredicate::True => "true".to_string(),
        ResolvedPredicate::False => "false".to_string(),
        ResolvedPredicate::And(children) => {
            if children.is_empty() {
                return "true".to_string();
            }
            if children.len() == 1 {
                return encode_predicate(&children[0], step, net);
            }
            let parts: Vec<String> = children
                .iter()
                .map(|child| encode_predicate(child, step, net))
                .collect();
            format!("(and {})", parts.join(" "))
        }
        ResolvedPredicate::Or(children) => {
            if children.is_empty() {
                return "false".to_string();
            }
            if children.len() == 1 {
                return encode_predicate(&children[0], step, net);
            }
            let parts: Vec<String> = children
                .iter()
                .map(|child| encode_predicate(child, step, net))
                .collect();
            format!("(or {})", parts.join(" "))
        }
        ResolvedPredicate::Not(inner) => {
            format!("(not {})", encode_predicate(inner, step, net))
        }
        ResolvedPredicate::IntLe(left, right) => {
            format!(
                "(<= {} {})",
                encode_int_expr(left, step),
                encode_int_expr(right, step)
            )
        }
        ResolvedPredicate::IsFireable(transitions) => {
            if transitions.is_empty() {
                return "false".to_string();
            }
            let parts: Vec<String> = transitions
                .iter()
                .map(|transition_idx| {
                    let transition = &net.transitions[transition_idx.0 as usize];
                    if transition.inputs.is_empty() {
                        return "true".to_string();
                    }
                    let guards: Vec<String> = transition
                        .inputs
                        .iter()
                        .map(|arc| {
                            format!("(>= m_{}_{} {})", step, arc.place.0 as usize, arc.weight)
                        })
                        .collect();
                    if guards.len() == 1 {
                        guards[0].clone()
                    } else {
                        format!("(and {})", guards.join(" "))
                    }
                })
                .collect();
            if parts.len() == 1 {
                parts[0].clone()
            } else {
                format!("(or {})", parts.join(" "))
            }
        }
    }
}

/// Encode a resolved integer expression as SMT-LIB at a given step.
pub(super) fn encode_int_expr(expr: &ResolvedIntExpr, step: usize) -> String {
    match expr {
        ResolvedIntExpr::Constant(value) => format!("{value}"),
        ResolvedIntExpr::TokensCount(places) => {
            if places.is_empty() {
                "0".to_string()
            } else if places.len() == 1 {
                format!("m_{}_{}", step, places[0].0)
            } else {
                let parts: Vec<String> = places
                    .iter()
                    .map(|place| format!("m_{}_{}", step, place.0))
                    .collect();
                format!("(+ {})", parts.join(" "))
            }
        }
    }
}

/// Run z4 on an SMT script and parse outcomes for each property.
///
/// Returns `None` on process failure (timeout, crash, I/O error).
/// Returns `Some(outcomes)` with one outcome per property.
pub(super) fn run_z4(
    z4_path: &std::path::Path,
    script: &str,
    num_properties: usize,
    timeout: Duration,
) -> Option<Vec<SolverOutcome>> {
    let mut child = Command::new(z4_path)
        .arg("-smt2")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(script.as_bytes());
    }

    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_status)) => break,
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return None;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
        }
    }

    let output = child.wait_with_output().ok()?;
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Ignore diagnostic chatter and keep only definitive SMT solver status
    // tokens. The local z4 binary may emit `[DIAG-SAT] ...` lines on stdout
    // before the actual `sat`/`unsat` result.
    let outcomes: Vec<SolverOutcome> = stdout
        .lines()
        .map(str::trim)
        .filter_map(|line| match line {
            "sat" => Some(SolverOutcome::Sat),
            "unsat" => Some(SolverOutcome::Unsat),
            "unknown" => Some(SolverOutcome::Unknown),
            _ => None,
        })
        .collect();

    if outcomes.len() < num_properties {
        return None;
    }

    Some(outcomes[outcomes.len() - num_properties..].to_vec())
}

/// Encode the transition relation for steps 0..depth into the SMT script.
pub(super) fn encode_transition_relation(
    script: &mut String,
    net: &PetriNet,
    num_places: usize,
    num_transitions: usize,
    depth: usize,
) {
    encode_transition_relation_steps(script, net, num_places, num_transitions, 0..depth);
}

/// Encode the transition relation for a specific step range.
///
/// Each step encodes: exactly-one-fires-or-stutters, guard+effect assertions,
/// and frame conditions for all places.
pub(super) fn encode_transition_relation_steps(
    script: &mut String,
    net: &PetriNet,
    num_places: usize,
    num_transitions: usize,
    step_range: std::ops::Range<usize>,
) {
    for step in step_range {
        script.push_str(&format!("(assert (or stay_{step}"));
        for transition in 0..num_transitions {
            script.push_str(&format!(" fire_{}_{}", step, transition));
        }
        script.push_str("))\n");

        let mut all_options = vec![format!("stay_{step}")];
        for transition in 0..num_transitions {
            all_options.push(format!("fire_{}_{}", step, transition));
        }
        for left in 0..all_options.len() {
            for right in (left + 1)..all_options.len() {
                script.push_str(&format!(
                    "(assert (not (and {} {})))\n",
                    all_options[left], all_options[right]
                ));
            }
        }

        for place in 0..num_places {
            script.push_str(&format!(
                "(assert (=> stay_{} (= m_{}_{} m_{}_{})))\n",
                step,
                step + 1,
                place,
                step,
                place
            ));
        }

        for transition_idx in 0..num_transitions {
            let transition = &net.transitions[transition_idx];
            let fire_var = format!("fire_{}_{}", step, transition_idx);

            for arc in &transition.inputs {
                let place = arc.place.0 as usize;
                script.push_str(&format!(
                    "(assert (=> {} (>= m_{}_{} {})))\n",
                    fire_var, step, place, arc.weight
                ));
            }

            let mut deltas: Vec<(usize, i64)> = Vec::new();
            for arc in &transition.inputs {
                let place = arc.place.0 as usize;
                match deltas
                    .iter_mut()
                    .find(|(existing_place, _)| *existing_place == place)
                {
                    Some((_, delta)) => *delta -= arc.weight as i64,
                    None => deltas.push((place, -(arc.weight as i64))),
                }
            }
            for arc in &transition.outputs {
                let place = arc.place.0 as usize;
                match deltas
                    .iter_mut()
                    .find(|(existing_place, _)| *existing_place == place)
                {
                    Some((_, delta)) => *delta += arc.weight as i64,
                    None => deltas.push((place, arc.weight as i64)),
                }
            }

            for &(place, delta) in &deltas {
                if delta == 0 {
                    script.push_str(&format!(
                        "(assert (=> {} (= m_{}_{} m_{}_{})))\n",
                        fire_var,
                        step + 1,
                        place,
                        step,
                        place
                    ));
                } else if delta > 0 {
                    script.push_str(&format!(
                        "(assert (=> {} (= m_{}_{} (+ m_{}_{} {}))))\n",
                        fire_var,
                        step + 1,
                        place,
                        step,
                        place,
                        delta
                    ));
                } else {
                    script.push_str(&format!(
                        "(assert (=> {} (= m_{}_{} (- m_{}_{} {}))))\n",
                        fire_var,
                        step + 1,
                        place,
                        step,
                        place,
                        -delta
                    ));
                }
            }

            let affected: Vec<usize> = deltas.iter().map(|(place, _)| *place).collect();
            for place in 0..num_places {
                if !affected.contains(&place) {
                    script.push_str(&format!(
                        "(assert (=> {} (= m_{}_{} m_{}_{})))\n",
                        fire_var,
                        step + 1,
                        place,
                        step,
                        place
                    ));
                }
            }
        }
    }
}
