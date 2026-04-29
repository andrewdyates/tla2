// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Liveness and safety trace building/formatting for counterexample display.

use tla_check::{liveness_trace_to_dot, trace_to_dot, Trace};

use crate::cli_schema::TraceFormat;

pub(super) struct PropertyViolationPresentation {
    pub tlc_code: i32,
    pub headline: String,
    pub trace_intro: &'static str,
}

pub(super) fn property_violation_presentation(
    property: &str,
    kind: tla_check::PropertyViolationKind,
) -> PropertyViolationPresentation {
    use crate::tlc_codes;
    match kind {
        tla_check::PropertyViolationKind::StateLevel => PropertyViolationPresentation {
            tlc_code: tlc_codes::ec::TLC_INVARIANT_VIOLATED_BEHAVIOR,
            headline: format!("Invariant {property} is violated."),
            trace_intro: "The behavior up to this point is:",
        },
        tla_check::PropertyViolationKind::ActionLevel => PropertyViolationPresentation {
            tlc_code: tlc_codes::ec::TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
            headline: format!("Action property {property} is violated."),
            trace_intro: "The behavior up to this point is:",
        },
    }
}

/// Format a liveness counterexample trace (prefix + cycle) with TLC-compatible
/// annotations for stuttering and cycle back-edges.
///
/// TLC emits `N: Stuttering` when a cycle contains only self-loops (all
/// states have the same fingerprint). TLC emits `Back to state N: <ActionLabel>`
/// when a cycle closes by returning to its start state.
///
/// Part of #2470, #2398: TLC-matching trace format with action labels.
pub(super) fn format_liveness_trace_text(prefix: &Trace, cycle: &Trace) {
    eprint!("{}", build_liveness_trace_text(prefix, cycle));
}

/// Build the formatted liveness trace string (full mode).
pub(super) fn build_liveness_trace_text(prefix: &Trace, cycle: &Trace) -> String {
    build_liveness_trace_inner(prefix, cycle, false)
        .expect("invariant: fmt::Write for String is infallible")
}

/// Build the formatted liveness trace string (diff mode, --difftrace).
pub(super) fn build_liveness_trace_difftrace(prefix: &Trace, cycle: &Trace) -> String {
    build_liveness_trace_inner(prefix, cycle, true)
        .expect("invariant: fmt::Write for String is infallible")
}

/// Get action label string for a state in a trace, falling back to placeholders.
fn get_action_label(trace: &Trace, idx: usize, is_first_overall: bool) -> String {
    if let Some(label) = trace.action_labels.get(idx) {
        format!("{}", label)
    } else if is_first_overall {
        "<Initial predicate>".to_string()
    } else {
        "<Action>".to_string()
    }
}

/// Write state variables in TLC format (single-var omits `/\ ` prefix).
///
/// When `diff` is true and `prev_state` is `Some`, only changed variables are shown.
fn write_state_vars(
    out: &mut String,
    state: &tla_check::State,
    prev_state: Option<&tla_check::State>,
    diff: bool,
) -> std::result::Result<(), std::fmt::Error> {
    if diff {
        write_vars_maybe_diff(out, state, prev_state)
    } else {
        write_vars_all(out, state)
    }
}

/// Write all state variables unconditionally.
fn write_vars_all(
    out: &mut String,
    state: &tla_check::State,
) -> std::result::Result<(), std::fmt::Error> {
    use std::fmt::Write;
    let vars: Vec<_> = state.vars().collect();
    if vars.len() == 1 {
        writeln!(out, "{} = {}", vars[0].0, vars[0].1)?;
    } else {
        for (name, value) in &vars {
            writeln!(out, "/\\ {} = {}", name, value)?;
        }
    }
    Ok(())
}

/// Core liveness trace builder parameterized by diff mode.
///
/// When `diff` is false, all variables are shown in every state (TLC default).
/// When `diff` is true, only changed variables are shown after the first state
/// (TLC `-difftrace` behavior). Part of #2470 Step 5.
fn build_liveness_trace_inner(
    prefix: &Trace,
    cycle: &Trace,
    diff: bool,
) -> std::result::Result<String, std::fmt::Error> {
    use std::fmt::Write;
    let mut out = String::new();
    let mut prev_state: Option<&tla_check::State> = None;

    // Print prefix states with sequential numbering (TLC uses "State N:" prefix).
    let mut state_num = 1usize;
    for (i, state) in prefix.states.iter().enumerate() {
        writeln!(
            out,
            "State {}: {}",
            state_num,
            get_action_label(prefix, i, i == 0)
        )?;
        write_state_vars(&mut out, state, prev_state, diff)?;
        writeln!(out)?; // TLC emits a blank line after each state.
        if diff {
            prev_state = Some(state);
        }
        state_num += 1;
    }

    if cycle.is_empty() {
        return Ok(out);
    }

    // Detect prefix-cycle overlap: skip first cycle state if it matches last prefix.
    let skip_first_cycle = !prefix.is_empty()
        && cycle.states[0].fingerprint()
            == prefix
                .states
                .last()
                .expect("invariant: prefix is non-empty")
                .fingerprint();
    let cycle_start_idx = usize::from(skip_first_cycle);
    let first_cycle_state_num = state_num - usize::from(skip_first_cycle);

    let effective_cycle = &cycle.states[cycle_start_idx..];
    if effective_cycle.is_empty() {
        return Ok(out);
    }

    // Detect stuttering: all effective cycle states have the same fingerprint.
    let first_fp = effective_cycle[0].fingerprint();
    let all_same = effective_cycle.iter().all(|s| s.fingerprint() == first_fp);

    if all_same && (skip_first_cycle || effective_cycle.len() > 1) {
        if !skip_first_cycle {
            writeln!(
                out,
                "State {}: {}",
                state_num,
                get_action_label(cycle, cycle_start_idx, state_num == 1)
            )?;
            write_state_vars(&mut out, &effective_cycle[0], prev_state, diff)?;
            writeln!(out)?; // blank line after state
            writeln!(out, "State {}: Stuttering", state_num + 1)?;
        } else {
            writeln!(out, "State {}: Stuttering", state_num)?;
        }
        return Ok(out);
    }

    // Detect back-to-state.
    let target_fp = if skip_first_cycle {
        prefix
            .states
            .last()
            .expect("invariant: prefix is non-empty")
            .fingerprint()
    } else {
        effective_cycle[0].fingerprint()
    };
    let last_fp = effective_cycle
        .last()
        .expect("invariant: effective_cycle is non-empty")
        .fingerprint();
    let has_back_edge = last_fp == target_fp && (effective_cycle.len() > 1 || skip_first_cycle);
    let cycle_end = if has_back_edge {
        effective_cycle.len() - 1
    } else {
        effective_cycle.len()
    };

    for (j, state) in effective_cycle[..cycle_end].iter().enumerate() {
        writeln!(
            out,
            "State {}: {}",
            state_num,
            get_action_label(cycle, cycle_start_idx + j, state_num == 1)
        )?;
        write_state_vars(&mut out, state, prev_state, diff)?;
        writeln!(out)?; // blank line after state
        if diff {
            prev_state = Some(state);
        }
        state_num += 1;
    }

    if has_back_edge {
        writeln!(
            out,
            "Back to state {}: {}",
            first_cycle_state_num,
            get_action_label(cycle, cycle.states.len() - 1, false)
        )?;
    }

    Ok(out)
}

// ---------------------------------------------------------------------------
// Diff-trace formatting (--difftrace / TLC -difftrace)
// ---------------------------------------------------------------------------

/// Helper: write state variables in TLC format, optionally showing only diffs.
///
/// If `prev_state` is `Some`, only variables whose values differ from the
/// previous state are printed. If all variables are unchanged, no variable
/// lines are emitted (TLC behavior). The first state always gets `None`
/// for `prev_state` so all variables are shown.
///
/// Part of #2470 Step 5.
fn write_vars_maybe_diff(
    out: &mut String,
    state: &tla_check::State,
    prev_state: Option<&tla_check::State>,
) -> std::result::Result<(), std::fmt::Error> {
    use std::fmt::Write;

    let vars: Vec<_> = state.vars().collect();
    match prev_state {
        None => {
            // First state: show all variables.
            if vars.len() == 1 {
                writeln!(out, "{} = {}", vars[0].0, vars[0].1)?;
            } else {
                for (name, value) in &vars {
                    writeln!(out, "/\\ {} = {}", name, value)?;
                }
            }
        }
        Some(prev) => {
            // Diff mode: only show changed variables.
            let changed: Vec<_> = vars
                .iter()
                .filter(|(name, value)| prev.get(name) != Some(*value))
                .collect();
            if changed.len() == 1 {
                writeln!(out, "{} = {}", changed[0].0, changed[0].1)?;
            } else {
                for (name, value) in &changed {
                    writeln!(out, "/\\ {} = {}", name, value)?;
                }
            }
        }
    }
    Ok(())
}

/// Format a safety/deadlock trace in diff mode: only changed variables are shown
/// after the first state. Matches TLC's `-difftrace` behavior.
///
/// Part of #2470 Step 5.
pub(super) fn format_trace_difftrace(trace: &Trace) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let mut prev_state: Option<&tla_check::State> = None;
    let last_idx = trace.states.len().saturating_sub(1);

    for (i, state) in trace.states.iter().enumerate() {
        writeln!(
            out,
            "State {}: {}",
            i + 1,
            get_action_label(trace, i, i == 0)
        )
        .expect("invariant: fmt::Write for String is infallible");
        // TLC always shows all variables on the last state of a violation trace,
        // even in difftrace mode, so users can see the full violating state.
        let effective_prev = if i == last_idx { None } else { prev_state };
        write_state_vars(&mut out, state, effective_prev, true)
            .expect("invariant: fmt::Write for String is infallible");
        writeln!(out).expect("invariant: fmt::Write for String is infallible"); // blank line after state
        prev_state = Some(state);
    }

    out
}

/// Emit a safety/deadlock/invariant trace to stderr based on format and diff settings.
///
/// Only used for non-liveness traces (invariant, property, deadlock).
/// Liveness traces use their own format with prefix+cycle and different DOT output.
///
/// `dot_label` controls the DOT format header message (e.g. "Counterexample trace"
/// for invariant/property violations, "Trace to deadlock" for deadlocks).
pub(super) fn emit_trace(
    trace: &Trace,
    trace_format: TraceFormat,
    difftrace: bool,
    dot_label: &str,
) {
    match trace_format {
        TraceFormat::Text => {
            if difftrace {
                eprint!("{}", format_trace_difftrace(trace));
            } else {
                eprintln!("{}", trace);
            }
        }
        TraceFormat::Dot => {
            eprintln!("{} ({} states) in DOT format:", dot_label, trace.len());
            eprintln!();
            println!("{}", trace_to_dot(trace, None));
        }
        TraceFormat::Itf => {
            super::itf::emit_itf_trace(trace);
        }
    }
}

/// Emit a liveness trace to stderr based on format and diff settings.
pub(super) fn emit_liveness_trace(
    prefix: &Trace,
    cycle: &Trace,
    trace_format: TraceFormat,
    difftrace: bool,
) {
    match trace_format {
        TraceFormat::Text => {
            if difftrace {
                eprint!("{}", build_liveness_trace_difftrace(prefix, cycle));
            } else {
                format_liveness_trace_text(prefix, cycle);
            }
        }
        TraceFormat::Dot => {
            eprintln!("Counterexample (lasso shape) in DOT format:");
            eprintln!(
                "  Prefix: {} states, Cycle: {} states",
                prefix.len(),
                cycle.len()
            );
            eprintln!();
            println!("{}", liveness_trace_to_dot(prefix, cycle));
        }
        TraceFormat::Itf => {
            super::itf::emit_itf_liveness_trace(prefix, cycle);
        }
    }
}
