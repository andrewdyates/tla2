// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLC-tool format model-checking result reporting (Eclipse Toolbox compatible).

use anyhow::Result;
use tla_check::CheckResult;

use crate::tlc_codes;
use crate::tlc_tool;

use super::trace_format::property_violation_presentation;

/// Emit the common TLC stats + finished footer.
///
/// Every match arm in `report_check_tlc_tool` emits TLC_STATS + TLC_FINISHED.
/// This helper deduplicates that pattern. The optional `depth` parameter is
/// only emitted in the Success arm (TLC behavior).
fn emit_tlc_stats_footer(
    out: &mut tlc_tool::TlcToolOutput,
    stats: &tla_check::CheckStats,
    elapsed: std::time::Duration,
    depth: Option<u64>,
) {
    out.emit(
        tlc_codes::ec::TLC_STATS,
        tlc_codes::mp::NONE,
        &tlc_tool::format_tlc_stats_message(
            stats.states_generated() as u64,
            stats.states_found as u64,
        ),
    );
    if let Some(d) = depth {
        out.emit(
            tlc_codes::ec::TLC_SEARCH_DEPTH,
            tlc_codes::mp::NONE,
            &tlc_tool::format_tlc_depth_message(d),
        );
    }
    let now = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
    out.emit(
        tlc_codes::ec::TLC_FINISHED,
        tlc_codes::mp::NONE,
        &tlc_tool::format_tlc_finished_message(elapsed, &now),
    );
}

/// Report model checking results in TLC-tool format (Eclipse Toolbox compatible).
pub(crate) fn report_check_tlc_tool(
    tool_out: Option<tlc_tool::TlcToolOutput>,
    result: &CheckResult,
    elapsed: std::time::Duration,
) -> Result<()> {
    let mut out = tool_out.unwrap_or_else(tlc_tool::TlcToolOutput::new);

    match result {
        CheckResult::Success(stats) => {
            out.emit(
                tlc_codes::ec::TLC_SUCCESS,
                tlc_codes::mp::NONE,
                &tlc_tool::format_tlc_success_message(&stats.collision_probability_string()),
            );
            emit_tlc_stats_footer(&mut out, stats, elapsed, Some(stats.max_depth as u64));
            std::process::exit(0);
        }
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            out.emit(
                tlc_codes::ec::TLC_INVARIANT_VIOLATED_BEHAVIOR,
                tlc_codes::mp::ERROR,
                &format!("Invariant {invariant} is violated."),
            );
            out.emit(
                tlc_codes::ec::TLC_BEHAVIOR_UP_TO_THIS_POINT,
                tlc_codes::mp::ERROR,
                &tlc_tool::format_tlc_error_trace_intro(),
            );
            if !trace.is_empty() {
                tlc_tool::emit_tool_trace_states(&mut out, trace, "<State>");
            }
            emit_tlc_stats_footer(&mut out, stats, elapsed, None);
            std::process::exit(1);
        }
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats,
        } => {
            let presentation = property_violation_presentation(property.as_str(), *kind);
            out.emit(
                presentation.tlc_code,
                tlc_codes::mp::ERROR,
                &presentation.headline,
            );
            out.emit(
                tlc_codes::ec::TLC_BEHAVIOR_UP_TO_THIS_POINT,
                tlc_codes::mp::ERROR,
                presentation.trace_intro,
            );
            if !trace.is_empty() {
                tlc_tool::emit_tool_trace_states(&mut out, trace, "<State>");
            }
            emit_tlc_stats_footer(&mut out, stats, elapsed, None);
            std::process::exit(1);
        }
        CheckResult::LivenessViolation {
            property: _,
            prefix,
            cycle,
            stats,
        } => {
            out.emit(
                tlc_codes::ec::TLC_TEMPORAL_PROPERTY_VIOLATED,
                tlc_codes::mp::ERROR,
                "Temporal properties were violated.",
            );
            out.emit(
                tlc_codes::ec::TLC_COUNTER_EXAMPLE,
                tlc_codes::mp::ERROR,
                "The following behavior constitutes a counter-example:",
            );
            if !prefix.is_empty() {
                tlc_tool::emit_tool_trace_states(&mut out, prefix, "<State>");
            }
            if !cycle.is_empty() {
                tlc_tool::emit_tool_trace_states(&mut out, cycle, "<State>");
            }
            emit_tlc_stats_footer(&mut out, stats, elapsed, None);
            std::process::exit(1);
        }
        CheckResult::Deadlock { trace, stats } => {
            out.emit(
                tlc_codes::ec::TLC_DEADLOCK_REACHED,
                tlc_codes::mp::ERROR,
                "Deadlock reached.",
            );
            out.emit(
                tlc_codes::ec::TLC_BEHAVIOR_UP_TO_THIS_POINT,
                tlc_codes::mp::ERROR,
                &tlc_tool::format_tlc_error_trace_intro(),
            );
            if !trace.is_empty() {
                tlc_tool::emit_tool_trace_states(&mut out, trace, "<State>");
            }
            emit_tlc_stats_footer(&mut out, stats, elapsed, None);
            std::process::exit(1);
        }
        CheckResult::LimitReached { stats, .. } => {
            out.emit(
                tlc_codes::ec::GENERAL,
                tlc_codes::mp::WARNING,
                "Model checking stopped: exploration limit reached.",
            );
            emit_tlc_stats_footer(&mut out, stats, elapsed, None);
            std::process::exit(0);
        }
        CheckResult::Error { error, stats, .. } => {
            out.emit(
                tlc_codes::ec::GENERAL,
                tlc_codes::mp::ERROR,
                &format!("Model checking failed: {error}"),
            );
            emit_tlc_stats_footer(&mut out, stats, elapsed, None);
            std::process::exit(1);
        }
        _ => {
            out.emit(
                tlc_codes::ec::GENERAL,
                tlc_codes::mp::TLCBUG,
                "Unsupported model checking result variant; upgrade tla2.",
            );
            std::process::exit(2);
        }
    }
}
