// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fmt::Write as _;
use std::io::{self, Write as _};
use std::time::Duration;

use crate::tlc_codes::{ec, mp};
use tla_check::{SearchCompleteness, Trace};

const DELIM: &str = "@!@!@";

fn start_tag(code: i32, class: i32) -> String {
    // Match TLC's MP.getMessage formatting:
    //   @!@!@STARTMSG <code>:<class> @!@!@
    format!("{DELIM}STARTMSG {code}:{class} {DELIM}")
}

fn end_tag(code: i32) -> String {
    // Match TLC's MP.getMessage formatting:
    //   @!@!@ENDMSG <code> @!@!@
    format!("{DELIM}ENDMSG {code} {DELIM}")
}

fn sanitize_body_for_toolbox(body: &str) -> String {
    // Avoid accidentally producing nested tags if a message line begins with "@!@!@".
    let mut out = String::with_capacity(body.len());
    for (idx, line) in body.split_inclusive('\n').enumerate() {
        let line = if idx == 0 {
            line
        } else {
            // `split_inclusive` keeps '\n' on each chunk; handle prefixes on the raw chunk.
            line
        };
        if line.starts_with(DELIM) {
            out.push(' ');
        }
        out.push_str(line);
    }
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

pub(crate) struct TlcToolOutput {
    stdout: io::Stdout,
}

impl TlcToolOutput {
    pub(crate) fn new() -> Self {
        Self {
            stdout: io::stdout(),
        }
    }

    pub(crate) fn emit(&mut self, code: i32, class: i32, body: &str) {
        let mut lock = self.stdout.lock();
        let _ = writeln!(lock, "{}", start_tag(code, class));
        let sanitized = sanitize_body_for_toolbox(body);
        let _ = write!(lock, "{sanitized}");
        let _ = writeln!(lock, "{}", end_tag(code));
        let _ = lock.flush();
    }
}

pub(crate) fn emit_check_tool_cli_error(
    file: &std::path::Path,
    config_path: Option<&std::path::Path>,
    workers: usize,
    completeness: SearchCompleteness,
    elapsed: Duration,
    msg: &str,
) -> ! {
    let mut out = TlcToolOutput::new();
    let mut body = String::new();
    let _ = writeln!(&mut body, "tla2 check failed.");
    let _ = writeln!(&mut body, "Spec: {}", file.display());
    if let Some(cfg) = config_path {
        let _ = writeln!(&mut body, "Config: {}", cfg.display());
    }
    let _ = writeln!(&mut body, "Workers: {workers}");
    let _ = writeln!(&mut body, "Completeness: {}", completeness.format_human());
    let _ = writeln!(&mut body, "Error: {msg}");
    out.emit(ec::GENERAL, mp::ERROR, &body);
    let now = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
    out.emit(
        ec::TLC_FINISHED,
        mp::NONE,
        &format_tlc_finished_message(elapsed, &now),
    );
    std::process::exit(2);
}

pub(crate) fn format_tlc_starting_message(now_utc: &str) -> String {
    format!("Starting... ({now_utc})")
}

pub(crate) fn format_tlc_finished_message(elapsed: Duration, now_utc: &str) -> String {
    format!("Finished in {}ms at ({now_utc})", elapsed.as_millis())
}

pub(crate) fn format_tlc_version_message() -> String {
    // Match TLC's MP.getMessage for EC.TLC_VERSION:
    //   "TLC2 %1%"
    format!("TLC2 tla2 {}", env!("CARGO_PKG_VERSION"))
}

pub(crate) fn format_tlc_sany_start_message() -> &'static str {
    // Match TLC's MP.getMessage for EC.TLC_SANY_START.
    "Starting SANY..."
}

pub(crate) fn format_tlc_sany_end_message() -> &'static str {
    // Match TLC's MP.getMessage for EC.TLC_SANY_END.
    "SANY finished."
}

pub(crate) fn format_tlc_computing_init_message() -> &'static str {
    // Match TLC's MP.getMessage for EC.TLC_COMPUTING_INIT.
    "Computing initial states..."
}

pub(crate) fn format_tlc_init_generated1_message(distinct_states: u64, now_utc: &str) -> String {
    // Match TLC's MP.getMessage for EC.TLC_INIT_GENERATED1:
    //   "Finished computing initial states: %1% distinct state%2% generated at <now>."
    let plural = if distinct_states == 1 { "" } else { "s" };
    format!(
        "Finished computing initial states: {distinct_states} distinct state{plural} generated at {now_utc}."
    )
}

pub(crate) fn format_tlc_progress_stats_message(
    diameter: u64,
    states_generated: u64,
    distinct_states: u64,
    left_on_queue: u64,
    now_utc: &str,
    elapsed_secs: f64,
) -> String {
    // Match TLC's MP.getMessage for EC.TLC_PROGRESS_STATS (new format with s/min metrics).
    // TLC emits: "Progress(N) at TIME: X states generated (Y s/min), Z distinct states found (W ds/min), Q states left on queue."
    // Fallback to parseOld format if elapsed_secs is zero (avoids division by zero).
    let elapsed_mins = elapsed_secs / 60.0;
    if elapsed_mins > 0.0 {
        let s_per_min = (states_generated as f64 / elapsed_mins).round() as u64;
        let ds_per_min = (distinct_states as f64 / elapsed_mins).round() as u64;
        format!(
            "Progress({diameter}) at {now_utc}: {states_generated} states generated ({s_per_min} s/min), {distinct_states} distinct states found ({ds_per_min} ds/min), {left_on_queue} states left on queue."
        )
    } else {
        // Old format (no s/min) when elapsed time is zero or negative
        format!(
            "Progress({diameter}) at {now_utc}: {states_generated} states generated, {distinct_states} distinct states found, {left_on_queue} states left on queue."
        )
    }
}

pub(crate) fn format_tlc_mode_message(workers: usize) -> String {
    // Match the Toolbox's strict startupMessagePattern so it can extract fp index.
    // Values are mostly placeholders; the parser is load-bearing, the numbers are not.
    let cores = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    let pid = std::process::id();
    format!(
        "Running breadth-first search Model-Checking with fp 0 and seed 0 with {workers} worker on {cores} cores with 0MB heap and 0MB offheap memory [pid: {pid}] (tla2)."
    )
}

pub(crate) fn format_tlc_success_message(collision_prob_str: &str) -> String {
    // Match Toolbox's collisionProbabilityPattern.
    // Part of #3005: collision probability now computed from CheckStats.
    format!(
        "Model checking completed. No error has been found.\n  \
         Estimates of the probability that TLC did not check all reachable states\n  \
         because two distinct states had the same fingerprint:\n  \
         calculated (optimistic):  val = {collision_prob_str}"
    )
}

pub(crate) fn format_tlc_stats_message(states_generated: u64, distinct_states: u64) -> String {
    format!(
        "{states_generated} states generated, {distinct_states} distinct states found, 0 states left on queue."
    )
}

pub(crate) fn format_tlc_depth_message(depth: u64) -> String {
    format!("The depth of the complete state graph search is {depth}.")
}

pub(crate) fn format_tlc_error_trace_intro() -> String {
    "The behavior up to this point is:".to_string()
}

fn format_tlc_state_body(index_1_based: usize, label: &str, state: &tla_check::State) -> String {
    let mut s = String::new();
    let _ = writeln!(&mut s, "{index_1_based}: {label}");
    for (name, value) in state.vars() {
        let _ = writeln!(&mut s, "/\\ {} = {}", name, value);
    }
    s
}

pub(crate) fn emit_tool_trace_states(out: &mut TlcToolOutput, trace: &Trace, fallback_label: &str) {
    for (idx, state) in trace.states.iter().enumerate() {
        let label = if let Some(action_label) = trace.action_labels.get(idx) {
            action_label.to_string()
        } else {
            fallback_label.to_string()
        };
        let body = format_tlc_state_body(idx + 1, &label, state);
        out.emit(ec::TLC_STATE_PRINT2, mp::STATE, &body);
    }
}

#[cfg(test)]
mod tests {
    use super::{end_tag, format_tlc_progress_stats_message, sanitize_body_for_toolbox, start_tag};

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn tags_match_tlc_format() {
        assert_eq!(start_tag(2185, 0), "@!@!@STARTMSG 2185:0 @!@!@");
        assert_eq!(end_tag(2185), "@!@!@ENDMSG 2185 @!@!@");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn sanitize_prefixes_delim_lines_and_ends_with_newline() {
        let body = "hello\n@!@!@ENDMSG 999 @!@!@\nbye";
        let out = sanitize_body_for_toolbox(body);
        assert!(out.starts_with("hello\n"));
        assert!(out.contains("\n @!@!@ENDMSG 999 @!@!@\n"));
        assert!(out.ends_with('\n'));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn progress_stats_includes_rates() {
        // Part of #1063: Progress format should include s/min and ds/min metrics.
        // Toolbox's StateSpaceInformationItem.parse() expects:
        //   "Progress(N) at TIME: X states generated (Y s/min), Z distinct ... (W ds/min), Q left"
        let msg = format_tlc_progress_stats_message(
            6,    // diameter
            1000, // states_generated
            900,  // distinct_states
            50,   // left_on_queue
            "2026-02-02 13:27:09",
            60.0, // elapsed_secs = 1 minute -> 1000 s/min, 900 ds/min
        );
        // Check new format markers that Toolbox parser looks for
        assert!(msg.contains(" s/min)"), "should include s/min rate");
        assert!(msg.contains(" ds/min)"), "should include ds/min rate");
        assert!(
            msg.contains("Progress(6) at "),
            "should have Progress(diameter)"
        );
        assert!(
            msg.contains("1000 states generated (1000 s/min)"),
            "should have correct s/min"
        );
        assert!(
            msg.contains("900 distinct states found (900 ds/min)"),
            "should have correct ds/min"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn progress_stats_zero_elapsed_uses_old_format() {
        // Part of #1063: When elapsed time is zero, use old format to avoid division by zero.
        let msg = format_tlc_progress_stats_message(1, 100, 100, 10, "2026-02-02 13:27:09", 0.0);
        // Old format has no s/min
        assert!(
            !msg.contains("s/min"),
            "zero elapsed should use old format without s/min"
        );
        assert!(
            msg.contains("100 states generated,"),
            "should have old format with comma"
        );
    }
}
