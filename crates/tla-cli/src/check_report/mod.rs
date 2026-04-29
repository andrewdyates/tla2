// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Model-checking result reporting in JSON, TLC-tool, and human-readable formats.

mod human;
pub(crate) mod itf;
mod json_report;
mod tlc_tool_report;
pub(crate) mod trace_format;
pub(crate) mod vmt;
mod vmt_sort;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod vmt_tests;

use tla_check::StorageStats;

pub(crate) use human::report_check_human;
pub(crate) use itf::report_check_itf;
pub(crate) use json_report::{report_check_json, JsonReportCtx};
pub(crate) use tlc_tool_report::report_check_tlc_tool;

/// Format max_states/max_depth bounds as a human-readable string.
pub(crate) fn format_configured_bounds(max_states: usize, max_depth: usize) -> Option<String> {
    if max_states == 0 && max_depth == 0 {
        return None;
    }
    Some(match (max_states, max_depth) {
        (0, 0) => unreachable!(),
        (0, d) => format!("max_depth={}", d),
        (s, 0) => format!("max_states={}", s),
        (s, d) => format!("max_states={}, max_depth={}", s, d),
    })
}

/// Format a warning suffix for state-count lines when guard errors were suppressed.
pub(crate) fn format_guard_suppression_suffix(suppressed_guard_errors: usize) -> String {
    if suppressed_guard_errors == 0 {
        return String::new();
    }
    format!(
        " (WARNING: {} guard errors suppressed; state count may be incorrect)",
        suppressed_guard_errors
    )
}

fn format_count(value: u64) -> String {
    let digits = value.to_string();
    let first_group = digits.len() % 3;
    let mut formatted = String::with_capacity(digits.len() + digits.len() / 3);
    let mut idx = 0;

    if first_group != 0 {
        formatted.push_str(&digits[..first_group]);
        idx = first_group;
        if idx < digits.len() {
            formatted.push(',');
        }
    }

    while idx < digits.len() {
        formatted.push_str(&digits[idx..idx + 3]);
        idx += 3;
        if idx < digits.len() {
            formatted.push(',');
        }
    }

    formatted
}

fn format_bytecode_vm_stats_line(stats: (u64, u64, u64)) -> String {
    let (executions, fallbacks, compile_failures) = stats;
    format!(
        "Bytecode VM: {} executions, {} fallbacks, {} compile failures",
        format_count(executions),
        format_count(fallbacks),
        format_count(compile_failures)
    )
}

fn bytecode_vm_stats_line() -> Option<String> {
    match std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() {
        Ok("1") => Some(format_bytecode_vm_stats_line(
            tla_check::aggregate_bytecode_vm_stats(),
        )),
        _ => None,
    }
}

/// Print storage backend statistics when non-trivial.
///
/// Only prints when there is something interesting to report — disk storage,
/// evictions, or reserved memory from mmap-backed storage. Pure in-memory runs
/// with small state spaces produce no output.
///
/// Part of #2665.
fn storage_stats_lines(stats: &StorageStats) -> Option<Vec<String>> {
    if stats.disk_count == 0
        && stats.eviction_count == 0
        && stats.disk_lookups == 0
        && stats.memory_bytes == 0
    {
        return None;
    }

    let mut lines = vec![
        String::new(),
        "Storage:".to_string(),
        format!("  Memory states: {}", stats.memory_count),
        format!("  Disk states: {}", stats.disk_count),
    ];
    if stats.memory_bytes > 0 {
        let mb = stats.memory_bytes as f64 / (1024.0 * 1024.0);
        lines.push(format!("  Memory reserved: {:.1} MB", mb));
    }
    if stats.disk_lookups > 0 {
        let hit_rate = 100.0 * stats.disk_hits as f64 / stats.disk_lookups as f64;
        lines.push(format!(
            "  Disk lookups: {} ({} hits, {:.1}% hit rate)",
            stats.disk_lookups, stats.disk_hits, hit_rate
        ));
    }
    if stats.eviction_count > 0 {
        lines.push(format!("  Evictions: {}", stats.eviction_count));
    }
    Some(lines)
}

fn print_storage_stats(stats: &StorageStats, to_stderr: bool) {
    let Some(lines) = storage_stats_lines(stats) else {
        return;
    };

    for line in lines {
        if to_stderr {
            eprintln!("{line}");
        } else {
            println!("{line}");
        }
    }
}
