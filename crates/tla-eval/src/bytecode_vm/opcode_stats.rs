// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Opcode execution-frequency counters for the bytecode VM.
//!
//! Counts are kept thread-locally on the hot path and merged into global
//! atomics when a worker exits or explicitly flushes at run finalization.

use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};

use tla_tir::bytecode::{Opcode, OpcodeCategory};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct OpcodeStats {
    pub arithmetic: u64,
    pub comparison: u64,
    pub logic: u64,
    pub control_flow: u64,
    pub state_access: u64,
    pub set_ops: u64,
    pub quantifier: u64,
    pub func_record: u64,
    pub call: u64,
    pub other: u64,
}

impl OpcodeStats {
    #[must_use]
    pub const fn total(self) -> u64 {
        self.arithmetic
            + self.comparison
            + self.logic
            + self.control_flow
            + self.state_access
            + self.set_ops
            + self.quantifier
            + self.func_record
            + self.call
            + self.other
    }

    #[must_use]
    pub const fn count_for(self, category: OpcodeCategory) -> u64 {
        match category {
            OpcodeCategory::Arithmetic => self.arithmetic,
            OpcodeCategory::Comparison => self.comparison,
            OpcodeCategory::Logic => self.logic,
            OpcodeCategory::ControlFlow => self.control_flow,
            OpcodeCategory::StateAccess => self.state_access,
            OpcodeCategory::SetOps => self.set_ops,
            OpcodeCategory::Quantifier => self.quantifier,
            OpcodeCategory::FuncRecord => self.func_record,
            OpcodeCategory::Call => self.call,
            OpcodeCategory::Other => self.other,
        }
    }

    fn add_assign(&mut self, other: Self) {
        self.arithmetic = self.arithmetic.saturating_add(other.arithmetic);
        self.comparison = self.comparison.saturating_add(other.comparison);
        self.logic = self.logic.saturating_add(other.logic);
        self.control_flow = self.control_flow.saturating_add(other.control_flow);
        self.state_access = self.state_access.saturating_add(other.state_access);
        self.set_ops = self.set_ops.saturating_add(other.set_ops);
        self.quantifier = self.quantifier.saturating_add(other.quantifier);
        self.func_record = self.func_record.saturating_add(other.func_record);
        self.call = self.call.saturating_add(other.call);
        self.other = self.other.saturating_add(other.other);
    }
}

struct LocalOpcodeStats {
    arithmetic: Cell<u64>,
    comparison: Cell<u64>,
    logic: Cell<u64>,
    control_flow: Cell<u64>,
    state_access: Cell<u64>,
    set_ops: Cell<u64>,
    quantifier: Cell<u64>,
    func_record: Cell<u64>,
    call: Cell<u64>,
    other: Cell<u64>,
}

impl LocalOpcodeStats {
    const fn new() -> Self {
        Self {
            arithmetic: Cell::new(0),
            comparison: Cell::new(0),
            logic: Cell::new(0),
            control_flow: Cell::new(0),
            state_access: Cell::new(0),
            set_ops: Cell::new(0),
            quantifier: Cell::new(0),
            func_record: Cell::new(0),
            call: Cell::new(0),
            other: Cell::new(0),
        }
    }

    fn increment(&self, category: OpcodeCategory) {
        let cell = match category {
            OpcodeCategory::Arithmetic => &self.arithmetic,
            OpcodeCategory::Comparison => &self.comparison,
            OpcodeCategory::Logic => &self.logic,
            OpcodeCategory::ControlFlow => &self.control_flow,
            OpcodeCategory::StateAccess => &self.state_access,
            OpcodeCategory::SetOps => &self.set_ops,
            OpcodeCategory::Quantifier => &self.quantifier,
            OpcodeCategory::FuncRecord => &self.func_record,
            OpcodeCategory::Call => &self.call,
            OpcodeCategory::Other => &self.other,
        };
        cell.set(cell.get().saturating_add(1));
    }

    fn snapshot(&self) -> OpcodeStats {
        OpcodeStats {
            arithmetic: self.arithmetic.get(),
            comparison: self.comparison.get(),
            logic: self.logic.get(),
            control_flow: self.control_flow.get(),
            state_access: self.state_access.get(),
            set_ops: self.set_ops.get(),
            quantifier: self.quantifier.get(),
            func_record: self.func_record.get(),
            call: self.call.get(),
            other: self.other.get(),
        }
    }

    fn drain(&self) -> OpcodeStats {
        OpcodeStats {
            arithmetic: self.arithmetic.replace(0),
            comparison: self.comparison.replace(0),
            logic: self.logic.replace(0),
            control_flow: self.control_flow.replace(0),
            state_access: self.state_access.replace(0),
            set_ops: self.set_ops.replace(0),
            quantifier: self.quantifier.replace(0),
            func_record: self.func_record.replace(0),
            call: self.call.replace(0),
            other: self.other.replace(0),
        }
    }

    fn clear(&self) {
        let _ = self.drain();
    }
}

struct GlobalOpcodeStats {
    arithmetic: AtomicU64,
    comparison: AtomicU64,
    logic: AtomicU64,
    control_flow: AtomicU64,
    state_access: AtomicU64,
    set_ops: AtomicU64,
    quantifier: AtomicU64,
    func_record: AtomicU64,
    call: AtomicU64,
    other: AtomicU64,
}

impl GlobalOpcodeStats {
    const fn new() -> Self {
        Self {
            arithmetic: AtomicU64::new(0),
            comparison: AtomicU64::new(0),
            logic: AtomicU64::new(0),
            control_flow: AtomicU64::new(0),
            state_access: AtomicU64::new(0),
            set_ops: AtomicU64::new(0),
            quantifier: AtomicU64::new(0),
            func_record: AtomicU64::new(0),
            call: AtomicU64::new(0),
            other: AtomicU64::new(0),
        }
    }

    fn add(&self, stats: OpcodeStats) {
        self.arithmetic
            .fetch_add(stats.arithmetic, Ordering::Relaxed);
        self.comparison
            .fetch_add(stats.comparison, Ordering::Relaxed);
        self.logic.fetch_add(stats.logic, Ordering::Relaxed);
        self.control_flow
            .fetch_add(stats.control_flow, Ordering::Relaxed);
        self.state_access
            .fetch_add(stats.state_access, Ordering::Relaxed);
        self.set_ops.fetch_add(stats.set_ops, Ordering::Relaxed);
        self.quantifier
            .fetch_add(stats.quantifier, Ordering::Relaxed);
        self.func_record
            .fetch_add(stats.func_record, Ordering::Relaxed);
        self.call.fetch_add(stats.call, Ordering::Relaxed);
        self.other.fetch_add(stats.other, Ordering::Relaxed);
    }

    fn snapshot(&self) -> OpcodeStats {
        OpcodeStats {
            arithmetic: self.arithmetic.load(Ordering::Relaxed),
            comparison: self.comparison.load(Ordering::Relaxed),
            logic: self.logic.load(Ordering::Relaxed),
            control_flow: self.control_flow.load(Ordering::Relaxed),
            state_access: self.state_access.load(Ordering::Relaxed),
            set_ops: self.set_ops.load(Ordering::Relaxed),
            quantifier: self.quantifier.load(Ordering::Relaxed),
            func_record: self.func_record.load(Ordering::Relaxed),
            call: self.call.load(Ordering::Relaxed),
            other: self.other.load(Ordering::Relaxed),
        }
    }

    fn clear(&self) {
        self.arithmetic.store(0, Ordering::Relaxed);
        self.comparison.store(0, Ordering::Relaxed);
        self.logic.store(0, Ordering::Relaxed);
        self.control_flow.store(0, Ordering::Relaxed);
        self.state_access.store(0, Ordering::Relaxed);
        self.set_ops.store(0, Ordering::Relaxed);
        self.quantifier.store(0, Ordering::Relaxed);
        self.func_record.store(0, Ordering::Relaxed);
        self.call.store(0, Ordering::Relaxed);
        self.other.store(0, Ordering::Relaxed);
    }
}

static GLOBAL_OPCODE_STATS: GlobalOpcodeStats = GlobalOpcodeStats::new();

thread_local! {
    static OPCODE_STATS_ENABLED: Cell<Option<bool>> = const { Cell::new(None) };
    static OPCODE_STATS_ENABLED_OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
    static LOCAL_OPCODE_STATS: LocalOpcodeStats = const { LocalOpcodeStats::new() };
}

fn parse_opcode_stats_enabled(value: Option<&str>) -> bool {
    matches!(value, Some("1"))
}

/// Whether opcode execution stats are enabled for the current thread.
pub fn opcode_stats_enabled() -> bool {
    if let Some(enabled) = OPCODE_STATS_ENABLED_OVERRIDE.with(Cell::get) {
        return enabled;
    }
    OPCODE_STATS_ENABLED.with(|cached| {
        if let Some(enabled) = cached.get() {
            return enabled;
        }
        let enabled =
            parse_opcode_stats_enabled(std::env::var("TLA2_OPCODE_STATS").ok().as_deref());
        cached.set(Some(enabled));
        enabled
    })
}

#[inline(always)]
pub(crate) fn record_opcode_execution(opcode: &Opcode) {
    LOCAL_OPCODE_STATS.with(|stats| stats.increment(opcode.category()));
}

/// Return the current thread's unmerged opcode counters.
#[must_use]
pub fn opcode_stats() -> OpcodeStats {
    LOCAL_OPCODE_STATS.with(LocalOpcodeStats::snapshot)
}

/// Merge the current thread's counters into the process-global totals.
pub fn merge_opcode_stats_current_thread() {
    let drained = LOCAL_OPCODE_STATS.with(LocalOpcodeStats::drain);
    if drained.total() > 0 {
        GLOBAL_OPCODE_STATS.add(drained);
    }
}

/// Return opcode counters aggregated across all flushed threads plus the current thread.
#[must_use]
pub fn aggregate_opcode_stats() -> OpcodeStats {
    let mut total = GLOBAL_OPCODE_STATS.snapshot();
    total.add_assign(opcode_stats());
    total
}

pub(crate) fn clear_opcode_stats() {
    OPCODE_STATS_ENABLED.with(|cached| cached.set(None));
    LOCAL_OPCODE_STATS.with(LocalOpcodeStats::clear);
    GLOBAL_OPCODE_STATS.clear();
}

pub fn print_opcode_stats_summary() {
    if !opcode_stats_enabled() {
        return;
    }

    let stats = aggregate_opcode_stats();
    let total = stats.total();

    eprintln!("\n=== Bytecode Opcode Stats ===");
    eprintln!(
        "{:<18} {:>16} {:>21}",
        "opcode_category", "count", "percentage_of_total"
    );
    for category in OpcodeCategory::ALL {
        let count = stats.count_for(category);
        let pct = if total > 0 {
            count as f64 * 100.0 / total as f64
        } else {
            0.0
        };
        eprintln!("{:<18} {:>16} {:>20.2}%", category.as_str(), count, pct);
    }
    eprintln!("{:<18} {:>16}", "total", total);
}

#[cfg(test)]
pub(crate) struct OpcodeStatsTestOverrideGuard {
    previous_override: Option<bool>,
}

#[cfg(test)]
pub(crate) fn set_opcode_stats_test_override(
    enabled: Option<bool>,
) -> OpcodeStatsTestOverrideGuard {
    let previous_override = OPCODE_STATS_ENABLED_OVERRIDE.with(|cached| {
        let previous = cached.get();
        cached.set(enabled);
        previous
    });
    OPCODE_STATS_ENABLED.with(|cached| cached.set(None));
    OpcodeStatsTestOverrideGuard { previous_override }
}

#[cfg(test)]
impl Drop for OpcodeStatsTestOverrideGuard {
    fn drop(&mut self) {
        OPCODE_STATS_ENABLED_OVERRIDE.with(|cached| cached.set(self.previous_override));
        OPCODE_STATS_ENABLED.with(|cached| cached.set(None));
    }
}
