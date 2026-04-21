// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Split out of `check/mod.rs` to keep the module navigable.

mod stats;
mod trace;

pub use self::stats::{
    CheckStats, InitProgress, InitProgressCallback, PorReductionStats, Progress,
    ProgressCallback, SymmetryReductionStats,
};
pub(crate) use self::trace::INLINE_NEXT_NAME;
pub use self::trace::{ActionLabel, Trace};

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::spec_formula::FairnessConstraint;
use crate::storage::StorageStats;
use tla_core::ast::Expr;
use tla_core::span::Span;
use tla_core::{Spanned, SyntaxNode};

/// Distinguishes the origin of a PROPERTY violation for TLC-parity error messages.
///
/// TLC reports state-level `[]P` property violations with invariant-style wording
/// ("Invariant X is violated."), while action-level `[][A]_v` violations use
/// "Action property X is violated.".
///
/// Part of #2676.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyViolationKind {
    /// State-level `[]P` from PROPERTY (promoted to BFS invariant checking or
    /// checked in post-BFS safety temporal pass). TLC reports these as
    /// "Invariant X is violated.".
    StateLevel,
    /// Action-level `[][A]_v` from PROPERTY (implied action checking).
    /// TLC reports these as "Action property X is violated."
    ActionLevel,
}

/// Zero-sized token that prevents direct construction of `CheckResult::Error`
/// outside this module. All error construction must go through
/// `check_error_to_result()`, which gates `ExitRequested` → `LimitReached`.
///
/// Part of #2851: compile-time enforcement of error construction gating.
#[derive(Debug, Clone, Copy)]
pub struct ErrorToken(());

/// Result of model checking
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CheckResult {
    /// All reachable states satisfy all invariants
    Success(CheckStats),
    /// An invariant was violated
    InvariantViolation {
        invariant: String,
        trace: Trace,
        stats: CheckStats,
    },
    /// A temporal property was violated by a finite trace
    ///
    /// This is used for safety-style temporal properties (e.g., Init /\ []Action)
    /// that can be checked without the full liveness tableau algorithm.
    PropertyViolation {
        property: String,
        kind: PropertyViolationKind,
        trace: Trace,
        stats: CheckStats,
    },
    /// A liveness property was violated
    LivenessViolation {
        /// The property that was violated
        property: String,
        /// Prefix of the counterexample (finite path to the cycle)
        prefix: Trace,
        /// The cycle itself (lasso)
        cycle: Trace,
        /// Statistics
        stats: CheckStats,
    },
    /// Deadlock detected (state with no successors, if deadlock checking enabled)
    Deadlock { trace: Trace, stats: CheckStats },
    /// Error during checking (evaluation error, missing definition, etc.)
    ///
    /// The `_token` field prevents direct construction outside `api.rs`.
    /// Use `check_error_to_result()` to construct this variant.
    /// Part of #2851.
    Error {
        error: CheckError,
        stats: CheckStats,
        /// Private token preventing direct construction. Use `check_error_to_result()`.
        _token: ErrorToken,
    },
    /// Exploration limit reached (state or depth limit)
    LimitReached {
        /// Which limit was hit
        limit_type: LimitType,
        /// Statistics at the time limit was reached
        stats: CheckStats,
    },
}

impl CheckResult {
    /// Construct an error result while preserving ExitRequested -> LimitReached gating.
    #[must_use]
    pub fn from_error(error: CheckError, stats: CheckStats) -> Self {
        if let CheckError::Eval(EvalCheckError::Eval(EvalError::ExitRequested { .. })) = &error {
            CheckResult::LimitReached {
                limit_type: LimitType::Exit,
                stats,
            }
        } else {
            CheckResult::Error {
                error,
                stats,
                _token: ErrorToken(()),
            }
        }
    }

    /// Borrow terminal statistics regardless of result variant.
    #[must_use]
    pub fn stats(&self) -> &CheckStats {
        match self {
            CheckResult::Success(stats)
            | CheckResult::InvariantViolation { stats, .. }
            | CheckResult::PropertyViolation { stats, .. }
            | CheckResult::LivenessViolation { stats, .. }
            | CheckResult::Deadlock { stats, .. }
            | CheckResult::Error { stats, .. }
            | CheckResult::LimitReached { stats, .. } => stats,
        }
    }

    fn stats_mut(&mut self) -> &mut CheckStats {
        match self {
            CheckResult::Success(stats)
            | CheckResult::InvariantViolation { stats, .. }
            | CheckResult::PropertyViolation { stats, .. }
            | CheckResult::LivenessViolation { stats, .. }
            | CheckResult::Deadlock { stats, .. }
            | CheckResult::Error { stats, .. }
            | CheckResult::LimitReached { stats, .. } => stats,
        }
    }

    /// Attach fingerprint-storage backend counters to this result.
    #[must_use]
    pub(crate) fn with_storage_stats(mut self, storage_stats: StorageStats) -> Self {
        self.stats_mut().storage_stats = storage_stats;
        self
    }

    /// Attach the number of suppressed guard-evaluation errors to this result.
    #[must_use]
    pub(crate) fn with_suppressed_guard_errors(mut self, suppressed_count: usize) -> Self {
        if suppressed_count > 0 {
            self.stats_mut().suppressed_guard_errors = suppressed_count;
        }
        self
    }

    /// Number of guard-evaluation errors suppressed during this run.
    #[must_use]
    pub(crate) fn suppressed_guard_errors(&self) -> usize {
        self.stats().suppressed_guard_errors
    }

    /// Apply ALIAS transformation to all traces in this result.
    ///
    /// When a config specifies `ALIAS AliasOp`, TLC evaluates `AliasOp` for each
    /// state in counterexample traces, replacing raw state variables with the
    /// ALIAS result (which should be a record). This method applies the same
    /// transformation to all traces in the result.
    ///
    /// Part of #3012.
    pub fn apply_alias(self, ctx: &mut EvalCtx, alias_name: &str) -> Self {
        match self {
            CheckResult::InvariantViolation {
                invariant,
                trace,
                stats,
            } => CheckResult::InvariantViolation {
                invariant,
                trace: trace.apply_alias(ctx, alias_name),
                stats,
            },
            CheckResult::PropertyViolation {
                property,
                kind,
                trace,
                stats,
            } => CheckResult::PropertyViolation {
                property,
                kind,
                trace: trace.apply_alias(ctx, alias_name),
                stats,
            },
            CheckResult::LivenessViolation {
                property,
                prefix,
                cycle,
                stats,
            } => CheckResult::LivenessViolation {
                property,
                prefix: prefix.apply_alias(ctx, alias_name),
                cycle: cycle.apply_alias(ctx, alias_name),
                stats,
            },
            CheckResult::Deadlock { trace, stats } => CheckResult::Deadlock {
                trace: trace.apply_alias(ctx, alias_name),
                stats,
            },
            // Success, Error, LimitReached have no traces.
            other => other,
        }
    }
}

/// Type of exploration limit that was reached
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum LimitType {
    /// Maximum states limit was reached
    States,
    /// Maximum depth limit was reached
    Depth,
    /// TLCSet("exit", TRUE) was called - spec requested early termination
    /// Part of #254: Animation and export specs use this for bounded exploration.
    Exit,
    /// Process RSS exceeded the configured memory limit.
    /// Part of #2751 Phase 3: graceful stop on memory pressure.
    Memory,
    /// Disk usage exceeded the configured disk budget.
    /// Part of #3282: resource budget enforcement for disk-backed storage.
    Disk,
}

/// Result of successor generation with information about constraint filtering.
///
/// TLC semantics: A state at the "edge" of the constrained state space (where all
/// successors violate state constraints) is NOT considered a deadlock. Only states
/// with truly no successors (before constraint filtering) are deadlocks.
pub(super) struct SuccessorResult<T> {
    /// The successors after filtering by state/action constraints
    pub(super) successors: T,
    /// True if there were any successors before constraint filtering.
    /// Used for deadlock detection: deadlock only if this is false AND successors is empty.
    pub(super) had_raw_successors: bool,
}

pub(super) enum SafetyTemporalPropertyOutcome {
    NotApplicable,
    Satisfied,
    Violated(Box<CheckResult>),
}

/// Safety parts extracted from a mixed safety/liveness property.
///
/// Used by `separate_safety_liveness_parts` to split properties like
/// `Init /\ [][Next]_vars /\ Liveness` into checkable parts.
pub(super) struct PropertySafetyParts {
    /// Init-level terms (checked on initial states)
    pub(super) init_terms: Vec<Spanned<Expr>>,
    /// Always-action terms (checked on transitions): body of `[]Action` where Action has no temporal
    pub(super) always_terms: Vec<Spanned<Expr>>,
}

// CheckError is now defined in check_error.rs (Part of #2651: decomposed into sub-enums).
// Re-exported through mod.rs as `pub use self::check_error::CheckError`.
use super::check_error::{CheckError, EvalCheckError};

/// Convert a CheckError to the appropriate CheckResult.
///
/// Part of #254: If the CheckError wraps an `ExitRequested`, convert to
/// `LimitReached` for graceful early termination. Otherwise, return as error.
pub(crate) fn check_error_to_result(e: CheckError, stats: &CheckStats) -> CheckResult {
    CheckResult::from_error(e, stats.clone())
}

/// Format a Span's location for error reporting
///
/// Returns a string like "bytes 123-456 of module M" for user-facing error messages.
///
/// TLC typically prints "line X, col Y to line X2, col Y2 of module M". When we don't have
/// a source-text mapping available at the call site, we fall back to byte offsets here.
pub(crate) fn format_span_location(span: &Span, module_name: &str) -> String {
    format!(
        "bytes {}-{} of module {}",
        span.start, span.end, module_name
    )
}

/// Format a Span's location in TLC's default "line/col range" style.
///
/// This requires the original source text to convert byte offsets to line/column.
/// Returns a string like:
/// `line 3, col 1 to line 4, col 12 of module Foo`
pub(crate) fn format_span_location_from_source(
    span: &Span,
    module_name: &str,
    source: &str,
) -> String {
    fn clamp_to_char_boundary(s: &str, mut idx: usize) -> usize {
        idx = idx.min(s.len());
        while idx > 0 && !s.is_char_boundary(idx) {
            idx -= 1;
        }
        idx
    }

    fn byte_offset_to_line_col(source: &str, byte_offset: usize) -> (usize, usize) {
        let byte_offset = clamp_to_char_boundary(source, byte_offset);
        let mut line = 1usize;
        let mut line_start = 0usize;

        for (idx, ch) in source.char_indices() {
            if idx >= byte_offset {
                break;
            }
            if ch == '\n' {
                line += 1;
                line_start = idx + 1;
            }
        }

        let col = source[line_start..byte_offset].chars().count() + 1;
        (line, col)
    }

    let start = clamp_to_char_boundary(source, span.start as usize);
    // TLC's end column appears to be inclusive. Our spans are end-exclusive, so map to end-1
    // when possible (and fall back to end for empty spans).
    let inclusive_end = if span.end > span.start {
        clamp_to_char_boundary(source, (span.end as usize).saturating_sub(1))
    } else {
        clamp_to_char_boundary(source, span.end as usize)
    };

    let (start_line, start_col) = byte_offset_to_line_col(source, start);
    let (end_line, end_col) = byte_offset_to_line_col(source, inclusive_end);

    format!(
        "line {}, col {} to line {}, col {} of module {}",
        start_line, start_col, end_line, end_col, module_name
    )
}

#[cfg(test)]
mod format_span_location_from_source_tests {
    use super::*;
    use tla_core::FileId;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn single_line_inclusive_end() {
        let source = "abc def\n";
        let span = Span::new(FileId(0), 4, 7); // "def"
        assert_eq!(
            format_span_location_from_source(&span, "Foo", source),
            "line 1, col 5 to line 1, col 7 of module Foo"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn multi_line_range() {
        let source = "a\nbc\ndef\n";
        let span = Span::new(FileId(0), 2, 8); // "bc\ndef"
        assert_eq!(
            format_span_location_from_source(&span, "Foo", source),
            "line 2, col 1 to line 3, col 3 of module Foo"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn utf8_non_boundary_end_is_clamped() {
        let source = "aé\n";
        // end-exclusive points at the '\n' boundary; inclusive_end will be end-1 which is not a
        // UTF-8 boundary for 'é'. Clamp to avoid panicking and keep a stable range.
        let span = Span::new(FileId(0), 1, 3);
        assert_eq!(
            format_span_location_from_source(&span, "Foo", source),
            "line 1, col 2 to line 1, col 2 of module Foo"
        );
    }
}

#[cfg(test)]
mod check_result_stats_tests {
    use super::*;

    #[test]
    fn with_suppressed_guard_errors_updates_success_stats() {
        let result = CheckResult::Success(CheckStats::default()).with_suppressed_guard_errors(3);
        assert_eq!(result.suppressed_guard_errors(), 3);
    }

    #[test]
    fn with_suppressed_guard_errors_updates_error_stats() {
        let result = CheckResult::Error {
            error: crate::ConfigCheckError::Setup("boom".to_string()).into(),
            stats: CheckStats::default(),
            _token: ErrorToken(()),
        }
        .with_suppressed_guard_errors(2);
        assert_eq!(result.suppressed_guard_errors(), 2);
    }
}

/// TLC-shaped liveness conversion failure message (EC 2213).
///
/// Centralize formatting so call sites don't diverge on prefixes, newlines, or location strings.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TlcLiveCannotHandleFormulaMsg<'a> {
    pub(crate) location: &'a str,
    pub(crate) reason: Option<&'a str>,
}

impl std::fmt::Display for TlcLiveCannotHandleFormulaMsg<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.reason {
            Some(reason) => write!(
                f,
                "TLC cannot handle the temporal formula {}:\n{}",
                self.location, reason
            ),
            None => write!(
                f,
                "TLC cannot handle the temporal formula {}",
                self.location
            ),
        }
    }
}

/// Resolved Init and Next names from config (either direct or via SPECIFICATION)
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ResolvedSpec {
    /// Init predicate name
    pub init: String,
    /// Next relation name (may be an operator name or an inline expression text)
    pub next: String,
    /// The syntax node for inline NEXT expressions (e.g., `\E n \in Node: Next(n)`)
    /// When present, the checker should create a synthetic operator from this node.
    pub next_node: Option<SyntaxNode>,
    /// Fairness constraints extracted from SPEC formula (if any)
    pub fairness: Vec<FairnessConstraint>,
    /// Whether the spec uses `[A]_v` form (stuttering allowed) or `<<A>>_v` form (stuttering forbidden).
    ///
    /// Note: deadlock checking is a model-checker option (`CHECK_DEADLOCK`), and is not implicitly
    /// disabled just because the spec uses `[A]_v` stuttering form.
    ///
    /// Defaults to `true` (stuttering allowed), which is the most common TLA+ pattern.
    pub stuttering_allowed: bool,
}
