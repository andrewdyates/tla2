// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error classification for enumeration paths.
//!
//! Centralizes the policy for which `EvalError` variants indicate:
//! - action-level constructs (primed variables / UNCHANGED) vs guards
//! - disabled actions in conjunction-guard contexts
//! - speculative fallback (unresolved references during speculative eval)
//! - iter-domain deferral vs fatal errors
//!
//! Extracted from enumerate.rs (Part of #2418).

use crate::error::EvalError;

/// Check if an error indicates the expression contains action-level constructs
/// (primed variables or UNCHANGED) that can't be evaluated as a guard.
///
/// These errors are expected during guard evaluation when the expression being
/// checked is actually an action (assignment) rather than a guard.
///
/// Fix #1891: Uses typed error variants instead of fragile string matching on
/// Internal error messages.
pub(crate) fn is_action_level_error(e: &EvalError) -> bool {
    matches!(
        e,
        EvalError::PrimedVariableNotBound { .. } | EvalError::UnchangedNotEvaluable { .. }
    )
}

/// Check if an error should be treated as a disabled conjunction guard during
/// speculative guard evaluation in the unified enumerator.
///
/// TLA2's unified enumerator speculatively evaluates conjuncts as boolean guards.
/// When a guard expression triggers one of these errors, the guard is treated as
/// "failed" (conjunction disabled), matching TLC's behavior where a conjunction
/// guard that can't be evaluated means the action is not enabled in this branch.
///
/// IMPORTANT (Fix #1552): This function must ONLY be used in conjunction guard
/// contexts within the unified enumerator. It must NOT be used at:
/// - Or-branch level (TLC propagates all errors from disjuncts fatally)
/// - Top-level action evaluation (TLC propagates all errors fatally)
/// - Worker-level error handling (TLC propagates all errors fatally)
///
/// Use `eval_enabled` for ENABLED operator contexts (separate suppression).
pub(crate) fn is_disabled_action_error(err: &EvalError) -> bool {
    matches!(
        err,
        EvalError::NotInDomain { .. }
            | EvalError::IndexOutOfBounds { .. }
            | EvalError::NoSuchField { .. }
            | EvalError::ChooseFailed { .. }
            | EvalError::DivisionByZero { .. }
    )
}

/// Check if an eval error during speculative guard evaluation should fall back
/// to assignment extraction instead of propagating.
///
/// TLA2's unified enumerator speculatively evaluates conjuncts as guards before
/// trying structural decomposition. Unlike TLC (which pattern-matches the AST),
/// TLA2 hits runtime errors when expressions reference unresolved variables
/// (e.g., primed vars not detected by `is_primed_assignment`). These errors are
/// expected in the speculative path and should fall through to assignment extraction.
///
/// All other errors (TypeError, ArityMismatch, AssertionFailed, etc.) match TLC
/// behavior: they propagate as model checking failures.
pub(crate) fn is_speculative_eval_fallback(err: &EvalError) -> bool {
    matches!(
        err,
        EvalError::UndefinedVar { .. } | EvalError::UndefinedOp { .. }
    )
}

/// Classification of `eval_iter_set` errors for speculative extraction paths.
///
/// When the checker speculatively extracts symbolic assignments (EXISTS domains,
/// InSet constraints), `eval_iter_set` may fail for two distinct reasons:
///
/// 1. **Not enumerable / not a set**: The value cannot be iterated because it is
///    not a set type, or it is an unresolved variable reference in a speculative
///    phase. These errors are safe to defer — the expression will be evaluated
///    on a strict path later.
///
/// 2. **Fatal evaluation error**: A genuine semantic failure (TypeError in a
///    predicate, assertion failure, division by zero, etc.). TLC treats these as
///    fatal model checking errors. Silently skipping them causes the checker to
///    miss states.
///
/// Part of #1886: replaces `Err(_)` catch-alls with explicit classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IterDomainAction {
    /// Safe to skip/defer — value is not enumerable in this phase, or references
    /// unresolved variables. The expression will be evaluated on a strict path.
    Defer,
    /// Fatal — a genuine evaluation error that must propagate. Swallowing this
    /// would silently drop states.
    Fatal,
}

/// Classify an `eval_iter_set` error for speculative extraction paths.
///
/// Uses the same error classes as `is_speculative_eval_fallback` for the `Defer`
/// bucket, plus `TypeError` with `expected: "Set"` (the canonical "not enumerable"
/// signal from `eval_iter_set`). Everything else is `Fatal`.
///
/// See designs/2026-02-15-1886-eval-iter-set-error-contract.md for rationale.
pub(crate) fn classify_iter_error_for_speculative_path(err: &EvalError) -> IterDomainAction {
    match err {
        // Not a set / not enumerable — safe to defer.
        EvalError::TypeError {
            expected: "Set", ..
        } => IterDomainAction::Defer,
        // Set exists but cannot be enumerated (infinite or exceeds limit) — safe to defer.
        // Part of #3015: eval_iter_set_tlc_normalized returns SetTooLarge (via
        // Value::iter_set_tlc_normalized catch-all) for infinite sets like Nat, Int,
        // Seq(S). Previously eval_iter_set returned TypeError("Set") for these, but
        // TLC-normalized iteration correctly identifies them as sets that happen to be
        // non-enumerable. Both cases are safe to defer in speculative paths.
        EvalError::SetTooLarge { .. } => IterDomainAction::Defer,
        // Unresolved references — speculative phase may not have all bindings.
        EvalError::UndefinedVar { .. } | EvalError::UndefinedOp { .. } => IterDomainAction::Defer,
        // Everything else is a genuine evaluation failure — propagate.
        _ => IterDomainAction::Fatal,
    }
}

#[cfg(test)]
mod tests {
    use super::{classify_iter_error_for_speculative_path, IterDomainAction};
    use crate::error::EvalError;

    #[test]
    fn test_classify_iter_error_defer_for_non_enumerable_set_type_error() {
        let err = EvalError::TypeError {
            expected: "Set",
            got: "Int",
            span: None,
        };
        assert_eq!(
            classify_iter_error_for_speculative_path(&err),
            IterDomainAction::Defer
        );
    }

    #[test]
    fn test_classify_iter_error_defer_for_unresolved_symbol() {
        let undefined_var = EvalError::UndefinedVar {
            name: "x".to_string(),
            span: None,
        };
        assert_eq!(
            classify_iter_error_for_speculative_path(&undefined_var),
            IterDomainAction::Defer
        );

        let undefined_op = EvalError::UndefinedOp {
            name: "Foo".to_string(),
            span: None,
        };
        assert_eq!(
            classify_iter_error_for_speculative_path(&undefined_op),
            IterDomainAction::Defer
        );
    }

    #[test]
    fn test_classify_iter_error_fatal_for_non_set_type_error() {
        let err = EvalError::TypeError {
            expected: "BOOLEAN",
            got: "Set",
            span: None,
        };
        assert_eq!(
            classify_iter_error_for_speculative_path(&err),
            IterDomainAction::Fatal
        );
    }

    /// Part of #3015: SetTooLarge is the canonical error from
    /// `Value::iter_set_tlc_normalized` for infinite sets (Nat, Int, Seq(S)).
    /// These are safe to defer in speculative paths — the domain is a valid set
    /// that simply cannot be enumerated.
    #[test]
    fn test_classify_iter_error_defer_for_set_too_large() {
        let err = EvalError::SetTooLarge { span: None };
        assert_eq!(
            classify_iter_error_for_speculative_path(&err),
            IterDomainAction::Defer
        );
    }
}
