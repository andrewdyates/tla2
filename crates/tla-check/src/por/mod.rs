// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Partial Order Reduction (POR) for state space reduction
//!
//! This module implements POR infrastructure: static dependency extraction,
//! visibility analysis, and ample-set computation. Supported in both
//! sequential and parallel modes (Part of #3706).
//!
//! # UNCHANGED Commutativity (Part of #3993)
//!
//! TLA+ requires every action to specify all state variables, typically via
//! `UNCHANGED` for variables the action does not modify. Naive treatment of
//! `UNCHANGED x` as both a read and write of `x` makes virtually all actions
//! dependent, defeating POR.
//!
//! The key insight is that `UNCHANGED x` means `x' = x` — the identity
//! function on `x`. Identity writes commute with ALL operations:
//! - With reads: reading x is unaffected by x' = x
//! - With real writes: UNCHANGED preserves whatever value is there
//! - With other identity writes: both preserve x
//!
//! Therefore, `UNCHANGED` variables are tracked separately from real writes
//! in `ActionDependencies::unchanged`, and the independence check only
//! considers real writes (in `ActionDependencies::writes`) for conflicts.
//!
//! # References
//!
//! - Godefroid, "Partial-Order Methods for the Verification of Concurrent Systems"
//! - Peled, "All from One, One for All: On Model Checking Using Representatives"

mod dependencies;
mod dependencies_ast;
mod visibility;

#[cfg(test)]
mod tests;

pub(crate) use dependencies::{check_static_independence, ActionDependencies};
pub(crate) use dependencies_ast::extract_dependencies_ast_expr;
pub(crate) use visibility::VisibilitySet;

use crate::coverage::DetectedAction;

use self::dependencies_ast::extract_action_dependencies;

/// Resolve whether auto-POR is enabled.
///
/// Config `auto_por` takes precedence when explicitly set (`Some(val)`).
/// Otherwise, the `TLA2_AUTO_POR` env var controls (default: enabled).
/// The env var is cached via `OnceLock` so it is read at most once per process.
///
/// Shared by both sequential (`check/model_checker/run.rs`) and parallel
/// (`parallel/checker/prepare.rs`) checkers. Part of #4164.
pub(crate) fn resolve_auto_por(config_override: Option<bool>) -> bool {
    match config_override {
        Some(val) => val,
        None => {
            static AUTO_POR: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *AUTO_POR.get_or_init(|| {
                std::env::var("TLA2_AUTO_POR").map_or(true, |v| v != "0")
            })
        }
    }
}

/// Independence status between two actions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IndependenceStatus {
    /// Actions are proven independent (via static or SMT analysis)
    Independent,
    /// Actions are proven dependent (conflict detected)
    Dependent,
    /// Independence could not be determined (treat as dependent)
    Unknown,
}

/// Matrix of independence relations between actions
#[derive(Debug)]
pub(crate) struct IndependenceMatrix {
    n: usize,
    matrix: Vec<IndependenceStatus>,
    dependencies: Vec<ActionDependencies>,
}

impl IndependenceMatrix {
    /// Compute independence matrix from canonical action dependencies.
    pub(crate) fn compute(dependencies: &[ActionDependencies]) -> Self {
        let n = dependencies.len();
        let dependencies = dependencies.to_vec();

        let mut matrix = vec![IndependenceStatus::Unknown; n * n];

        for i in 0..n {
            matrix[i * n + i] = IndependenceStatus::Dependent;

            for j in (i + 1)..n {
                let status = if check_static_independence(&dependencies[i], &dependencies[j]) {
                    IndependenceStatus::Independent
                } else {
                    IndependenceStatus::Dependent
                };

                matrix[i * n + j] = status;
                matrix[j * n + i] = status;
            }
        }

        IndependenceMatrix {
            n,
            matrix,
            dependencies,
        }
    }

    /// Get independence status between two actions
    #[inline]
    pub(crate) fn get(&self, i: usize, j: usize) -> IndependenceStatus {
        debug_assert!(i < self.n && j < self.n);
        self.matrix[i * self.n + j]
    }

    /// Get the number of actions.
    #[allow(dead_code)]
    pub(crate) fn action_count(&self) -> usize {
        self.n
    }

    /// Get dependencies for a specific action
    pub(crate) fn get_dependencies(&self, action_idx: usize) -> &ActionDependencies {
        &self.dependencies[action_idx]
    }

    /// Count the number of independent pairs.
    ///
    /// Part of #3993 Phase 11: always available (not just debug builds)
    /// so POR diagnostic reports can be generated in release mode.
    pub(crate) fn count_independent_pairs(&self) -> usize {
        let mut count = 0;
        for i in 0..self.n {
            for j in (i + 1)..self.n {
                if self.matrix[i * self.n + j] == IndependenceStatus::Independent {
                    count += 1;
                }
            }
        }
        count
    }

    /// Count the total number of pairs (n choose 2).
    ///
    /// Part of #3993 Phase 11: always available (not just debug builds).
    pub(crate) fn total_pairs(&self) -> usize {
        if self.n < 2 {
            0
        } else {
            self.n * (self.n - 1) / 2
        }
    }

    /// Generate a human-readable diagnostic summary of action independence.
    ///
    /// Lists each action pair and whether they are independent or dependent,
    /// along with the read/write/unchanged sets for each action. This helps
    /// users understand why POR is or is not achieving reduction.
    ///
    /// Part of #3993 Phase 11: POR analysis diagnostic reporting.
    pub(crate) fn diagnostic_summary(&self, action_names: &[String]) -> String {
        use std::fmt::Write;
        let mut out = String::new();

        let _ = writeln!(
            out,
            "POR Independence Analysis: {} actions, {} pairs ({} independent)",
            self.n,
            self.total_pairs(),
            self.count_independent_pairs(),
        );

        // Per-action dependency summary
        for (i, deps) in self.dependencies.iter().enumerate() {
            let name = action_names
                .get(i)
                .map(|s| s.as_str())
                .unwrap_or("<unknown>");
            let reads: Vec<_> = deps.reads.iter().map(|v| format!("v{}", v.0)).collect();
            let writes: Vec<_> = deps.writes.iter().map(|v| format!("v{}", v.0)).collect();
            let unchanged: Vec<_> =
                deps.unchanged.iter().map(|v| format!("v{}", v.0)).collect();
            let _ = writeln!(
                out,
                "  Action {i} ({name}): reads={{{}}}, writes={{{}}}, unchanged={{{}}}",
                reads.join(", "),
                writes.join(", "),
                unchanged.join(", "),
            );
        }

        // Pairwise independence
        if self.n >= 2 {
            let _ = writeln!(out, "  Pairwise independence:");
            for i in 0..self.n {
                for j in (i + 1)..self.n {
                    let name_i = action_names
                        .get(i)
                        .map(|s| s.as_str())
                        .unwrap_or("<unknown>");
                    let name_j = action_names
                        .get(j)
                        .map(|s| s.as_str())
                        .unwrap_or("<unknown>");
                    let status = match self.matrix[i * self.n + j] {
                        IndependenceStatus::Independent => "INDEPENDENT",
                        IndependenceStatus::Dependent => "dependent",
                        IndependenceStatus::Unknown => "unknown",
                    };
                    let _ = writeln!(out, "    ({name_i}, {name_j}): {status}");
                }
            }
        }

        out
    }
}

/// Extract action dependencies from detected canonical action expressions.
///
/// Callers must pass actions from an already-expanded `Next` body. The checker's
/// `prepare_bfs_common()` path does this via `checker_ops::expand_operator_body(...)`
/// before `detect_actions(...)`, so the resulting action expressions are the
/// canonical AST bodies rather than bare operator references.
pub(crate) fn extract_detected_action_dependencies(
    actions: &[DetectedAction],
) -> Vec<ActionDependencies> {
    actions
        .iter()
        .map(|action| extract_action_dependencies(&action.expr))
        .collect()
}

/// Result of ample set computation
#[derive(Debug, Clone)]
pub(crate) struct AmpleSetResult {
    /// Indices of actions in the ample set
    pub(crate) actions: Vec<usize>,
    /// Whether a reduction was achieved (ample set is smaller than enabled set)
    pub(crate) reduced: bool,
}

/// Compute the ample set for a given set of enabled actions.
///
/// Implements stubborn-set-style partial order reduction adapted from
/// tla-petri's `stubborn.rs` (Schmidt 2000 / Valmari 1990). The algorithm:
///
/// 1. Pick a seed action from the enabled set (prefer non-visible action
///    with the smallest dependency closure -- heuristic from tla-petri).
/// 2. Close under the dependency relation: for each action in the candidate
///    set, transitively add all dependent enabled actions.
/// 3. **C2 (visibility)**: if any action in the candidate set is visible
///    (writes to a variable in an invariant), fall back to the full enabled
///    set. This preserves safety properties.
/// 4. **C3 (cycle proviso)**: automatically satisfied for BFS-based safety
///    checking because BFS visits each state at most once -- no exploration
///    cycles exist. This is the same argument that makes tla-petri's
///    deadlock-preserving stubborn sets sound for BFS.
///
/// Thread-safe: each worker calls this independently with shared read-only
/// `IndependenceMatrix` and `VisibilitySet`.
///
/// Reference: Cross-pollinated from `crates/tla-petri/src/stubborn.rs`
/// (Part of #3712).
pub(crate) fn compute_ample_set(
    enabled: &[usize],
    independence: &IndependenceMatrix,
    visibility: &VisibilitySet,
) -> AmpleSetResult {
    if enabled.len() <= 1 {
        return AmpleSetResult {
            actions: enabled.to_vec(),
            reduced: false,
        };
    }

    // Build enabled lookup for O(1) membership tests.
    let mut is_enabled = vec![false; independence.n];
    for &idx in enabled {
        if idx < independence.n {
            is_enabled[idx] = true;
        }
    }

    // Try each enabled action as a potential seed, preferring non-visible
    // actions with the smallest dependency closure (heuristic from tla-petri's
    // stubborn set seed selection). Stop at the first seed that produces a
    // proper subset of the enabled set.
    let mut best_result: Option<Vec<usize>> = None;

    // Sort candidates: non-visible first, then by number of dependent
    // enabled actions (ascending). This heuristic minimizes closure size.
    let mut candidates: Vec<usize> = enabled.to_vec();
    candidates.sort_by(|&a, &b| {
        let a_visible = visibility.is_action_visible(independence.get_dependencies(a));
        let b_visible = visibility.is_action_visible(independence.get_dependencies(b));
        // Non-visible before visible
        a_visible.cmp(&b_visible).then_with(|| {
            // Among same visibility, prefer fewer dependent enabled actions
            let a_deps = count_dependent_enabled(a, enabled, independence);
            let b_deps = count_dependent_enabled(b, enabled, independence);
            a_deps.cmp(&b_deps)
        })
    });

    for &seed in &candidates {
        // C2: if the seed itself is visible, skip it -- a visible action
        // in the ample set forces inclusion of ALL enabled actions.
        if visibility.is_action_visible(independence.get_dependencies(seed)) {
            // All remaining candidates are also visible (sorted order).
            break;
        }

        // Close under dependencies among enabled actions.
        // Adapted from tla-petri's `compute_deadlock_preserving` closure.
        let mut in_ample = vec![false; independence.n];
        let mut worklist = vec![seed];
        in_ample[seed] = true;
        let mut has_visible = false;

        while let Some(action) = worklist.pop() {
            // Check visibility of this action
            if visibility.is_action_visible(independence.get_dependencies(action)) {
                has_visible = true;
                break;
            }

            // Add all enabled actions that are dependent on this action.
            // This mirrors tla-petri's "add interferes_with[t]" step.
            for &other in enabled {
                if !in_ample[other]
                    && independence.get(action, other) != IndependenceStatus::Independent
                {
                    in_ample[other] = true;
                    worklist.push(other);
                }
            }
        }

        // C2: if any visible action entered the closure, this seed
        // cannot produce a valid ample set -- try the next seed.
        if has_visible {
            continue;
        }

        // Collect the ample set (intersection of closure with enabled).
        let ample: Vec<usize> = enabled.iter().copied().filter(|&a| in_ample[a]).collect();

        // Only accept if we achieved actual reduction.
        if ample.len() < enabled.len() {
            // Keep the smallest ample set found across all seeds.
            if best_result
                .as_ref()
                .map_or(true, |prev| ample.len() < prev.len())
            {
                best_result = Some(ample);
            }
            // First valid reduction is typically good enough; the seed
            // heuristic already selected the best candidate first.
            break;
        }
    }

    match best_result {
        Some(actions) => AmpleSetResult {
            reduced: true,
            actions,
        },
        None => AmpleSetResult {
            actions: enabled.to_vec(),
            reduced: false,
        },
    }
}

/// Count how many enabled actions are dependent on `action`.
/// Used as a heuristic for seed selection (prefer fewer dependencies).
fn count_dependent_enabled(
    action: usize,
    enabled: &[usize],
    independence: &IndependenceMatrix,
) -> usize {
    enabled
        .iter()
        .filter(|&&other| {
            other != action && independence.get(action, other) != IndependenceStatus::Independent
        })
        .count()
}

/// Statistics about POR effectiveness
#[derive(Debug, Clone, Default)]
pub(crate) struct PorStats {
    /// Number of states where POR achieved reduction
    pub(crate) reductions: u64,
    /// Total number of states processed
    pub(crate) total_states: u64,
    /// Total actions skipped due to POR
    pub(crate) actions_skipped: u64,
}

impl PorStats {
    /// Record a POR computation result
    pub(crate) fn record(&mut self, enabled_count: usize, ample_count: usize) {
        self.total_states += 1;
        if ample_count < enabled_count {
            self.reductions += 1;
            self.actions_skipped += (enabled_count - ample_count) as u64;
        }
    }
}
