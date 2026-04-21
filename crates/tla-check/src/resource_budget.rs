// Copyright 2026 Andrew Yates Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unified resource budget for model checking runs (Part of #3282).
// Bundles all resource limits into a single struct with safe defaults.

use crate::enumerate::{Constraint, InitDomain};
use crate::memory;
use std::sync::Arc;

/// Unified resource budget for a model checking run.
///
/// Collects all resource limits (states, depth, memory, disk, timeout) in one
/// place so that callers don't need to manage 5+ separate setter calls. When
/// no explicit limits are provided, conservative defaults prevent runaway
/// resource consumption (TLC disk-exhaustion post-mortem, #3282).
///
/// # Safe Defaults
///
/// | Limit          | Default                                  |
/// |----------------|------------------------------------------|
/// | `max_states`   | 0 (unlimited)                            |
/// | `max_depth`    | 0 (unlimited)                            |
/// | `memory_bytes` | 90% of physical RAM (auto-detected)      |
/// | `disk_bytes`   | 80% of available disk on working dir     |
/// | `timeout_secs` | 0 (unlimited)                            |
///
/// Part of #3282.
#[derive(Debug, Clone)]
pub struct ResourceBudget {
    /// Maximum number of states to explore (0 = unlimited).
    pub max_states: usize,
    /// Maximum BFS depth (0 = unlimited).
    pub max_depth: usize,
    /// Maximum process RSS in bytes (0 = unlimited).
    pub memory_bytes: usize,
    /// Maximum disk usage in bytes for state storage (0 = unlimited).
    pub disk_bytes: usize,
    /// Timeout in seconds (0 = unlimited).
    pub timeout_secs: u64,
}

impl ResourceBudget {
    /// Create a budget with no limits (all zeros).
    #[must_use]
    pub fn unlimited() -> Self {
        Self {
            max_states: 0,
            max_depth: 0,
            memory_bytes: 0,
            disk_bytes: 0,
            timeout_secs: 0,
        }
    }

    /// Create a budget with safe auto-detected defaults.
    ///
    /// Memory: 90% of physical RAM (via `MemoryPolicy::from_system_default()`).
    /// Disk: 80% of available disk space on the current working directory.
    /// Other limits: unlimited (states, depth, timeout).
    ///
    /// Falls back to unlimited for any limit that cannot be auto-detected
    /// (e.g., unsupported platforms).
    #[must_use]
    pub fn safe_defaults() -> Self {
        let memory_bytes = memory::MemoryPolicy::from_system_default()
            .map(|p| p.limit_bytes())
            .unwrap_or(0);

        let disk_bytes = available_disk_bytes_cwd()
            .map(|avail| (avail as f64 * 0.80) as usize)
            .unwrap_or(0);

        Self {
            max_states: 0,
            max_depth: 0,
            memory_bytes,
            disk_bytes,
            timeout_secs: 0,
        }
    }

    /// Override the memory limit (in bytes). 0 = unlimited.
    #[must_use]
    pub fn with_memory_bytes(mut self, bytes: usize) -> Self {
        self.memory_bytes = bytes;
        self
    }

    /// Override the disk limit (in bytes). 0 = unlimited.
    #[must_use]
    pub fn with_disk_bytes(mut self, bytes: usize) -> Self {
        self.disk_bytes = bytes;
        self
    }

    /// Override the max states limit. 0 = unlimited.
    #[must_use]
    pub fn with_max_states(mut self, limit: usize) -> Self {
        self.max_states = limit;
        self
    }

    /// Override the max depth limit. 0 = unlimited.
    #[must_use]
    pub fn with_max_depth(mut self, limit: usize) -> Self {
        self.max_depth = limit;
        self
    }

    /// Override the timeout in seconds. 0 = unlimited.
    #[must_use]
    pub fn with_timeout_secs(mut self, secs: u64) -> Self {
        self.timeout_secs = secs;
        self
    }

    /// Whether any disk budget is configured.
    #[must_use]
    pub fn has_disk_limit(&self) -> bool {
        self.disk_bytes > 0
    }

    /// Whether any memory budget is configured.
    #[must_use]
    pub fn has_memory_limit(&self) -> bool {
        self.memory_bytes > 0
    }
}

impl Default for ResourceBudget {
    /// Default is safe defaults (auto-detected limits), not unlimited.
    fn default() -> Self {
        Self::safe_defaults()
    }
}

/// Query available disk space (in bytes) on the filesystem containing the
/// current working directory.
///
/// Returns `None` if the query fails or the platform is unsupported.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn available_disk_bytes_impl(path: &std::path::Path) -> Option<usize> {
    use std::mem;

    let c_path = std::ffi::CString::new(path.to_str()?).ok()?;
    let mut stat: libc::statvfs = unsafe { mem::zeroed() };
    // SAFETY: statvfs with a valid null-terminated path and output buffer.
    let ret = unsafe { libc::statvfs(c_path.as_ptr(), &mut stat) };

    if ret == 0 {
        // Available space for non-root users: f_bavail * f_frsize
        let avail = (stat.f_bavail as u64) * (stat.f_frsize as u64);
        Some(avail as usize)
    } else {
        None
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn available_disk_bytes_cwd() -> Option<usize> {
    let cwd = std::env::current_dir().ok()?;
    available_disk_bytes_impl(&cwd)
}

/// Unsupported platform fallback.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn available_disk_bytes_cwd() -> Option<usize> {
    None
}

/// Query available disk space (in bytes) for a specific path.
///
/// Test-only helper used to validate the path-based statvfs query.
#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
pub(crate) fn available_disk_bytes(path: &std::path::Path) -> Option<usize> {
    available_disk_bytes_impl(path)
}

/// Unsupported platform fallback.
#[cfg(all(test, not(any(target_os = "macos", target_os = "linux"))))]
pub(crate) fn available_disk_bytes(_path: &std::path::Path) -> Option<usize> {
    None
}

/// Render byte counts with binary units so byte-sized limits stay visible.
#[must_use]
pub(crate) fn format_bytes(bytes: usize) -> String {
    const KIB: usize = 1024;
    const MIB: usize = 1024 * KIB;
    const GIB: usize = 1024 * MIB;

    if bytes < KIB {
        format!("{bytes} B")
    } else if bytes < MIB {
        format!("{:.1} KiB", bytes as f64 / KIB as f64)
    } else if bytes < GIB {
        format!("{:.1} MiB", bytes as f64 / MIB as f64)
    } else {
        format!("{:.1} GiB", bytes as f64 / GIB as f64)
    }
}

/// Result of pre-exploration state space estimation (Part of #3282).
///
/// Provides a coarse upper bound on initial state count derived from
/// Init predicate constraints and variable domain cardinalities. This
/// estimate is computed BEFORE exploration begins, using only the
/// constraint structure extracted from the Init predicate.
///
/// The estimate is an upper bound because:
/// - Filter constraints reduce the space but are not accounted for
/// - Deferred constraints are treated as unbounded
/// - Cross-variable dependencies (e.g., x depends on y) are ignored
#[derive(Debug, Clone)]
pub struct StateSpaceEstimate {
    /// Upper bound on initial states. `None` means unbounded (some variable
    /// has no finite domain estimate).
    pub initial_states_upper_bound: Option<u128>,
    /// Per-variable domain cardinality estimate. `None` means unbounded.
    pub variable_domains: Vec<(String, Option<u128>)>,
    /// Variables whose domain could not be estimated (deferred, unconstrained).
    pub unbounded_vars: Vec<String>,
    /// Number of disjunctive branches in the Init predicate.
    pub branch_count: usize,
}

impl StateSpaceEstimate {
    /// Whether the estimate is finite (all variables have bounded domains).
    #[must_use]
    pub fn is_bounded(&self) -> bool {
        self.initial_states_upper_bound.is_some()
    }

    /// Check whether this estimate exceeds a given state limit.
    /// Returns `true` if the estimate is bounded and exceeds `limit`.
    #[must_use]
    pub fn exceeds_states(&self, limit: u128) -> bool {
        self.initial_states_upper_bound
            .map_or(false, |est| est > limit)
    }

    /// Estimate memory usage in bytes assuming 8 bytes per fingerprint.
    /// Returns `None` if the initial state estimate is unbounded.
    #[must_use]
    pub fn estimated_memory_bytes(&self) -> Option<u128> {
        self.initial_states_upper_bound.map(|s| s.saturating_mul(8))
    }
}

/// Estimate the initial state space size from Init predicate constraints.
///
/// Takes the constraint branches produced by `extract_init_constraints()`
/// and the list of state variable names. For each variable, computes the
/// domain cardinality from the constraint (Eq=1, In=|domain|, etc.).
/// The per-branch estimate is the product of all variable domain sizes;
/// the total is the sum across branches (disjunctive OR).
///
/// This is a coarse upper bound — it does not account for Filter constraints,
/// NotEq exclusions, or cross-variable dependencies. It runs in O(vars * branches)
/// without materializing any set values, using `Value::set_len()` for lazy
/// cardinality computation.
///
/// Part of #3282: pre-exploration estimation.
pub(crate) fn estimate_init_state_space(
    branches: &[Vec<Constraint>],
    vars: &[Arc<str>],
) -> StateSpaceEstimate {
    if branches.is_empty() {
        return StateSpaceEstimate {
            initial_states_upper_bound: Some(0),
            variable_domains: vars.iter().map(|v| (v.to_string(), Some(0))).collect(),
            unbounded_vars: Vec::new(),
            branch_count: 0,
        };
    }

    // Aggregate domain sizes across all branches for each variable.
    // For each branch, we compute the product of variable domain sizes.
    // The total estimate is the sum of branch products (disjunction = union).
    let mut total_estimate: Option<u128> = Some(0);
    let mut var_max_domains: Vec<Option<u128>> = vec![None; vars.len()];
    let mut unbounded_set: std::collections::HashSet<String> = std::collections::HashSet::new();

    for branch in branches {
        let mut branch_product: Option<u128> = Some(1);

        for (var_idx, var_name) in vars.iter().enumerate() {
            let domain_size = estimate_var_domain_in_branch(var_name, branch);

            // Track the max domain size per variable across branches (for reporting)
            match (var_max_domains[var_idx], domain_size) {
                (None, Some(d)) => var_max_domains[var_idx] = Some(d),
                (Some(existing), Some(d)) if d > existing => {
                    var_max_domains[var_idx] = Some(d);
                }
                (Some(_), None) => {
                    var_max_domains[var_idx] = None;
                    unbounded_set.insert(var_name.to_string());
                }
                _ => {}
            }

            // Multiply into branch product
            match (branch_product, domain_size) {
                (Some(prod), Some(d)) => {
                    branch_product = prod.checked_mul(d);
                }
                _ => {
                    branch_product = None;
                }
            }
        }

        // Sum across branches
        match (total_estimate, branch_product) {
            (Some(total), Some(prod)) => {
                total_estimate = total.checked_add(prod);
            }
            _ => {
                total_estimate = None;
            }
        }
    }

    // Collect unbounded variables
    for (idx, var) in vars.iter().enumerate() {
        if var_max_domains[idx].is_none() && !unbounded_set.contains(var.as_ref()) {
            unbounded_set.insert(var.to_string());
        }
    }

    let variable_domains = vars
        .iter()
        .enumerate()
        .map(|(idx, v)| (v.to_string(), var_max_domains[idx]))
        .collect();

    let unbounded_vars: Vec<String> = vars
        .iter()
        .filter(|v| unbounded_set.contains(v.as_ref()))
        .map(|v| v.to_string())
        .collect();

    StateSpaceEstimate {
        initial_states_upper_bound: total_estimate,
        variable_domains,
        unbounded_vars,
        branch_count: branches.len(),
    }
}

/// Estimate the domain cardinality for a single variable in one constraint branch.
///
/// Returns `Some(n)` for a finite domain, `None` if unbounded or unknown.
fn estimate_var_domain_in_branch(var_name: &str, constraints: &[Constraint]) -> Option<u128> {
    let mut domain_size: Option<u128> = None;

    for constraint in constraints {
        match constraint {
            Constraint::Eq(name, _) if name == var_name => {
                // Exact equality: exactly 1 value
                domain_size = intersect_domain(domain_size, Some(1));
            }
            Constraint::In(name, init_domain) if name == var_name => {
                let d = match init_domain {
                    InitDomain::Concrete(values) => Some(values.len() as u128),
                    InitDomain::Enumerable(value) => {
                        value.set_len().map(|n| {
                            // BigInt -> u128 with saturation
                            use num_traits::ToPrimitive;
                            n.to_u128().unwrap_or(u128::MAX)
                        })
                    }
                };
                domain_size = intersect_domain(domain_size, d);
            }
            Constraint::Deferred(name, _) if name == var_name => {
                // Deferred: depends on other variables, can't estimate statically.
                // Treat as bounded-by-1 since it resolves to exactly 1 value once
                // its dependencies are bound (it's an equality `x = expr`).
                domain_size = intersect_domain(domain_size, Some(1));
            }
            Constraint::DeferredIn(name, _) if name == var_name => {
                // DeferredIn: set membership that depends on other variables.
                // We can't estimate the set size without evaluation.
                return None;
            }
            // NotEq reduces domain but we don't subtract (upper bound).
            // Filter reduces domain but we don't account for it (upper bound).
            _ => {}
        }
    }

    // If no constraint found for this variable, it's unconstrained (unbounded).
    domain_size
}

/// Intersect two domain size estimates: take the minimum (tightest constraint wins).
fn intersect_domain(existing: Option<u128>, new: Option<u128>) -> Option<u128> {
    match (existing, new) {
        (None, d) => d,
        (Some(e), Some(n)) => Some(e.min(n)),
        (Some(e), None) => Some(e), // Keep existing if new is unbounded
    }
}
