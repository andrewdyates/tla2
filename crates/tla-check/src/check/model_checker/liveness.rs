// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug::debug_safety_temporal;
#[cfg(debug_assertions)]
use super::State;
use super::{Fingerprint, ModelChecker};

#[cfg(test)]
mod bug_3161_tests;
mod build_formula;
mod check_property;
mod checkpoint;
#[cfg(test)]
mod compact_state_fp_tests;
mod error_format;
#[cfg(test)]
mod fairness_planning_tests;
#[cfg(test)]
mod inline_cache_tests;
pub(super) mod inline_fairness;
mod inline_fairness_enabled;
#[cfg(test)]
mod inline_fairness_tests;
pub(super) mod inline_helpers;
mod inline_liveness;
mod inline_record;
#[cfg(test)]
mod liveness_mode_tests;
#[cfg(test)]
mod on_the_fly_tests;
mod periodic;
mod runner;
mod safety_parts;
mod safety_split;
mod safety_temporal;
#[cfg(test)]
mod specification_property_tests;
pub(super) mod subscript_action_pair;
mod tautology;
#[cfg(test)]
mod tautology_tests;
pub(crate) mod temporal_scan;

pub(crate) use inline_liveness::InlineLivenessPropertyPlan;

#[inline]
fn compact_value_fingerprint_local(value: &tla_value::CompactValue) -> u64 {
    if value.is_bool() {
        return crate::state::value_fingerprint(&crate::Value::Bool(value.as_bool()));
    }
    if value.is_int() {
        return crate::state::value_fingerprint(&crate::Value::SmallInt(value.as_int()));
    }
    if value.is_heap() {
        return crate::state::value_fingerprint(value.as_heap_value());
    }

    crate::state::value_fingerprint(&crate::Value::from(value))
}

#[inline]
fn compute_fingerprint_from_compact_values(
    values: &[tla_value::CompactValue],
    registry: &crate::var_index::VarRegistry,
) -> Fingerprint {
    let mut combined = 0u64;
    for (i, value) in values.iter().enumerate() {
        let value_fp = compact_value_fingerprint_local(value);
        let salt = registry.fp_salt(crate::var_index::VarIndex::new(i));
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined ^= contribution;
    }

    Fingerprint(crate::state::finalize_fingerprint_xor(
        combined,
        tla_core::FNV_PRIME,
    ))
}

/// Part of #3225: single-source liveness mode matrix for the sequential checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LivenessMode {
    /// No PROPERTY entries require post-BFS liveness handling.
    Disabled,
    /// Full states are retained during BFS.
    ///
    /// `symmetry=true` means this is the symmetry-upgraded liveness lane from
    /// `prepare_bfs_common()`. `view=true` records that VIEW is active even
    /// though full-state storage avoids the fp-only replay constraints.
    FullState { symmetry: bool, view: bool },
    /// Fingerprint-only liveness; VIEW requires canonical-fingerprint handling.
    FingerprintOnly { view: bool },
}

impl LivenessMode {
    // Four feature-flag bools map 1:1 to the three LivenessMode variants;
    // a config struct adds indirection without improving clarity here.
    #[allow(clippy::fn_params_excessive_bools)]
    pub(super) fn compute(
        has_properties: bool,
        store_full_states: bool,
        has_symmetry: bool,
        has_view: bool,
    ) -> Self {
        if !has_properties {
            Self::Disabled
        } else if store_full_states {
            Self::FullState {
                symmetry: has_symmetry,
                view: has_view,
            }
        } else {
            Self::FingerprintOnly { view: has_view }
        }
    }

    /// Whether this mode implies full states are stored in BFS.
    ///
    /// Part of #3225: callsites that previously read `store_full_states`
    /// directly to decide on deferred state-cache construction can use
    /// this method instead, keeping the decision coupled to the mode enum.
    pub(crate) fn stores_full_states(self) -> bool {
        matches!(self, Self::FullState { .. })
    }

    /// Whether any post-BFS liveness work is needed.
    pub(crate) fn is_active(self) -> bool {
        !matches!(self, Self::Disabled)
    }
}

/// Debug-log a safety temporal property violation with state details.
#[cfg(debug_assertions)]
fn debug_log_safety_temporal_violation(
    source_fp: Fingerprint,
    dest_fp: Fingerprint,
    cur_state: &State,
    succ_state: &State,
) {
    debug_block!(debug_safety_temporal(), {
        eprintln!("=== Safety Temporal Property Violation ===");
        eprintln!("Source canon fp: {source_fp}");
        eprintln!("Dest canon fp: {dest_fp}");
        eprintln!("Current state (from seen):");
        for (name, value) in cur_state.vars() {
            eprintln!("  {name} = {value:?}");
        }
        eprintln!("Successor state (from witness):");
        for (name, value) in succ_state.vars() {
            eprintln!("  {name} = {value:?}");
        }
        eprintln!("==========================================");
    });
}

impl ModelChecker<'_> {
    pub(super) fn track_liveness_init_states(&self) -> bool {
        !self.config.properties.is_empty() && !super::debug::skip_liveness()
    }

    pub(super) fn use_on_the_fly_liveness(&self) -> bool {
        self.track_liveness_init_states() && self.config.liveness_execution.uses_on_the_fly()
    }

    pub(super) fn refresh_liveness_mode(&mut self) {
        self.liveness_mode = LivenessMode::compute(
            !self.config.properties.is_empty(),
            self.state_storage.store_full_states,
            !self.symmetry.perms.is_empty(),
            self.compiled.cached_view_name.is_some(),
        );
    }
}
