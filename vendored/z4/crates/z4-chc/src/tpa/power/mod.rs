// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Power abstraction management for TPA.
//!
//! Manages the exact (T^{=n}) and less-than (T^{<n}) power abstractions,
//! including composition, strengthening via interpolation, Houdini filtering,
//! and fixed-point detection.
//!
//! Reference: Golem TPA.cc power management (357-396),
//!            Golem TPA.cc fixed point checks (975-1140)

mod bool_partition;

use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::transition_system::TransitionSystem;
use crate::ChcExpr;

use super::solver::{flatten_to_constraints, PowerKind, TpaSolver};

use bool_partition::{bool_partition_branch_count, classify_bool_partition};

/// Maximum total Bool branch combinations before we refuse to even try
/// the partitioned path.
const BOOL_PARTITION_BRANCH_LIMIT: usize = 65536;

impl TpaSolver {
    /// Get exact power abstraction at the given level.
    ///
    /// Returns the stored pure transition summary. Exact powers are learned
    /// through interpolation (not computed by explicit composition), so they
    /// mention only current-state and next-state variables — never intermediate
    /// midpoint layers. This prevents the geometric formula blowup that
    /// occurred when powers were built by explicit conjunction.
    ///
    /// Level 0 is always the base transition T (set in `init_powers`).
    /// Higher levels are populated by `strengthen_power_with_interpolant`.
    ///
    /// Reference: Golem TPA.cc:getExactPower (line 352-355)
    pub(super) fn get_exact_power(&self, power: u32, _ts: &TransitionSystem) -> Option<ChcExpr> {
        let idx = power as usize;
        if idx < self.exact_powers.len() {
            self.exact_powers[idx].clone()
        } else {
            None
        }
    }

    /// Get less-than power abstraction at the given level.
    ///
    /// Returns the stored pure transition summary. Less-than powers are learned
    /// through interpolation, not computed by explicit composition.
    /// Level 0 is always the identity (0 transition steps, set in `init_powers`).
    ///
    /// Reference: Golem TPA.cc:getLessThanPower (line 381-384)
    pub(super) fn get_less_than_power(
        &self,
        power: u32,
        _ts: &TransitionSystem,
    ) -> Option<ChcExpr> {
        let idx = power as usize;
        if idx < self.less_than_powers.len() {
            self.less_than_powers[idx].clone()
        } else {
            None
        }
    }

    /// Get power abstraction for the given kind (exact or less-than).
    pub(super) fn get_power(
        &self,
        kind: PowerKind,
        power: u32,
        ts: &TransitionSystem,
    ) -> Option<ChcExpr> {
        match kind {
            PowerKind::Exact => self.get_exact_power(power, ts),
            PowerKind::LessThan => self.get_less_than_power(power, ts),
        }
    }

    /// Strengthen power abstraction with a learned interpolant.
    ///
    /// Stores the interpolant at level `power + 1`, conjoining with any
    /// existing value. If the slot is empty, stores the interpolant directly.
    /// This matches Golem's storeExactPower/storeLessThanPower semantics
    /// (TPA.cc:357-396): exact powers are pure learned summaries, not
    /// compositions of lower levels.
    ///
    /// Reference: Golem TPA.cc:storeExactPower (line 357-378),
    ///            Golem TPA.cc:storeLessThanPower (line 386-396)
    fn strengthen_power_with_interpolant(
        &mut self,
        kind: PowerKind,
        power: u32,
        interpolant: ChcExpr,
    ) {
        if self.config.verbose_level > 0 {
            let kind_name = match kind {
                PowerKind::Exact => "Exact",
                PowerKind::LessThan => "Less-than",
            };
            safe_eprintln!(
                "TPA: strengthening {} power {} with interpolant ({} conjuncts)",
                kind_name,
                power,
                interpolant.collect_conjuncts().len()
            );
        }

        let idx = (power + 1) as usize;
        let powers = match kind {
            PowerKind::Exact => &mut self.exact_powers,
            PowerKind::LessThan => &mut self.less_than_powers,
        };
        if powers.len() <= idx {
            powers.resize_with(idx + 1, || None);
        }
        let new_val = match powers[idx].take() {
            Some(existing) => ChcExpr::and(existing, interpolant),
            None => interpolant,
        };
        powers[idx] = Some(new_val);
    }

    /// Compute interpolant from an UNSAT reachability query and strengthen.
    ///
    /// For exact: query was from(v) ∧ T^{=n}(v,v_1) ∧ T^{=n}(v_1,v_2) ∧ to(v_2)
    /// For less-than: learns from the composed case:
    ///   from(v) ∧ T^{<n}(v,v_1) ∧ T^{=n}(v_1,v_2) ∧ to(v_2)
    ///
    /// Partitions at intermediate state v_1:
    /// - A: from(v) ∧ T^{kind}(v, v_1)
    /// - B: T^{=n}(v_1, v_2) ∧ to(v_2)
    ///
    /// The interpolant constrains intermediate states at time 1 and strengthens
    /// the power abstraction at `power + 1`.
    pub(super) fn strengthen_power_from_unsat(
        &mut self,
        kind: PowerKind,
        power: u32,
        from: &ChcExpr,
        to: &ChcExpr,
        ts: &TransitionSystem,
    ) {
        let a_power = match self.get_power(kind, power, ts) {
            Some(p) => p,
            None => return, // Level not learned yet, skip strengthening
        };

        // B-partition always uses the exact power shifted to time 1→2
        let exact_power = match self.get_exact_power(power, ts) {
            Some(ep) => ep,
            None => return, // Level not learned yet, skip strengthening
        };
        let shifted_exact = self.shift_and_freshen(&exact_power, 1, ts);

        // A-partition: from(v) ∧ T^{kind}(v, v_1)
        let a_constraints = {
            let mut constraints = flatten_to_constraints(from);
            constraints.extend(flatten_to_constraints(&a_power));
            constraints
        };

        // B-partition: T^{=n}(v_1, v_2) ∧ to(v_2)
        let shifted_to = self.shift_expr(to, 2, ts);
        let b_constraints = {
            let mut constraints = flatten_to_constraints(&shifted_exact);
            constraints.extend(flatten_to_constraints(&shifted_to));
            constraints
        };

        // Shared variables are at time 1 (the intermediate state)
        let shared_vars = ts.state_var_names_at(1);

        let kind_name = match kind {
            PowerKind::Exact => "Exact",
            PowerKind::LessThan => "Less-than",
        };

        let bool_partition = classify_bool_partition(&a_constraints, &b_constraints);
        let bool_var_count = bool_partition.a_local.len()
            + bool_partition.shared.len()
            + bool_partition.b_local.len();
        if bool_var_count > 0 {
            let branch_count = bool_partition_branch_count(&bool_partition);
            if branch_count.is_some_and(|count| count <= BOOL_PARTITION_BRANCH_LIMIT) {
                if let Some(interpolant) = self.interpolate_with_full_bool_partitioning(
                    &a_constraints,
                    &b_constraints,
                    &shared_vars,
                    &bool_partition,
                ) {
                    if self.config.verbose_level > 0 {
                        safe_eprintln!(
                            "TPA: full Bool partition interpolation succeeded at power {} ({} kind), {} conjuncts, {}/{}/{} Bool vars, {} branch pairs",
                            power,
                            kind_name,
                            interpolant.collect_conjuncts().len(),
                            bool_partition.a_local.len(),
                            bool_partition.shared.len(),
                            bool_partition.b_local.len(),
                            branch_count.expect("checked above")
                        );
                    }
                    self.strengthen_power_with_interpolant(kind, power, interpolant);
                    return;
                }
                if self.config.verbose_level > 0 {
                    safe_eprintln!(
                        "TPA: full Bool partition interpolation failed at power {} ({} kind), falling back",
                        power, kind_name
                    );
                }
            } else if self.config.verbose_level > 0 {
                safe_eprintln!(
                    "TPA: skipping full Bool partition interpolation at power {} ({} kind): {} Bool vars exceed {} branch pairs",
                    power,
                    kind_name,
                    bool_var_count,
                    BOOL_PARTITION_BRANCH_LIMIT
                );
            }
        }

        // Standard interpolation (no Bool partitioning)
        match interpolating_sat_constraints(&a_constraints, &b_constraints, &shared_vars) {
            InterpolatingSatResult::Unsat(interpolant) => {
                if self.config.verbose_level > 0 {
                    safe_eprintln!(
                        "TPA: interpolation succeeded at power {} ({} kind), {} conjuncts",
                        power,
                        kind_name,
                        interpolant.collect_conjuncts().len()
                    );
                }
                self.strengthen_power_with_interpolant(kind, power, interpolant);
            }
            InterpolatingSatResult::Unknown => {
                if self.config.verbose_level > 0 {
                    safe_eprintln!(
                        "TPA: interpolation FAILED at power {} ({} kind), {} shared vars",
                        power,
                        kind_name,
                        shared_vars.len()
                    );
                }
            }
        }
    }

    /// Check if a power abstraction reached a fixed point.
    ///
    /// Exact fixed point: T^{=n} ∘ T^{=n} ⊆ T^{=n}
    /// Less-than fixed point: T^{<n} ∘ T ⊆ T^{<n}
    ///
    /// Three-step verification: (1) containment, (2) non-vacuity, (3) safety.
    ///
    /// Reference: Golem TPA.cc:checkExactFixedPoint (1080-1140),
    ///            Golem TPA.cc:checkLessThanFixedPoint (975-1078)
    pub(super) fn check_fixed_point(
        &mut self,
        kind: PowerKind,
        power: u32,
        ts: &TransitionSystem,
    ) -> bool {
        if power == 0 {
            return false;
        }

        // SOUNDNESS (#7467): Exact fixed-point acceptance is unsound.
        //
        // The safety check (init ∧ T^{=n} ∧ query') only covers states reachable
        // in exactly 2^n steps. But the full reachable set includes ALL step counts
        // (1, 2, ..., 2^n - 1, 2^n, 2^n + 1, ...). An exact fixed-point
        // (T^{=n} ∘ T^{=n} ⊆ T^{=n}) only proves closure of the 2^n-step relation
        // under self-composition — it does NOT prove that ALL reachable states are
        // safe.
        //
        // The less-than fixed-point (T^{<n} ∘ T ⊆ T^{<n}) IS sound because T^{<n}
        // is a true transition invariant: closed under single-step transition, so it
        // covers all reachable states.
        //
        // Golem's exact fixed-point (TPA.cc:1080-1132) builds a separate
        // safeTransitionInvariant from T^{<i} and T^{=i} and verifies it
        // independently. z4 does not yet have that infrastructure.
        //
        // Disable exact fixed-point until the proper Golem port is complete.
        if matches!(kind, PowerKind::Exact) {
            return false;
        }

        let idx = power as usize;
        let powers = match kind {
            PowerKind::Exact => &self.exact_powers,
            PowerKind::LessThan => &self.less_than_powers,
        };
        if idx >= powers.len() || powers[idx].is_none() {
            return false;
        }
        let current_level = powers[idx].clone().expect("power computed for idx");

        let kind_name = match kind {
            PowerKind::Exact => "Exact",
            PowerKind::LessThan => "Less-than",
        };

        // Build composition (differs by kind):
        // Exact: T^{=n}(v,v_1) ∧ T^{=n}(v_1,v_2) — compose with self
        // Less-than: T^{<n}(v,v_1) ∧ T(v_1,v_2) — compose with single transition
        let composition = match kind {
            PowerKind::Exact => ChcExpr::and(
                current_level.clone(),
                self.shift_and_freshen(&current_level, 1, ts),
            ),
            PowerKind::LessThan => ChcExpr::and(current_level.clone(), ts.transition_at(1)),
        };
        let shifted = ts.rename_state_vars_at(&current_level, 1, 2);
        let query = ChcExpr::and(composition, ChcExpr::not(shifted));

        // Step 1: Containment check
        let containment = self
            .smt
            .check_sat_with_timeout(&query, self.config.timeout_per_power);

        if !containment.is_unsat() {
            return false;
        }

        if self.config.verbose_level > 1 {
            safe_eprintln!("TPA: {} containment holds at power {}", kind_name, power);
        }

        // Step 2: Non-vacuity — init ∧ T^{kind} must be satisfiable.
        let init_and_fp = ChcExpr::and(ts.init.clone(), current_level);
        let non_vac = self
            .smt
            .check_sat_with_timeout(&init_and_fp, self.config.timeout_per_power);

        if !non_vac.is_sat() {
            if self.config.verbose_level > 1 {
                safe_eprintln!(
                    "TPA: Rejecting vacuous {} fixed point at power {}",
                    kind_name,
                    power
                );
            }
            return false;
        }

        // Step 3: Safety — init ∧ T^{kind} ∧ query' must be UNSAT.
        let query_at_1 = ts.query_at(1);
        let safety_query = ChcExpr::and(init_and_fp, query_at_1);
        let safety = self
            .smt
            .check_sat_with_timeout(&safety_query, self.config.timeout_per_power);

        if safety.is_unsat() {
            if self.config.verbose_level > 0 {
                safe_eprintln!(
                    "TPA: {} fixed point verified safe at power {}",
                    kind_name,
                    power
                );
            }
            true
        } else {
            if self.config.verbose_level > 1 {
                safe_eprintln!(
                    "TPA: {} containment holds but safety NOT verified at power {}",
                    kind_name,
                    power
                );
            }
            false
        }
    }
}

#[cfg(test)]
mod tests;
