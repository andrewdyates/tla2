// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Time-indexed variable versioning, unrolling, and transition system accessors.

use super::TransitionSystem;
use crate::{ChcExpr, ChcSort, ChcVar};
use rustc_hash::FxHashSet;

impl TransitionSystem {
    /// Create a time-indexed version of a variable.
    ///
    /// - Time 0: returns the original variable (`x`)
    /// - Time t>0: returns `x_t`
    ///
    /// This convention matches standard BMC/KIND unrolling.
    pub(crate) fn version_var(var: &ChcVar, k: usize) -> ChcVar {
        if k == 0 {
            var.clone()
        } else {
            ChcVar::new(format!("{}_{}", var.name, k), var.sort.clone())
        }
    }

    /// Version an expression for timestep k.
    ///
    /// Substitutes all state variables with their time-indexed versions.
    pub(crate) fn version_expr(expr: &ChcExpr, vars: &[ChcVar], k: usize) -> ChcExpr {
        let substitutions: Vec<_> = vars
            .iter()
            .map(|v| (v.clone(), ChcExpr::var(Self::version_var(v, k))))
            .collect();
        expr.substitute(&substitutions)
    }

    /// Version local (non-canonical) variables in an expression per timestep.
    ///
    /// After `version_expr` has handled canonical state variables, any remaining
    /// free variables are clause-local existentials. When the same formula is
    /// instantiated at multiple timesteps (e.g., Tr(0) ∧ Tr(1)), these locals
    /// collide and add spurious constraints. This function gives each timestep's
    /// locals unique names by appending `__{tag}{k}`.
    ///
    /// The `canonical_vars` slice lists base state variables. Variables matching
    /// these names (or their versioned forms like "v0_1", "v0_2") are excluded
    /// from renaming. `next_vars` optionally lists next-state variables to also
    /// exclude.
    ///
    /// Fixes #6789: Kind engine false-Safe from local variable collision across
    /// BMC unrollings.
    fn version_local_vars(
        expr: &ChcExpr,
        canonical_vars: &[ChcVar],
        next_vars: Option<&[ChcVar]>,
        k: usize,
        tag: &str,
    ) -> ChcExpr {
        let all_vars = expr.vars();

        // Build set of state variable names that should NOT be versioned.
        // These are canonical vars at various timesteps (v0, v0_1, v0_2, ...).
        let canonical_base_names: FxHashSet<&str> =
            canonical_vars.iter().map(|v| v.name.as_str()).collect();

        let is_canonical = |name: &str| -> bool {
            // Direct match: v0, v1, etc.
            if canonical_base_names.contains(name) {
                return true;
            }
            // Versioned match: v0_1, v0_2, etc.
            if let Some(base) = name.rsplit_once('_') {
                if base.1.chars().all(|c| c.is_ascii_digit())
                    && canonical_base_names.contains(base.0)
                {
                    return true;
                }
            }
            false
        };

        let substitutions: Vec<(ChcVar, ChcExpr)> = all_vars
            .into_iter()
            .filter(|v| {
                if is_canonical(&v.name) {
                    return false;
                }
                if let Some(nvars) = next_vars {
                    if nvars.iter().any(|nv| nv.name == v.name) {
                        return false;
                    }
                }
                true
            })
            .map(|v| {
                let versioned = ChcVar::new(format!("{}__{}{}", v.name, tag, k), v.sort.clone());
                (v, ChcExpr::var(versioned))
            })
            .collect();

        if substitutions.is_empty() {
            expr.clone()
        } else {
            expr.substitute(&substitutions)
        }
    }

    /// Send formula through time by k steps.
    ///
    /// Convenience method that versions using this system's variables.
    pub(crate) fn send_through_time(&self, formula: &ChcExpr, k: usize) -> ChcExpr {
        Self::version_expr(formula, &self.vars, k)
    }

    /// Rename state variables at exactly one timestep to another timestep.
    ///
    /// This is more targeted than `shift_versioned_state_vars`: it only affects
    /// variables at exactly `from_k`, leaving all other timesteps unchanged.
    ///
    /// Used by TPA for:
    /// - `rename_state_vars_at(expr, 1, 2)`: shifts v1 → v2 (Golem's `shiftOnlyNextVars`)
    /// - `rename_state_vars_at(expr, 2, 1)`: shifts v2 → v1 (Golem's `cleanInterpolant`)
    ///
    /// Part of #1008.
    pub(crate) fn rename_state_vars_at(
        &self,
        expr: &ChcExpr,
        from_k: usize,
        to_k: usize,
    ) -> ChcExpr {
        if from_k == to_k {
            return expr.clone();
        }

        let subst: Vec<(ChcVar, ChcExpr)> = self
            .vars
            .iter()
            .map(|v| {
                let from_var = Self::version_var(v, from_k);
                let to_var = Self::version_var(v, to_k);
                (from_var, ChcExpr::var(to_var))
            })
            .collect();

        expr.substitute(&subst)
    }

    /// Shift state variables by `delta` timesteps.
    ///
    /// This operates on the naming scheme produced by `version_var`:
    /// - Time 0: `x`
    /// - Time t>0: `x_t`
    ///
    /// Only canonical `x_<pos>` suffixes are treated as time indices. This avoids
    /// rewriting original variables like `x_0`, `x_-1`, `x_01`, or `x_+1`.
    ///
    /// The shift is clamped at time 0 to avoid creating negative time indices.
    pub(crate) fn shift_versioned_state_vars(&self, expr: &ChcExpr, delta: i32) -> ChcExpr {
        fn split_base_and_time(name: &str) -> (&str, i32) {
            if let Some((base, suffix)) = name.rsplit_once('_') {
                let bytes = suffix.as_bytes();
                let is_canonical_pos_int = !bytes.is_empty()
                    && bytes[0].is_ascii_digit()
                    && (bytes[0] != b'0' || bytes.len() == 1)
                    && bytes.iter().all(u8::is_ascii_digit);

                if is_canonical_pos_int {
                    if let Ok(t) = suffix.parse::<i32>() {
                        // Treat only strictly-positive suffixes as time indices.
                        //
                        // This matches `version_var` which uses `x` (not `x_0`) for time 0.
                        if t > 0 {
                            return (base, t);
                        }
                    }
                }
            }
            (name, 0)
        }

        let state_bases: FxHashSet<&str> = self.vars.iter().map(|v| v.name.as_str()).collect();

        let subst: Vec<(ChcVar, ChcExpr)> = expr
            .vars()
            .into_iter()
            .filter_map(|v| {
                let (base, t) = split_base_and_time(&v.name);
                if !state_bases.contains(base) {
                    return None;
                }

                let new_t = (t + delta).max(0);
                let new_name = if new_t == 0 {
                    base.to_string()
                } else {
                    format!("{base}_{new_t}")
                };
                if new_name == v.name {
                    return None;
                }
                let sort = v.sort.clone();
                Some((v, ChcExpr::var(ChcVar::new(new_name, sort))))
            })
            .collect();

        if subst.is_empty() {
            return expr.clone();
        }
        expr.substitute(&subst)
    }

    // ========================================================================
    // Unrolling
    // ========================================================================

    /// Create the k-step unrolled transition relation.
    ///
    /// Returns: `trans@0 ∧ trans@1 ∧ ... ∧ trans@(k-1)`
    ///
    /// Where `trans@i` is the transition from time `i` to time `i+1`.
    pub(crate) fn k_transition(&self, k: usize) -> ChcExpr {
        if k == 0 {
            return ChcExpr::Bool(true);
        }

        let mut conjuncts = Vec::with_capacity(k);
        for i in 0..k {
            conjuncts.push(self.transition_at(i));
        }

        ChcExpr::and_all(conjuncts)
    }

    /// Create transition constraint from step k to step k+1.
    ///
    /// Substitutes:
    /// - `vars` → `vars_k`
    /// - `vars_next` → `vars_{k+1}`
    pub(crate) fn transition_at(&self, k: usize) -> ChcExpr {
        let mut substitutions: Vec<_> = self
            .vars
            .iter()
            .map(|v| (v.clone(), ChcExpr::var(Self::version_var(v, k))))
            .collect();

        // Handle _next variables
        let mut canonical_names: FxHashSet<String> =
            self.vars.iter().map(|v| v.name.clone()).collect();
        for v in &self.vars {
            let next_var = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
            canonical_names.insert(next_var.name.clone());
            substitutions.push((next_var, ChcExpr::var(Self::version_var(v, k + 1))));
            // Also recognize versioned forms (v_0, v_1, v_2, ...) as canonical.
            // TransitionSystems created via `new()` may use numeric suffixes (x_1)
            // instead of _next (x_next) for next-state variables. Without this,
            // `x_1` in the transition would be erroneously renamed as a local.
            canonical_names.insert(Self::version_var(v, k).name);
            canonical_names.insert(Self::version_var(v, k + 1).name);
        }

        // Version local (non-canonical) variables per timestep to avoid collisions
        // across unrollings (#6789). Without this, Tr(0) ∧ Tr(1) shares local vars,
        // adding spurious constraints that make reachable states unreachable.
        let all_vars = self.transition.vars();
        for v in all_vars {
            if !canonical_names.contains(&v.name) {
                let versioned = ChcVar::new(format!("{}__t{}", v.name, k), v.sort.clone());
                substitutions.push((v, ChcExpr::var(versioned)));
            }
        }

        self.transition.substitute(&substitutions)
    }

    /// Create init constraint at step k.
    pub(crate) fn init_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.init, &self.vars, k);
        // Version local variables per timestep (#6789)
        Self::version_local_vars(&versioned, &self.vars, None, k, "i")
    }

    /// Create query constraint at step k.
    pub(crate) fn query_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.query, &self.vars, k);
        // Version local variables per timestep (#6789)
        Self::version_local_vars(&versioned, &self.vars, None, k, "q")
    }

    /// Create ¬query at step k.
    ///
    /// Uses the raw (pre-mod-elimination) query to avoid free auxiliary
    /// variables in the negation. See `init_raw` field doc for details.
    pub(crate) fn neg_query_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.query_raw, &self.vars, k);
        let with_locals = Self::version_local_vars(&versioned, &self.vars, None, k, "nq");
        ChcExpr::not(with_locals)
    }

    /// Create ¬init at step k.
    ///
    /// Uses the raw (pre-mod-elimination) init to avoid free auxiliary
    /// variables in the negation. See `init_raw` field doc for details.
    pub(crate) fn neg_init_at(&self, k: usize) -> ChcExpr {
        let versioned = Self::version_expr(&self.init_raw, &self.vars, k);
        let with_locals = Self::version_local_vars(&versioned, &self.vars, None, k, "ni");
        ChcExpr::not(with_locals)
    }

    // ========================================================================
    // Variable Queries
    // ========================================================================

    /// Get all state variable names (for interpolation shared_vars).
    pub(crate) fn state_var_names(&self) -> FxHashSet<String> {
        self.vars.iter().map(|v| v.name.clone()).collect()
    }

    /// Get state variable names at timestep `k` (e.g. `x_1`) for interpolation boundaries.
    pub(crate) fn state_var_names_at(&self, k: usize) -> FxHashSet<String> {
        self.vars
            .iter()
            .map(|v| Self::version_var(v, k).name)
            .collect()
    }

    /// Get the state variables.
    pub(crate) fn state_vars(&self) -> &[ChcVar] {
        &self.vars
    }

    /// Get the raw (pre-mod-elimination) query.
    ///
    /// Used when negating the query: the raw form ensures `check_sat` handles
    /// mod elimination with properly scoped aux vars per call.
    pub(crate) fn query_raw(&self) -> &ChcExpr {
        &self.query_raw
    }

    /// Returns the first state sort unsupported by interpolation engines, if any.
    ///
    /// Interpolation-based engines (IMC, DAR) support Int, Real, BitVec, and
    /// Array sorts. Bool is rejected because Craig interpolation over 100+
    /// shared Boolean variables is inefficient (#5877). This scans state
    /// variables and returns the first unsupported sort for early rejection
    /// (#1940). BV support added (#5595, #5644).
    pub(crate) fn find_unsupported_interpolation_state_sort(&self) -> Option<ChcSort> {
        for var in self.state_vars() {
            match &var.sort {
                ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) | ChcSort::Array(_, _) => {
                    continue
                }
                sort => return Some(sort.clone()),
            }
        }
        None
    }

    /// Returns the first state sort unsupported by transition-system engines, if any.
    ///
    /// Non-interpolation engines (PDKIND, BMC) can handle Bool-state transition
    /// systems that arise from BvToBool preprocessing (#5877). This accepts
    /// Bool in addition to Int, Real, BitVec, and Array.
    pub(crate) fn find_unsupported_transition_state_sort(&self) -> Option<ChcSort> {
        for var in self.state_vars() {
            match &var.sort {
                ChcSort::Bool
                | ChcSort::Int
                | ChcSort::Real
                | ChcSort::BitVec(_)
                | ChcSort::Array(_, _) => continue,
                sort => return Some(sort.clone()),
            }
        }
        None
    }
}
