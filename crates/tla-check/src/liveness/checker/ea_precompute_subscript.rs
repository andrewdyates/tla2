// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Subscript value pre-computation for the EA precompute pass (#2364).
//!
//! Extracted from `ea_precompute.rs` to stay under the 500-line file limit.
//! Pre-populates the subscript value cache with StateChanged and ENABLED
//! subscript values for all unique (fingerprint, tag) pairs. This ensures
//! all StateChanged evaluations during the transition loop are cache hits,
//! preserving SUBST_CACHE warmth across ActionPred evaluations.

use super::live_expr::LiveExpr;
use super::LivenessChecker;
use crate::state::Fingerprint;
use rustc_hash::{FxHashMap, FxHashSet};

/// Information about a subscript-bearing sub-expression (StateChanged or ENABLED).
struct SubscriptInfo {
    subscript: std::sync::Arc<tla_core::Spanned<tla_core::ast::Expr>>,
    bindings: Option<crate::eval::BindingChain>,
    tag: u32,
}

/// Walk a `LiveExpr` tree and collect all `StateChanged` sub-expressions with subscripts.
fn collect_state_changed_subscripts(expr: &LiveExpr, out: &mut Vec<SubscriptInfo>) {
    match expr {
        LiveExpr::StateChanged {
            subscript: Some(sub),
            bindings,
            tag,
        } => {
            out.push(SubscriptInfo {
                subscript: std::sync::Arc::clone(sub),
                bindings: bindings.clone(),
                tag: *tag,
            });
        }
        LiveExpr::And(parts) | LiveExpr::Or(parts) => {
            for p in parts {
                collect_state_changed_subscripts(p, out);
            }
        }
        LiveExpr::Not(inner) => collect_state_changed_subscripts(inner, out),
        _ => {}
    }
}

/// Walk a `LiveExpr` tree and collect all `ENABLED` sub-expressions with subscripts.
/// Used for array-based fast path (#2364): pre-computing subscript values enables
/// O(1) subscript change detection during ENABLED evaluation.
fn collect_enabled_subscripts(expr: &LiveExpr, out: &mut Vec<SubscriptInfo>) {
    match expr {
        LiveExpr::Enabled {
            subscript: Some(sub),
            bindings,
            tag,
            ..
        } => {
            out.push(SubscriptInfo {
                subscript: std::sync::Arc::clone(sub),
                bindings: bindings.clone(),
                tag: *tag,
            });
        }
        LiveExpr::And(parts) | LiveExpr::Or(parts) => {
            for p in parts {
                collect_enabled_subscripts(p, out);
            }
        }
        LiveExpr::Not(inner) => collect_enabled_subscripts(inner, out),
        _ => {}
    }
}

/// Group subscript infos by expression pointer identity.
///
/// Many WF/SF conditions share the same subscript expression (e.g., `vars`).
/// Instead of evaluating the same expression once per tag, group tags by
/// Arc pointer identity and evaluate once per unique expression per state.
/// For AllocatorImplementation with 115 WF conditions all using `vars`,
/// this reduces subscript evaluations per state from 115 to ~1.
///
/// Safety: The subscript expression for `<<A>>_v` is `v`, which is typically
/// a pure state variable tuple that does NOT reference quantified bindings.
/// Even when different WF conditions have different bindings (from quantified
/// fairness), the subscript `v` evaluates identically because it only reads
/// state variables. The grouping evaluates once using the representative's
/// bindings and clones the result to all tags in the group.
fn group_by_subscript_expr(infos: &[SubscriptInfo]) -> Vec<(usize, Vec<usize>)> {
    // Map from Arc raw pointer to (representative index, [all indices with same ptr])
    let mut groups: FxHashMap<usize, (usize, Vec<usize>)> = FxHashMap::default();
    for (idx, info) in infos.iter().enumerate() {
        let ptr = std::sync::Arc::as_ptr(&info.subscript) as usize;
        groups
            .entry(ptr)
            .and_modify(|(_, indices)| indices.push(idx))
            .or_insert((idx, vec![idx]));
    }
    groups.into_values().collect()
}

impl LivenessChecker {
    /// Pre-populate subscript value cache for all unique (fingerprint, tag) pairs.
    ///
    /// Ensures ALL StateChanged evaluations during the transition loop are
    /// cache hits, which preserves SUBST_CACHE warmth across ActionPred evaluations.
    /// Without this, each StateChanged miss switches to state_env=None (via
    /// with_explicit_env) and clears SUBST_CACHE, forcing the next ActionPred to
    /// rebuild the full INSTANCE chain from scratch (#2364).
    ///
    /// Optimized: groups tags by subscript expression pointer identity so that
    /// expressions shared across multiple WF/SF conditions (e.g., `vars`) are
    /// evaluated only once per state instead of once per tag per state.
    pub(super) fn precompute_subscript_values(
        &mut self,
        check_action: &[LiveExpr],
        action_used: &[bool],
        state_cache: &FxHashMap<Fingerprint, crate::state::State>,
    ) -> Result<(), crate::error::EvalError> {
        // Collect StateChanged + ENABLED subscripts from used check_action entries.
        let mut sc_infos: Vec<SubscriptInfo> = Vec::new();
        for (check_idx, check) in check_action.iter().enumerate() {
            if !action_used.get(check_idx).copied().unwrap_or(false) {
                continue;
            }
            collect_state_changed_subscripts(check, &mut sc_infos);
            collect_enabled_subscripts(check, &mut sc_infos);
        }

        // Deduplicate by tag (same tag = same expression).
        {
            let mut seen_tags: FxHashSet<u32> = FxHashSet::default();
            sc_infos.retain(|info| seen_tags.insert(info.tag));
        }

        if sc_infos.is_empty() {
            return Ok(());
        }

        // Group tags by subscript expression pointer identity.
        // For specs like AllocatorImplementation where 115 WF conditions all use
        // `vars` as the subscript, this reduces evaluations from 115× to 1× per state.
        let expr_groups = group_by_subscript_expr(&sc_infos);

        // Pre-compute subscript values.
        let registry_is_empty = self.ctx.var_registry().is_empty();
        if !registry_is_empty {
            let registry = self.ctx.var_registry().clone();
            for (fp, state) in state_cache {
                let values = state.to_values(&registry);
                let _guard = self.ctx.bind_state_array_guard(&values);
                for (repr_idx, group_indices) in &expr_groups {
                    let info = &sc_infos[*repr_idx];
                    // Part of #2895: BindingChain bindings survive closure/function entry.
                    let eval_ctx = match info.bindings {
                        Some(ref chain) => self.ctx.with_liveness_bindings(chain),
                        None => self.ctx.clone(),
                    };
                    let value = crate::eval::eval_entry(&eval_ctx, &info.subscript)?;
                    // Store the same value for all tags sharing this expression.
                    for &idx in group_indices {
                        super::subscript_cache::set_subscript_value_cache(
                            *fp,
                            sc_infos[idx].tag,
                            value.clone(),
                        );
                    }
                }
            }
        } else {
            // Fallback: HashMap-based for empty VarRegistry (tests)
            for (fp, state) in state_cache {
                // Fix #2780: Clear SUBST_CACHE before first-iteration
                // with_explicit_env (state_env=None, pointer 0). Prior
                // callers may have left stale entries keyed on pointer 0.
                crate::eval::clear_subst_cache();
                for (repr_idx, group_indices) in &expr_groups {
                    let info = &sc_infos[*repr_idx];
                    // Part of #2895: BindingChain bindings survive closure/function entry.
                    let eval_ctx = match info.bindings {
                        Some(ref chain) => self.ctx.with_liveness_bindings(chain),
                        None => self.ctx.clone(),
                    };
                    let mut env = eval_ctx.env().clone();
                    for (name, value) in state.vars() {
                        // Part of #2144: skip state vars that shadow local bindings.
                        if !eval_ctx.has_local_binding(name.as_ref()) {
                            env.insert(std::sync::Arc::clone(name), value.clone());
                        }
                    }
                    let ctx_with_state = eval_ctx.with_explicit_env(env);
                    let value = crate::eval::eval_entry(&ctx_with_state, &info.subscript)?;
                    // Store the same value for all tags sharing this expression.
                    for &idx in group_indices {
                        super::subscript_cache::set_subscript_value_cache(
                            *fp,
                            sc_infos[idx].tag,
                            value.clone(),
                        );
                    }
                }
                crate::eval::clear_subst_cache();
            }
        }

        Ok(())
    }
}
