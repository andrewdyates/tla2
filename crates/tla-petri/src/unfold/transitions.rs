// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transition expansion, variable discovery, binding enumeration, and arc
//! resolution for colored-net unfolding.

use std::collections::HashMap;

use crate::error::PnmlError;
use crate::hlpnml::{ColorExpr, ColorSort, ColorTerm, ColoredNet, GuardExpr};
use crate::petri_net::{Arc, PlaceIdx, TransitionIdx, TransitionInfo};

use super::context::UnfoldContext;
use super::places::PlaceUnfolding;
use super::{ColorValue, MAX_UNFOLDED_TRANSITIONS};

/// Result of unfolding all colored transitions.
pub(super) struct TransitionUnfolding {
    pub(super) transitions: Vec<TransitionInfo>,
    pub(super) transition_aliases: HashMap<String, Vec<TransitionIdx>>,
}

/// Unfold all colored transitions into P/T transitions.
pub(super) fn unfold_transitions(
    ctx: &UnfoldContext,
    colored: &ColoredNet,
    pu: &PlaceUnfolding,
) -> Result<TransitionUnfolding, PnmlError> {
    let mut transitions = Vec::new();
    let mut transition_aliases: HashMap<String, Vec<TransitionIdx>> = HashMap::new();

    let trans_variables = collect_transition_variables(colored, ctx);
    // Pre-compute place id set for arc direction detection.
    let place_ids: std::collections::HashSet<&str> =
        colored.places.iter().map(|p| p.id.as_str()).collect();

    for ct in &colored.transitions {
        let vars = trans_variables.get(&ct.id).cloned().unwrap_or_default();

        let bindings = ctx.enumerate_bindings(&vars, &ct.guard)?;

        let mut alias_indices = Vec::with_capacity(bindings.len());

        for binding in &bindings {
            let tidx = TransitionIdx(transitions.len() as u32);

            if transitions.len() >= MAX_UNFOLDED_TRANSITIONS {
                return Err(PnmlError::UnsupportedNetType {
                    net_type: format!(
                        "unfolded net exceeds {} transitions (model too large)",
                        MAX_UNFOLDED_TRANSITIONS
                    ),
                });
            }

            let binding_suffix = ctx.binding_suffix(&vars, binding);
            let unfolded_id = format!("{}_{}", ct.id, binding_suffix);

            let inputs = resolve_arcs_for_binding(
                colored,
                &ct.id,
                true,
                binding,
                &vars,
                ctx,
                &pu.place_map,
                &place_ids,
                &pu.place_sort_ids,
            )?;
            let outputs = resolve_arcs_for_binding(
                colored,
                &ct.id,
                false,
                binding,
                &vars,
                ctx,
                &pu.place_map,
                &place_ids,
                &pu.place_sort_ids,
            )?;

            transitions.push(TransitionInfo {
                id: unfolded_id,
                name: None,
                inputs,
                outputs,
            });

            alias_indices.push(tidx);
        }

        transition_aliases.insert(ct.id.clone(), alias_indices.clone());
        if let Some(ref name) = ct.name {
            if name != &ct.id {
                transition_aliases.insert(name.clone(), alias_indices);
            }
        }
    }

    Ok(TransitionUnfolding {
        transitions,
        transition_aliases,
    })
}

// ---------------------------------------------------------------------------
// Binding enumeration and guard evaluation (impl UnfoldContext)
// ---------------------------------------------------------------------------

impl UnfoldContext {
    /// Enumerate all valid variable bindings for a transition.
    pub(super) fn enumerate_bindings(
        &self,
        vars: &[(String, String)], // (var_id, sort_id)
        guard: &Option<GuardExpr>,
    ) -> Result<Vec<Vec<ColorValue>>, PnmlError> {
        if vars.is_empty() {
            return Ok(vec![vec![]]);
        }

        let mut cardinalities = Vec::with_capacity(vars.len());
        for (_, sort_id) in vars {
            let sort = self
                .sorts
                .get(sort_id)
                .ok_or_else(|| PnmlError::MissingElement(format!("sort '{sort_id}' not found")))?;
            cardinalities.push(self.sort_cardinality(sort)?);
        }

        let mut bindings = Vec::new();
        let mut current = vec![0usize; vars.len()];

        loop {
            let var_map: HashMap<&str, ColorValue> = vars
                .iter()
                .zip(current.iter())
                .map(|((var_id, _), &val)| (var_id.as_str(), val))
                .collect();

            if self.eval_guard(guard, &var_map) {
                bindings.push(current.clone());
            }

            // Increment counter (odometer style).
            let mut carry = true;
            for i in (0..vars.len()).rev() {
                if carry {
                    current[i] += 1;
                    if current[i] >= cardinalities[i] {
                        current[i] = 0;
                    } else {
                        carry = false;
                    }
                }
            }
            if carry {
                break;
            }
        }

        Ok(bindings)
    }

    /// Evaluate a guard under a variable binding.
    fn eval_guard(&self, guard: &Option<GuardExpr>, binding: &HashMap<&str, ColorValue>) -> bool {
        match guard {
            None => true,
            Some(expr) => self.eval_guard_expr(expr, binding),
        }
    }

    fn eval_guard_expr(&self, expr: &GuardExpr, binding: &HashMap<&str, ColorValue>) -> bool {
        match expr {
            GuardExpr::True => true,
            GuardExpr::And(children) => children.iter().all(|c| self.eval_guard_expr(c, binding)),
            GuardExpr::Or(children) => children.iter().any(|c| self.eval_guard_expr(c, binding)),
            GuardExpr::Not(inner) => !self.eval_guard_expr(inner, binding),
            GuardExpr::Equality(lhs, rhs) => {
                self.eval_color_value(lhs, binding) == self.eval_color_value(rhs, binding)
            }
            GuardExpr::Inequality(lhs, rhs) => {
                self.eval_color_value(lhs, binding) != self.eval_color_value(rhs, binding)
            }
            GuardExpr::LessThan(lhs, rhs) => {
                match (
                    self.eval_color_value(lhs, binding),
                    self.eval_color_value(rhs, binding),
                ) {
                    (Some(l), Some(r)) => l < r,
                    _ => false,
                }
            }
            GuardExpr::LessThanOrEqual(lhs, rhs) => {
                match (
                    self.eval_color_value(lhs, binding),
                    self.eval_color_value(rhs, binding),
                ) {
                    (Some(l), Some(r)) => l <= r,
                    _ => false,
                }
            }
            GuardExpr::GreaterThan(lhs, rhs) => {
                match (
                    self.eval_color_value(lhs, binding),
                    self.eval_color_value(rhs, binding),
                ) {
                    (Some(l), Some(r)) => l > r,
                    _ => false,
                }
            }
            GuardExpr::GreaterThanOrEqual(lhs, rhs) => {
                match (
                    self.eval_color_value(lhs, binding),
                    self.eval_color_value(rhs, binding),
                ) {
                    (Some(l), Some(r)) => l >= r,
                    _ => false,
                }
            }
        }
    }

    /// Create a human-readable binding suffix for unfolded transition IDs.
    pub(super) fn binding_suffix(
        &self,
        vars: &[(String, String)],
        binding: &[ColorValue],
    ) -> String {
        if vars.is_empty() {
            return "0".to_string();
        }

        vars.iter()
            .zip(binding.iter())
            .map(|((_, sort_id), &val)| {
                if let Some(sort) = self.sorts.get(sort_id) {
                    self.sort_value_name(sort, val)
                        .unwrap_or_else(|_| val.to_string())
                } else {
                    val.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join("_")
    }
}

// ---------------------------------------------------------------------------
// Variable collection
// ---------------------------------------------------------------------------

/// Collect variables used by each transition (from arc inscriptions and guards).
fn collect_transition_variables(
    colored: &ColoredNet,
    ctx: &UnfoldContext,
) -> HashMap<String, Vec<(String, String)>> {
    let mut result: HashMap<String, Vec<(String, String)>> = HashMap::new();

    let trans_ids: std::collections::HashSet<&str> =
        colored.transitions.iter().map(|t| t.id.as_str()).collect();

    for arc in &colored.arcs {
        let trans_id = if trans_ids.contains(arc.source.as_str()) {
            &arc.source
        } else if trans_ids.contains(arc.target.as_str()) {
            &arc.target
        } else {
            continue;
        };

        let entry = result.entry(trans_id.clone()).or_default();
        collect_vars_from_expr(&arc.inscription, entry, ctx);
    }

    // Also collect from guards.
    for ct in &colored.transitions {
        if let Some(ref guard) = ct.guard {
            let entry = result.entry(ct.id.clone()).or_default();
            collect_vars_from_guard(guard, entry, ctx);
        }
    }

    // Deduplicate while preserving order.
    for vars in result.values_mut() {
        let mut seen = std::collections::HashSet::new();
        vars.retain(|(var_id, _)| seen.insert(var_id.clone()));
    }

    result
}

fn collect_vars_from_expr(expr: &ColorExpr, vars: &mut Vec<(String, String)>, ctx: &UnfoldContext) {
    match expr {
        ColorExpr::All { .. } => {}
        ColorExpr::NumberOf { color, .. } => {
            collect_vars_from_term(color, vars, ctx);
        }
        ColorExpr::Add(children) => {
            for child in children {
                collect_vars_from_expr(child, vars, ctx);
            }
        }
    }
}

fn collect_vars_from_term(term: &ColorTerm, vars: &mut Vec<(String, String)>, ctx: &UnfoldContext) {
    match term {
        ColorTerm::Variable(var_id) => {
            if let Some(sort_id) = ctx.var_sorts.get(var_id) {
                vars.push((var_id.clone(), sort_id.clone()));
            }
        }
        ColorTerm::Tuple(terms) => {
            for term in terms {
                collect_vars_from_term(term, vars, ctx);
            }
        }
        ColorTerm::Predecessor(inner) | ColorTerm::Successor(inner) => {
            collect_vars_from_term(inner, vars, ctx);
        }
        ColorTerm::UserConstant(_) | ColorTerm::DotConstant => {}
    }
}

fn collect_vars_from_guard(
    guard: &GuardExpr,
    vars: &mut Vec<(String, String)>,
    ctx: &UnfoldContext,
) {
    match guard {
        GuardExpr::True => {}
        GuardExpr::And(children) | GuardExpr::Or(children) => {
            for child in children {
                collect_vars_from_guard(child, vars, ctx);
            }
        }
        GuardExpr::Not(inner) => collect_vars_from_guard(inner, vars, ctx),
        GuardExpr::Equality(lhs, rhs)
        | GuardExpr::Inequality(lhs, rhs)
        | GuardExpr::LessThan(lhs, rhs)
        | GuardExpr::LessThanOrEqual(lhs, rhs)
        | GuardExpr::GreaterThan(lhs, rhs)
        | GuardExpr::GreaterThanOrEqual(lhs, rhs) => {
            collect_vars_from_term(lhs, vars, ctx);
            collect_vars_from_term(rhs, vars, ctx);
        }
    }
}

// ---------------------------------------------------------------------------
// Arc resolution
// ---------------------------------------------------------------------------

/// Resolve arcs for a specific transition binding.
///
/// `is_input`: true for place→transition arcs, false for transition→place.
fn resolve_arcs_for_binding(
    colored: &ColoredNet,
    trans_id: &str,
    is_input: bool,
    binding: &[ColorValue],
    vars: &[(String, String)],
    ctx: &UnfoldContext,
    place_map: &HashMap<(String, ColorValue), PlaceIdx>,
    place_ids: &std::collections::HashSet<&str>,
    place_sort_ids: &HashMap<String, String>,
) -> Result<Vec<Arc>, PnmlError> {
    let var_map: HashMap<&str, ColorValue> = vars
        .iter()
        .zip(binding.iter())
        .map(|((var_id, _), &val)| (var_id.as_str(), val))
        .collect();

    let mut arcs = Vec::new();

    for colored_arc in &colored.arcs {
        let (place_id, matches) = if is_input {
            if colored_arc.target != trans_id {
                continue;
            }
            if !place_ids.contains(colored_arc.source.as_str()) {
                continue;
            }
            (&colored_arc.source, true)
        } else {
            if colored_arc.source != trans_id {
                continue;
            }
            if !place_ids.contains(colored_arc.target.as_str()) {
                continue;
            }
            (&colored_arc.target, true)
        };

        if !matches {
            continue;
        }

        let place_sort_id = place_sort_ids
            .get(place_id)
            .ok_or_else(|| PnmlError::MissingElement(format!("sort for place '{place_id}'")))?;
        let place_sort = ctx
            .sorts
            .get(place_sort_id)
            .ok_or_else(|| PnmlError::MissingElement(format!("sort '{place_sort_id}'")))?;
        let contributions = eval_inscription(&colored_arc.inscription, &var_map, ctx, place_sort)?;

        for (color_val, weight) in contributions {
            if let Some(&pidx) = place_map.get(&(place_id.clone(), color_val)) {
                if let Some(existing) = arcs.iter_mut().find(|a: &&mut Arc| a.place == pidx) {
                    existing.weight += weight;
                } else {
                    arcs.push(Arc {
                        place: pidx,
                        weight,
                    });
                }
            }
        }
    }

    Ok(arcs)
}

/// Evaluate an inscription expression under a binding.
///
/// Returns a list of (color_value, weight) pairs.
fn eval_inscription(
    expr: &ColorExpr,
    binding: &HashMap<&str, ColorValue>,
    ctx: &UnfoldContext,
    target_sort: &ColorSort,
) -> Result<Vec<(ColorValue, u64)>, PnmlError> {
    match expr {
        ColorExpr::All { sort_id } => {
            let sort = ctx
                .sorts
                .get(sort_id)
                .ok_or_else(|| PnmlError::MissingElement(format!("sort '{sort_id}' not found")))?;
            Ok((0..ctx.sort_cardinality(sort)?).map(|i| (i, 1)).collect())
        }
        ColorExpr::NumberOf { count, color } => {
            if let Some(val) = ctx.eval_color_value_for_sort(color, binding, target_sort)? {
                Ok(vec![(val, *count)])
            } else {
                Ok(vec![])
            }
        }
        ColorExpr::Add(children) => {
            let mut result = Vec::new();
            for child in children {
                let child_result = eval_inscription(child, binding, ctx, target_sort)?;
                for (color_val, weight) in child_result {
                    if let Some(existing) = result
                        .iter_mut()
                        .find(|(c, _): &&mut (ColorValue, u64)| *c == color_val)
                    {
                        existing.1 += weight;
                    } else {
                        result.push((color_val, weight));
                    }
                }
            }
            Ok(result)
        }
    }
}
