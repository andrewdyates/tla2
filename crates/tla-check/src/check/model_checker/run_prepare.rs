// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-BFS preparation: constant binding, symmetry computation, VIEW validation,
//! invariant compilation, operator expansion, and action compilation.
//!
//! Extracted from `run.rs` to separate setup concerns from runtime dispatch
//! (Part of #2385). TLC keeps construction/init concerns in `ModelChecker` init
//! path; this module mirrors that boundary.

use super::super::api::{check_error_to_result, CheckResult, ResolvedSpec, INLINE_NEXT_NAME};
use super::super::check_error::CheckError;
use super::debug::debug_bytecode_vm;
#[cfg(debug_assertions)]
use super::debug::tla2_debug;
use super::fingerprint::BfsFingerprintDomain;
use super::mc_struct::ModelChecker;
use super::trace_detect::compute_uses_trace;
use crate::constants::bind_constants_from_config;
use crate::{ConfigCheckError, EvalCheckError};
use num_traits::ToPrimitive;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar, Expr, Module, OperatorDef, RecordFieldName};
use tla_core::name_intern::{intern_name, NameId};
// Part of #4267 Gate 1 Batch C: collapse Cranelift-backed JIT type paths.
use tla_jit::bytecode_lower::JitInvariantCache as JitInvariantCacheImpl;

fn collect_sequence_capacity_proofs(
    expr: &Expr,
    invariant: &str,
    registry: &crate::var_index::VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    proof_domains: &BTreeMap<String, Arc<[crate::Value]>>,
    scope: &mut ProofScope,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<crate::state::SequenceCapacityProof>,
) {
    match expr {
        Expr::And(left, right) => {
            collect_sequence_capacity_proofs(
                &left.node,
                invariant,
                registry,
                constants,
                op_defs,
                op_replacements,
                proof_domains,
                scope,
                visiting,
                out,
            );
            collect_sequence_capacity_proofs(
                &right.node,
                invariant,
                registry,
                constants,
                op_defs,
                op_replacements,
                proof_domains,
                scope,
                visiting,
                out,
            );
        }
        Expr::Forall(vars, body) => {
            if let Some(added) = push_bounded_quantifier_names(vars, proof_domains, scope) {
                collect_sequence_capacity_proofs(
                    &body.node,
                    invariant,
                    registry,
                    constants,
                    op_defs,
                    op_replacements,
                    proof_domains,
                    scope,
                    visiting,
                    out,
                );
                for name in added {
                    scope.pop(&name);
                }
            }
        }
        Expr::Leq(left, right) => {
            if let (Some((var_idx, path)), Some(max_len)) = (
                extract_bounded_sequence_path(&left.node, registry, scope, op_replacements),
                expr_usize_bound(&right.node, constants, op_replacements),
            ) {
                push_sequence_capacity_proof(
                    out,
                    crate::state::SequenceCapacityProof {
                        var_idx,
                        path,
                        max_len,
                        invariant: Arc::from(invariant),
                    },
                );
            }
        }
        Expr::Geq(left, right) => {
            if let (Some(max_len), Some((var_idx, path))) = (
                expr_usize_bound(&left.node, constants, op_replacements),
                extract_bounded_sequence_path(&right.node, registry, scope, op_replacements),
            ) {
                push_sequence_capacity_proof(
                    out,
                    crate::state::SequenceCapacityProof {
                        var_idx,
                        path,
                        max_len,
                        invariant: Arc::from(invariant),
                    },
                );
            }
        }
        Expr::Ident(name, _) if !scope.is_bound(name) => {
            collect_sequence_capacity_proofs_from_zero_arg_op(
                name,
                invariant,
                registry,
                constants,
                op_defs,
                op_replacements,
                proof_domains,
                scope,
                visiting,
                out,
            );
        }
        Expr::OpRef(name) => {
            collect_sequence_capacity_proofs_from_zero_arg_op(
                name,
                invariant,
                registry,
                constants,
                op_defs,
                op_replacements,
                proof_domains,
                scope,
                visiting,
                out,
            );
        }
        _ => {}
    }
}

fn collect_sequence_capacity_proofs_from_zero_arg_op(
    name: &str,
    invariant: &str,
    registry: &crate::var_index::VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    proof_domains: &BTreeMap<String, Arc<[crate::Value]>>,
    scope: &mut ProofScope,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<crate::state::SequenceCapacityProof>,
) {
    let Some((resolved_name, def)) = proof_safe_zero_arg_op_def(name, op_defs, op_replacements)
    else {
        return;
    };
    if !visiting.insert(resolved_name.to_owned()) {
        return;
    }
    collect_sequence_capacity_proofs(
        &def.body.node,
        invariant,
        registry,
        constants,
        op_defs,
        op_replacements,
        proof_domains,
        scope,
        visiting,
        out,
    );
    visiting.remove(resolved_name);
}

fn push_sequence_capacity_proof(
    out: &mut Vec<crate::state::SequenceCapacityProof>,
    proof: crate::state::SequenceCapacityProof,
) {
    if !out.iter().any(|existing| existing == &proof) {
        out.push(proof);
    }
}

#[derive(Default)]
struct ProofScope {
    bindings: BTreeMap<String, Vec<Option<Arc<[crate::Value]>>>>,
}

impl ProofScope {
    fn push(&mut self, name: String, homogeneous_domain: Option<Arc<[crate::Value]>>) {
        self.bindings
            .entry(name)
            .or_default()
            .push(homogeneous_domain);
    }

    fn pop(&mut self, name: &str) {
        if let Some(stack) = self.bindings.get_mut(name) {
            stack.pop();
            if stack.is_empty() {
                self.bindings.remove(name);
            }
        }
    }

    fn is_bound(&self, name: &str) -> bool {
        self.bindings
            .get(name)
            .is_some_and(|stack| !stack.is_empty())
    }

    fn homogeneous_bound_domain(&self, name: &str) -> Option<Arc<[crate::Value]>> {
        self.bindings
            .get(name)
            .and_then(|stack| stack.last())
            .and_then(|domain| domain.as_ref().map(Arc::clone))
    }
}

fn push_bounded_quantifier_names(
    vars: &[BoundVar],
    proof_domains: &BTreeMap<String, Arc<[crate::Value]>>,
    scope: &mut ProofScope,
) -> Option<Vec<String>> {
    let mut added = Vec::new();
    for var in vars {
        let homogeneous_domain = bound_var_full_homogeneous_domain(var, proof_domains, scope);
        homogeneous_domain.as_ref()?;
        match &var.pattern {
            None | Some(BoundPattern::Var(_)) => {
                let name = var.name.node.clone();
                scope.push(name.clone(), homogeneous_domain);
                added.push(name);
            }
            Some(BoundPattern::Tuple(_)) => return None,
        }
    }
    Some(added)
}

fn bound_var_full_homogeneous_domain(
    var: &BoundVar,
    proof_domains: &BTreeMap<String, Arc<[crate::Value]>>,
    scope: &ProofScope,
) -> Option<Arc<[crate::Value]>> {
    var.domain
        .as_ref()
        .and_then(|domain| full_homogeneous_domain_values(&domain.node, proof_domains, scope))
}

fn full_homogeneous_domain_values(
    expr: &Expr,
    proof_domains: &BTreeMap<String, Arc<[crate::Value]>>,
    scope: &ProofScope,
) -> Option<Arc<[crate::Value]>> {
    match expr {
        Expr::Ident(name, _) if !scope.is_bound(name) => proof_domains.get(name).cloned(),
        _ => None,
    }
}

fn extract_bounded_sequence_path(
    expr: &Expr,
    registry: &crate::var_index::VarRegistry,
    scope: &ProofScope,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
) -> Option<(usize, Vec<crate::state::SequenceCapacityPathStep>)> {
    let Expr::Apply(op, args) = expr else {
        return None;
    };
    if args.len() != 1 || !is_len_operator(&op.node, op_replacements) {
        return None;
    }
    let mut used_bindings = BTreeSet::new();
    extract_state_path(&args[0].node, registry, scope, &mut used_bindings)
}

fn is_len_operator(
    expr: &Expr,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
) -> bool {
    matches!(
        expr,
        Expr::Ident(name, _) | Expr::OpRef(name)
            if matches!(resolve_proof_op_name(name, op_replacements), Some("Len"))
    )
}

fn extract_state_path(
    expr: &Expr,
    registry: &crate::var_index::VarRegistry,
    scope: &ProofScope,
    used_bindings: &mut BTreeSet<String>,
) -> Option<(usize, Vec<crate::state::SequenceCapacityPathStep>)> {
    match expr {
        Expr::StateVar(_, idx, _) => Some((*idx as usize, Vec::new())),
        Expr::Ident(name, _) if !scope.is_bound(name) => {
            registry.get(name).map(|idx| (idx.0 as usize, Vec::new()))
        }
        Expr::FuncApply(func, arg) => {
            let (binding, domain) = bound_subscript_arg(&arg.node, scope)?;
            if !used_bindings.insert(binding) {
                return None;
            }
            let (var_idx, mut path) =
                extract_state_path(&func.node, registry, scope, used_bindings)?;
            path.push(crate::state::SequenceCapacityPathStep::HomogeneousRange { domain });
            Some((var_idx, path))
        }
        Expr::RecordAccess(base, field) => {
            let (var_idx, mut path) =
                extract_state_path(&base.node, registry, scope, used_bindings)?;
            path.push(crate::state::SequenceCapacityPathStep::RecordField(
                record_field_name(field),
            ));
            Some((var_idx, path))
        }
        _ => None,
    }
}

fn bound_subscript_arg(expr: &Expr, scope: &ProofScope) -> Option<(String, Arc<[crate::Value]>)> {
    match expr {
        Expr::Ident(name, _) => Some((name.clone(), scope.homogeneous_bound_domain(name)?)),
        _ => None,
    }
}

fn record_field_name(field: &RecordFieldName) -> Arc<str> {
    Arc::from(field.name.node.as_str())
}

fn expr_usize_bound(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
) -> Option<usize> {
    match expr {
        Expr::Int(n) => n.to_usize(),
        Expr::Ident(name, name_id) => {
            proof_domain_scalar_constant_value(name, *name_id, constants, op_replacements)
                .as_ref()
                .and_then(value_usize_bound)
        }
        _ => None,
    }
}

fn value_usize_bound(value: &crate::Value) -> Option<usize> {
    match value {
        crate::Value::SmallInt(n) => usize::try_from(*n).ok(),
        crate::Value::Int(n) => n.to_usize(),
        _ => None,
    }
}

fn proof_domain_values_from_value(value: &crate::Value) -> Option<Vec<crate::Value>> {
    if value.set_len()?.to_usize()? > 63 {
        return None;
    }
    let set = value.to_sorted_set()?;
    normalize_proof_domain_values(set.iter().cloned().collect())
}

fn expression_proof_domain_values(
    expr: &Expr,
    op_defs: &tla_core::OpEnv,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    visiting: &mut BTreeSet<String>,
) -> Option<Vec<crate::Value>> {
    match expr {
        Expr::SetEnum(elems) => {
            let values: Option<Vec<crate::Value>> = elems
                .iter()
                .map(|elem| proof_domain_scalar_value(&elem.node, constants, op_replacements))
                .collect();
            normalize_proof_domain_values(values?)
        }
        Expr::Range(left, right) => {
            let lo = proof_domain_int_value(&left.node, constants, op_replacements)?;
            let hi = proof_domain_int_value(&right.node, constants, op_replacements)?;
            if hi < lo || hi - lo >= 63 {
                return None;
            }
            normalize_proof_domain_values((lo..=hi).map(crate::Value::SmallInt).collect())
        }
        Expr::SetMinus(left, right) => {
            let mut values = expression_proof_domain_values(
                &left.node,
                op_defs,
                constants,
                op_replacements,
                visiting,
            )?;
            let remove = expression_proof_domain_values(
                &right.node,
                op_defs,
                constants,
                op_replacements,
                visiting,
            )?;
            values.retain(|value| !remove.contains(value));
            normalize_proof_domain_values(values)
        }
        Expr::Ident(name, name_id) => {
            if let Some(values) =
                proof_domain_constant_values(name, *name_id, constants, op_replacements)
            {
                return Some(values);
            }
            let resolved = resolve_proof_op_name(name, op_replacements)?;
            if !visiting.insert(resolved.to_string()) {
                return None;
            }
            let result = op_defs.get(resolved).and_then(|def| {
                let def = def.as_ref();
                (def.params.is_empty() && !def.contains_prime && !def.is_recursive)
                    .then(|| {
                        expression_proof_domain_values(
                            &def.body.node,
                            op_defs,
                            constants,
                            op_replacements,
                            visiting,
                        )
                    })
                    .flatten()
            });
            visiting.remove(resolved);
            result
        }
        _ => None,
    }
}

fn resolve_proof_op_name<'a>(
    name: &'a str,
    op_replacements: &'a tla_core::kani_types::HashMap<String, String>,
) -> Option<&'a str> {
    let mut current = name;
    let mut seen = BTreeSet::new();
    loop {
        if !seen.insert(current) {
            return None;
        }
        let Some(next) = op_replacements.get(current) else {
            return Some(current);
        };
        current = next.as_str();
    }
}

fn proof_domain_constant_values(
    name: &str,
    name_id: NameId,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
) -> Option<Vec<crate::Value>> {
    let resolved = resolve_proof_op_name(name, op_replacements)?;
    let resolved_id = intern_name(resolved);
    if let Some(values) = constants
        .get(&resolved_id)
        .and_then(proof_domain_values_from_value)
    {
        return Some(values);
    }

    let id = if name_id == NameId::INVALID {
        intern_name(name)
    } else {
        name_id
    };
    if id != resolved_id && !op_replacements.contains_key(name) {
        constants.get(&id).and_then(proof_domain_values_from_value)
    } else {
        None
    }
}

fn proof_safe_zero_arg_op_def<'a>(
    name: &'a str,
    op_defs: &'a tla_core::OpEnv,
    op_replacements: &'a tla_core::kani_types::HashMap<String, String>,
) -> Option<(&'a str, &'a OperatorDef)> {
    let resolved = resolve_proof_op_name(name, op_replacements)?;
    let def = op_defs.get(resolved)?.as_ref();
    (def.params.is_empty() && !def.contains_prime && !def.has_primed_param && !def.is_recursive)
        .then_some((resolved, def))
}

fn proof_domain_scalar_value(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
) -> Option<crate::Value> {
    match expr {
        Expr::Bool(value) => Some(crate::Value::Bool(*value)),
        Expr::Int(value) => value
            .to_i64()
            .map(crate::Value::SmallInt)
            .or_else(|| Some(crate::Value::Int(Arc::new(value.clone())))),
        Expr::String(value) => Some(crate::Value::String(Arc::from(value.as_str()))),
        Expr::Ident(name, name_id) => {
            proof_domain_scalar_constant_value(name, *name_id, constants, op_replacements)
        }
        _ => None,
    }
}

fn proof_domain_int_value(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
) -> Option<i64> {
    let value = proof_domain_scalar_value(expr, constants, op_replacements)?;
    match &value {
        crate::Value::SmallInt(value) => Some(*value),
        crate::Value::Int(value) => value.to_i64(),
        _ => None,
    }
}

fn proof_domain_scalar_constant_value(
    name: &str,
    name_id: NameId,
    constants: &tla_core::kani_types::HashMap<NameId, crate::Value>,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
) -> Option<crate::Value> {
    let resolved = resolve_proof_op_name(name, op_replacements)?;
    let resolved_id = intern_name(resolved);
    if let Some(value) = constants
        .get(&resolved_id)
        .filter(|value| is_proof_scalar_value(value))
        .cloned()
    {
        return Some(value);
    }

    let id = if name_id == NameId::INVALID {
        intern_name(name)
    } else {
        name_id
    };
    if id != resolved_id && !op_replacements.contains_key(name) {
        constants
            .get(&id)
            .filter(|value| is_proof_scalar_value(value))
            .cloned()
    } else {
        None
    }
}

fn normalize_proof_domain_values(mut values: Vec<crate::Value>) -> Option<Vec<crate::Value>> {
    if values.is_empty() || values.len() > 63 || !values.iter().all(is_proof_scalar_value) {
        return None;
    }
    values.sort();
    values.dedup();
    Some(values)
}

fn is_proof_scalar_value(value: &crate::Value) -> bool {
    matches!(
        value,
        crate::Value::Bool(_)
            | crate::Value::SmallInt(_)
            | crate::Value::Int(_)
            | crate::Value::String(_)
            | crate::Value::ModelValue(_)
    )
}

impl ModelChecker<'_> {
    /// Register an inline NEXT expression from a ResolvedSpec.
    ///
    /// Delegates CST lowering and OperatorDef construction to the shared
    /// `checker_ops::lower_inline_next`, then registers the result in both
    /// the module's op_defs and the evaluation context.
    pub fn register_inline_next(&mut self, resolved: &ResolvedSpec) -> Result<(), CheckError> {
        let op_def = match crate::checker_ops::lower_inline_next(
            resolved.next_node.as_ref(),
            self.ctx.var_registry(),
        ) {
            None => return Ok(()),
            Some(result) => result?,
        };

        // Register the operator in our definitions and evaluation context.
        self.module
            .op_defs
            .insert(INLINE_NEXT_NAME.to_string(), op_def.clone());
        self.ctx.define_op(INLINE_NEXT_NAME.to_string(), op_def);

        Ok(())
    }

    /// Validate and cache the VIEW operator name from the configuration.
    ///
    /// Delegates to `checker_ops::validate_view_operator` — the single shared
    /// implementation used by both sequential and parallel checkers (Part of #810).
    pub(super) fn validate_view(&mut self) {
        self.compiled.cached_view_name =
            crate::checker_ops::validate_view_operator(&self.ctx, self.config);
        self.refresh_liveness_mode();
    }

    fn configured_sequence_capacity_proofs(&self) -> Vec<crate::state::SequenceCapacityProof> {
        let mut proofs = Vec::new();
        let proof_domains = self.named_homogeneous_proof_domains();
        let op_defs = &self.ctx.shared().ops;
        let op_replacements = self.ctx.op_replacements();
        for invariant in &self.config.invariants {
            let Some((resolved_name, def)) =
                proof_safe_zero_arg_op_def(invariant, op_defs, op_replacements)
            else {
                continue;
            };
            let mut scope = ProofScope::default();
            let mut visiting = BTreeSet::from([resolved_name.to_owned()]);
            collect_sequence_capacity_proofs(
                &def.body.node,
                invariant,
                self.ctx.var_registry(),
                self.ctx.precomputed_constants(),
                op_defs,
                op_replacements,
                &proof_domains,
                &mut scope,
                &mut visiting,
                &mut proofs,
            );
        }
        proofs
    }

    fn configured_sequence_element_layout_proofs(
        &self,
    ) -> Vec<crate::state::SequenceElementLayoutProof> {
        let mut proofs = Vec::new();
        let proof_domains = self.named_homogeneous_proof_domains();
        let op_defs = &self.ctx.shared().ops;
        let op_replacements = self.ctx.op_replacements();
        for invariant in &self.config.invariants {
            let Some((_, def)) = proof_safe_zero_arg_op_def(invariant, op_defs, op_replacements)
            else {
                continue;
            };
            crate::state::collect_sequence_element_layout_proofs_with_ops(
                &def.body.node,
                invariant,
                self.ctx.var_registry(),
                self.ctx.precomputed_constants(),
                &proof_domains,
                op_defs,
                op_replacements,
                &mut proofs,
            );
        }
        proofs
    }

    fn configured_sequence_fixed_domain_type_proofs(
        &self,
    ) -> Vec<crate::state::SequenceFixedDomainTypeProof> {
        let mut proofs = Vec::new();
        let proof_domains = self.named_homogeneous_proof_domains();
        let op_defs = &self.ctx.shared().ops;
        let op_replacements = self.ctx.op_replacements();
        for invariant in &self.config.invariants {
            let Some((_, def)) = proof_safe_zero_arg_op_def(invariant, op_defs, op_replacements)
            else {
                continue;
            };
            crate::state::collect_sequence_fixed_domain_type_proofs_with_ops(
                &def.body.node,
                invariant,
                self.ctx.var_registry(),
                self.ctx.precomputed_constants(),
                &proof_domains,
                op_defs,
                op_replacements,
                &mut proofs,
            );
        }
        proofs
    }

    fn named_homogeneous_proof_domains(&self) -> BTreeMap<String, Arc<[crate::Value]>> {
        let ops = &self.ctx.shared().ops;
        let op_replacements = self.ctx.op_replacements();
        let mut domains: BTreeMap<String, Arc<[crate::Value]>> = ops
            .iter()
            .filter_map(|(name, def)| {
                if op_replacements.contains_key(name.as_str()) {
                    return None;
                }
                let def = def.as_ref();
                if !(def.params.is_empty()
                    && !def.contains_prime
                    && !def.has_primed_param
                    && !def.is_recursive)
                {
                    return None;
                }
                let values = expression_proof_domain_values(
                    &def.body.node,
                    ops,
                    self.ctx.precomputed_constants(),
                    op_replacements,
                    &mut BTreeSet::new(),
                )?;
                Some((name.clone(), Arc::from(values.into_boxed_slice())))
            })
            .collect();

        for from in op_replacements.keys() {
            if let Some(resolved) = resolve_proof_op_name(from, op_replacements) {
                if let Some(values) = domains.get(resolved).cloned() {
                    domains.insert(from.clone(), values);
                }
            }
        }
        domains
    }

    /// Shared setup for BFS model checking: constant binding, symmetry, VIEW validation,
    /// config validation, invariant compilation, operator expansion, and action compilation.
    /// Returns the resolved `Next` operator name on success.
    ///
    /// Both `check_impl` and `check_with_resume` call this to avoid duplicating setup logic.
    /// Part of #1230: extracted from check_impl/check_with_resume to eliminate copy-paste.
    #[allow(clippy::result_large_err)]
    pub(super) fn prepare_bfs_common(&mut self) -> Result<String, CheckResult> {
        // Install ENABLED hook (adaptive/parallel checkers install in their entry points).
        crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);

        // Bind constants from config before checking
        // Part of #2356/#2777: Route through check_error_to_result so
        // ExitRequested maps to LimitReached(Exit).
        if let Err(e) = bind_constants_from_config(&mut self.ctx, self.config) {
            return Err(check_error_to_result(
                EvalCheckError::Eval(e).into(),
                &self.stats,
            ));
        }

        // Pre-evaluate zero-arity constant-level operators (Part of #2364).
        // Mirrors TLC's SpecProcessor.processConstantDefns(): evaluate all zero-arg
        // operators that don't reference state variables ONCE, store the result in
        // SharedCtx for O(1) lookup during model checking. This eliminates per-reference
        // overhead (dep tracking, cache key hashing, context stripping) for constant ops
        // like RingOfNodes, Initiator, N in EWD998ChanID.
        super::precompute::precompute_constant_operators(&mut self.ctx);

        // Part of #2895: Promote env constants (CONSTANT declarations from model config)
        // to precomputed_constants for NameId-keyed O(1) lookup in eval_ident.
        // Constants in env are looked up via string-key HashMap::get; moving them to
        // precomputed_constants (NameId key) eliminates string hashing on the fast path.
        // Only promotes non-state-variable entries (state vars stay in state_env).
        super::precompute::promote_env_constants_to_precomputed(&mut self.ctx);
        // Part of #3961: Build ident resolution hints for eval_ident fast-path dispatch.
        super::precompute::build_ident_hints(&mut self.ctx);

        // Part of #4251 Stream 5: populate the TIR partial-evaluation
        // ConstantEnv from the authoritative precomputed_constants map now
        // that all CONSTANT bindings (from .cfg and --constant overrides)
        // have been resolved. The env is attached to every TirProgram built
        // during this run; partial-eval substitution runs at TIR preprocess
        // time only when `TLA2_PARTIAL_EVAL=1` / `--partial-eval` is set.
        if let Some(tir_parity) = self.tir_parity.as_mut() {
            let mut env = tla_tir::analysis::ConstantEnv::new();
            for (name_id, value) in self.ctx.precomputed_constants().iter() {
                env.bind(*name_id, value.clone());
            }
            tir_parity.set_partial_eval_env(env);
        }

        // Compute symmetry permutations now that constants are bound.
        // Two paths: explicit SYMMETRY config, or auto-detection from model value sets.
        if self.symmetry.perms.is_empty() && self.config.symmetry.is_some() {
            self.symmetry.perms =
                super::symmetry_perms::compute_symmetry_perms(&self.ctx, self.config)
                    .map_err(|e| check_error_to_result(e, &self.stats))?;
            // Extract group names from config for statistics.
            self.symmetry.group_names =
                super::symmetry_detect::detect_symmetric_model_value_sets(self.config)
                    .into_iter()
                    .map(|(name, _)| name)
                    .collect();
            self.symmetry.auto_detected = false;
            self.symmetry.mvperms = self // #358: MVPerm for O(1) model value lookup
                .symmetry
                .perms
                .iter()
                .map(crate::value::MVPerm::from_func_value)
                .collect::<Result<Vec<_>, _>>()
                // Part of #2356/#2777: Route through check_error_to_result so
                // ExitRequested maps to LimitReached(Exit).
                .map_err(|e| check_error_to_result(EvalCheckError::Eval(e).into(), &self.stats))?;
            self.refresh_liveness_mode();
        } else if self.symmetry.perms.is_empty() && self.config.symmetry.is_none() {
            // Auto-detect symmetry from model value sets (TLA2_AUTO_SYMMETRY=1).
            let (auto_perms, group_names) =
                super::symmetry_detect::auto_detect_symmetry_perms(&self.ctx, self.config);
            if !auto_perms.is_empty() {
                #[cfg(debug_assertions)]
                if tla2_debug() {
                    eprintln!(
                        "Auto-detected symmetry: {} permutations from {} group(s): {:?}",
                        auto_perms.len(),
                        group_names.len(),
                        group_names,
                    );
                }
                self.symmetry.perms = auto_perms;
                self.symmetry.group_names = group_names;
                self.symmetry.auto_detected = true;
                self.symmetry.mvperms = self
                    .symmetry
                    .perms
                    .iter()
                    .map(crate::value::MVPerm::from_func_value)
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| {
                        check_error_to_result(EvalCheckError::Eval(e).into(), &self.stats)
                    })?;
                self.refresh_liveness_mode();
            }
        }

        // Part of #2227: Only warn/reject for genuine temporal properties.
        // Pure safety properties (`[]P`) are handled by the safety-temporal fast
        // path and work correctly in notrace mode even with symmetry.
        // Check both explicit and auto-detected symmetry.
        let has_symmetry = !self.symmetry.perms.is_empty();
        let has_genuine_temporal = has_symmetry
            && !self.config.properties.is_empty()
            && crate::checker_ops::any_property_requires_liveness_checker(
                &self.ctx,
                &self.module.op_defs,
                &self.config.properties,
            );

        // Part of #1963: Warn when SYMMETRY and genuine liveness properties are both present.
        if has_genuine_temporal {
            eprintln!(
                "Warning: Declaring symmetry during liveness checking is dangerous. \
                 Please check liveness without symmetry defined."
            );
        }

        // Part of #2200/#3222: SYMMETRY + genuine temporal properties require
        // full-state storage for witness reconstruction because inline liveness
        // recording is disabled under symmetry. TLC warns but continues because
        // it always stores full states, so match TLC by auto-upgrading here.
        if has_genuine_temporal && !self.state_storage.store_full_states {
            self.set_store_states(true);
        }

        // Validate and cache VIEW operator name now that constants are bound
        if self.compiled.cached_view_name.is_none() && self.config.view.is_some() {
            self.validate_view();
        }

        // Validate next_name
        let raw_next_name = match &self.config.next {
            Some(name) => name.clone(),
            None => {
                return Err(CheckResult::from_error(
                    ConfigCheckError::MissingNext.into(),
                    self.stats.clone(),
                ));
            }
        };

        // Cache the raw config alias for trace reconstruction and user-facing labels,
        // but resolve replacements for the actual operator body we execute/compile.
        self.trace.cached_next_name = Some(raw_next_name.clone());
        let resolved = self.ctx.resolve_op_name(&raw_next_name).to_string();
        self.trace.cached_resolved_next_name = Some(resolved);

        // Part of #254: Set initial TLC level for TLCGet("level") - TLC uses 1-based indexing.
        // Set level=1 before any expression evaluation (including constraint extraction)
        // to avoid side effects (like PrintT) seeing level=0. Later phases update this
        // to the correct depth during BFS exploration.
        self.ctx.set_tlc_level(1);

        // Validate config operators: existence, arity, level, and variables.
        // Part of #2573: TLC validates all config elements at setup time
        // (SpecProcessor.java:processConfigInvariants/Properties/Constraints).
        self.validate_config_ops()?;

        let next_name = self.ctx.resolve_op_name(&raw_next_name).to_string();

        // Classify PROPERTY entries into BFS-phase checking buckets (#2332, #2670, #2740).
        let classification = crate::checker_ops::classify_property_safety_parts(
            &self.ctx,
            &self.config.properties,
            &self.module.op_defs,
        );
        self.compiled.promoted_property_invariants = classification.promoted_invariant_properties;
        self.compiled.state_property_violation_names = classification.state_violation_properties;
        self.compiled.eval_implied_actions = classification.eval_implied_actions;
        self.compiled.eval_state_invariants = classification.eval_state_invariants;
        self.compiled.promoted_implied_action_properties =
            classification.promoted_action_properties;
        self.compiled.property_init_predicates = classification.init_predicates;

        // Part of #1121: Shared alias-aware trace detection (invariants + constraints + action_constraints).
        self.compiled.uses_trace = compute_uses_trace(self.config, &self.module.op_defs)
            .map_err(|e| CheckResult::from_error(e, self.stats.clone()))?;

        // Pre-expand operator references in the Next action body (Part of #207).
        // Delegates to checker_ops::expand_operator_body (Part of #810).
        if let Some(next_def) = self.module.op_defs.get(&next_name).cloned() {
            let expanded_def = crate::checker_ops::expand_operator_body(&self.ctx, &next_def);
            self.module.op_defs.insert(next_name.clone(), expanded_def);
        }

        // Part of #3100: Discover split-action metadata for liveness provenance.
        // Successor generation no longer uses compiled split actions, but inline
        // liveness still needs the split action names/bindings to match action
        // predicates against BFS actions.
        if {
            static ACTION_SPLIT_ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *ACTION_SPLIT_ENABLED.get_or_init(|| std::env::var("TLA2_NO_ACTION_SPLIT").is_err())
        } {
            if let Some(next_def) = self.module.op_defs.get(&next_name) {
                match crate::action_instance::split_action_instances(&self.ctx, &next_def.body) {
                    Ok(instances) if !instances.is_empty() => {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!(
                                "[#3100] Action split: {} instances recorded for liveness provenance",
                                instances.len()
                            );
                        }
                        let meta: Vec<_> = instances
                            .iter()
                            .map(|inst| super::mc_struct::ActionInstanceMeta {
                                name: inst
                                    .name
                                    .clone()
                                    .or_else(|| (instances.len() == 1).then(|| next_name.clone())),
                                bindings: inst.bindings.clone(),
                                formal_bindings: inst.formal_bindings.clone(),
                                expr: Some(inst.expr.clone()),
                            })
                            .collect();
                        self.compiled.split_action_meta = Some(meta);
                    }
                    Ok(_) =>
                    {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!("[#1150] Action split produced no instances");
                        }
                    }
                    Err(_e) =>
                    {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!("[#1150] Action split failed, using monolithic: {_e:?}");
                        }
                    }
                }
            }
        }

        // TLC_LIVE_FORMULA_TAUTOLOGY pre-check (EC 2253, #2215).
        if let Some(result) = self.check_properties_for_tautologies() {
            return Err(result);
        }

        // Pre-analyze ACTION_CONSTRAINTs for variable dependencies.
        // This enables skipping constraint evaluation when referenced variables
        // are unchanged between current and successor states.
        if !self.config.action_constraints.is_empty() {
            self.compiled.action_constraint_analysis =
                Some(crate::checker_ops::ActionConstraintAnalysis::build(
                    &self.ctx,
                    &self.config.action_constraints,
                ));
        }

        // Detect PlusCal pc-dispatch pattern for action guard hoisting.
        // When all disjuncts of Next are guarded by `pc = "label"`, the BFS
        // loop can skip evaluating actions whose pc guard doesn't match the
        // current state, avoiding wasted work in PlusCal-generated specs.
        if let Some(next_def) = self.module.op_defs.get(&next_name) {
            let registry = self.ctx.var_registry().clone();
            if let Some(table) = crate::checker_ops::pc_dispatch::detect_pc_dispatch(
                next_def,
                &self.module.vars,
                &registry,
                &self.ctx,
            ) {
                #[cfg(debug_assertions)]
                if tla2_debug() {
                    eprintln!(
                        "[pc-dispatch] Detected PlusCal pattern: {} actions, {} distinct pc values",
                        table.total_actions,
                        table.dispatch.len(),
                    );
                }
                self.compiled.pc_var_idx = Some(table.pc_var_idx);
                self.compiled.pc_dispatch = Some(table);
            } else {
                // Part of #3805: Multi-process PlusCal guard hoisting.
                // When the full dispatch table can't be built (multi-process specs
                // use `pc[self] = "label"` instead of `pc = "label"`), we can still
                // enable guard hoisting by detecting the pc variable and verifying
                // the spec has pc guards. The enumerator handles multi-process pc
                // values (Value::Func) by looking up `self` in the binding chain.
                if let Some(pc_var_idx) = registry.get("pc") {
                    if crate::checker_ops::pc_dispatch::spec_has_pc_guards(next_def, &self.ctx) {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!(
                                "[pc-dispatch] Detected multi-process PlusCal pc guards (pc_var_idx={:?})",
                                pc_var_idx,
                            );
                        }
                        self.compiled.pc_var_idx = Some(pc_var_idx);
                    }
                }
            }
        }

        // Part of #3578: Compile invariant operators to bytecode for VM fast path.
        // NOTE: Profiling shows the bytecode VM is currently ~2.6x slower than
        // tree-walking with TIR cache for invariant evaluation (EWD998Small:
        // 27.1s bytecode vs 10.3s tree-walk). The per-state VM setup overhead
        // (BytecodeVm::from_state_env) exceeds the benefit of avoiding AST
        // traversal. Skip bytecode compilation when TIR eval owns invariants.
        //
        // Previously JIT forced bytecode compilation here, but the compiled
        // bytecode activates the slow bytecode VM path for ALL invariant evals.
        // Since JIT invariant native code currently has 0% hit rate (all
        // FallbackNeeded), this caused a 33% regression. JIT bytecode
        // compilation is now deferred to the JIT compilation phase.
        let tir_blocks_bytecode_vm = self
            .tir_parity
            .as_ref()
            .is_some_and(super::tir_parity::TirParityState::is_eval_mode);
        if tla_eval::tir::bytecode_vm_enabled() && !tir_blocks_bytecode_vm {
            self.compile_invariant_bytecode();
        }

        // Part of #3910: Compile action operators to bytecode for JIT next-state dispatch.
        // This is separate from invariant bytecode because actions use StoreVar opcodes
        // for primed variables, and the JitNextStateCache requires action-specific bytecode.
        // Also needed when LLVM2 is enabled (#4190), since the LLVM2 pipeline takes
        // BytecodeFunction as input.
        {
            let need_action_bytecode = crate::check::debug::jit_enabled();
            #[cfg(feature = "llvm2")]
            let need_action_bytecode =
                need_action_bytecode || super::llvm2_dispatch::should_use_llvm2();
            if need_action_bytecode {
                self.compile_action_bytecode();
            }
        }

        // Part of #3850: Initialize tiered JIT manager after action splitting
        // so we know the action count. The tier manager tracks per-action
        // compilation tiers and makes promotion decisions based on evaluation
        // frequency.
        if crate::check::debug::jit_enabled() {
            self.initialize_tier_manager();
        }

        // Part of #4118: Initialize LLVM2 native compilation cache.
        // Must be called after compile_action_bytecode() so bytecode is available.
        // Only activates when TLA2_LLVM2=1 and llc is on PATH.
        self.initialize_llvm2_cache();

        Ok(next_name)
    }

    /// Compile invariant operators to bytecode for VM-accelerated evaluation.
    ///
    /// Part of #3578: Attempts bytecode compilation for all configured invariant
    /// names. The result is stored in `self.bytecode` and consulted during
    /// `check_invariants_array` to bypass tree-walking evaluation.
    fn compile_invariant_bytecode(&mut self) {
        if self.config.invariants.is_empty() {
            return;
        }

        // Get module references from tir_parity if available, otherwise use
        // the root module from the context.
        let (mut root, mut deps) = if let Some(tir) = &self.tir_parity {
            let (root, deps) = tir.clone_modules();
            (root, deps)
        } else {
            return;
        };

        // The cloned module's operator bodies contain Expr::Ident for state
        // variables (state var resolution in checker_setup.rs only applies to
        // the op_defs HashMap, not the module AST). The TIR lowerer needs
        // Expr::StateVar nodes to emit LoadVar opcodes; without this, variable
        // references lower to TirNameKind::Ident and the bytecode compiler
        // emits LoadConst with a string name instead of LoadVar with a
        // VarRegistry index — causing the VM to evaluate against wrong values.
        use tla_core::ast::Unit;
        let registry = self.ctx.var_registry().clone();
        for unit in &mut root.units {
            if let Unit::Operator(def) = &mut unit.node {
                tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
            }
        }
        // Also resolve state vars in dependency modules — invariants defined
        // in EXTENDS'd base specs reference the same state variables.
        for dep in &mut deps {
            for unit in &mut dep.units {
                if let Unit::Operator(def) = &mut unit.node {
                    tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
                }
            }
        }

        // Diagnostic: show what modules and operators are available for compilation.
        if super::debug::bytecode_vm_stats_enabled() {
            let root_ops: Vec<_> = root
                .units
                .iter()
                .filter_map(|u| {
                    if let Unit::Operator(def) = &u.node {
                        Some(def.name.node.as_str())
                    } else {
                        None
                    }
                })
                .collect();
            eprintln!(
                "[bytecode] root module '{}': {} operators: {:?}",
                root.name.node,
                root_ops.len(),
                &root_ops[..root_ops.len().min(10)]
            );
            for (i, dep) in deps.iter().enumerate() {
                let dep_ops: Vec<_> = dep
                    .units
                    .iter()
                    .filter_map(|u| {
                        if let Unit::Operator(def) = &u.node {
                            Some(def.name.node.as_str())
                        } else {
                            None
                        }
                    })
                    .collect();
                eprintln!(
                    "[bytecode] dep[{i}] module '{}': {} operators: {:?}",
                    dep.name.node,
                    dep_ops.len(),
                    &dep_ops[..dep_ops.len().min(10)]
                );
            }
        }

        let dep_refs: Vec<&Module> = deps.iter().collect();
        let tir_callees =
            tla_eval::bytecode_vm::collect_bytecode_namespace_callees(&root, &dep_refs);
        let compiled = tla_eval::bytecode_vm::compile_operators_to_bytecode_full(
            &root,
            &dep_refs,
            &self.config.invariants,
            self.ctx.precomputed_constants(),
            Some(self.ctx.op_replacements()),
            Some(&tir_callees),
        );

        // Keep the rollout measurements behind the stats flag, but allow
        // release-mode reason logging via TLA2_DEBUG_BYTECODE_VM=1.
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        let reason_logs_enabled = stats_enabled || debug_bytecode_vm();
        if stats_enabled {
            eprintln!(
                "[bytecode] compiled {}/{} invariants ({} failed)",
                compiled.op_indices.len(),
                self.config.invariants.len(),
                compiled.failed.len(),
            );
        }
        if reason_logs_enabled {
            for (name, err) in &compiled.failed {
                eprintln!("[bytecode]   skip {name}: {err}");
            }
        }
        #[cfg(debug_assertions)]
        if super::debug::tla2_debug() {
            eprintln!(
                "[#3578] Bytecode VM: compiled {}/{} invariants ({} failed)",
                compiled.op_indices.len(),
                self.config.invariants.len(),
                compiled.failed.len(),
            );
            for (name, err) in &compiled.failed {
                eprintln!("[#3578]   skip {name}: {err}");
            }
        }
        if !compiled.op_indices.is_empty() {
            // Part of #3582: JIT-compile eligible bytecode invariants to native code.
            if crate::check::debug::jit_enabled() {
                match JitInvariantCacheImpl::build(&compiled.chunk, &compiled.op_indices) {
                    Ok(cache) => {
                        let jit_count = cache.len();
                        if jit_count > 0 {
                            if stats_enabled {
                                eprintln!(
                                    "[jit] compiled {}/{} bytecode invariants to native code",
                                    jit_count,
                                    compiled.op_indices.len(),
                                );
                            }
                            let all = cache.covers_all(&self.config.invariants);
                            self.jit_all_compiled = all;
                            self.jit_resolved_fns = if all {
                                cache.resolve_ordered(&self.config.invariants)
                            } else {
                                None
                            };
                            self.jit_cache = Some(cache);
                        }
                    }
                    Err(e) => {
                        if reason_logs_enabled {
                            eprintln!("[jit] JIT compilation failed: {e}");
                        }
                    }
                }
            }

            self.bytecode = Some(compiled);
        }
    }

    /// Compile action operators to bytecode for JIT next-state dispatch.
    ///
    /// Part of #3910: The JitNextStateCache needs bytecode for split-action operators
    /// (like "Send", "Receive"), not invariant operators. This method compiles the
    /// action operators discovered by split_action_instances into bytecode that the
    /// Cranelift JIT can lower to native code.
    ///
    /// No-op when:
    /// - No split_action_meta (monolithic single-action specs)
    /// - tir_parity modules unavailable (no AST to compile from)
    fn compile_action_bytecode(&mut self) {
        if self
            .compiled
            .split_action_meta
            .as_ref()
            .map_or(true, |m| m.is_empty())
        {
            return;
        }

        // Collect unique action operator names from BOTH sources:
        // 1. split_action_meta (leaf actions: "RecvMsg", "PassToken", etc.)
        // 2. coverage.actions (detected actions: "System", "Environment", etc.)
        //
        // We need both because the JIT dispatch uses detected action names
        // (from run_gen.rs per-action loop) while deeper split actions may
        // also be referenced. Having both ensures cache hits regardless of
        // which naming level the dispatch uses.
        //
        // Part of: JIT name mismatch fix — detected vs split action names.
        let mut name_set = std::collections::HashSet::new();
        if let Some(meta) = self.compiled.split_action_meta.as_ref() {
            for m in meta {
                if let Some(name) = &m.name {
                    name_set.insert(name.clone());
                }
            }
        }
        for action in &self.coverage.actions {
            name_set.insert(action.name.clone());
        }
        let action_names: Vec<String> = name_set.into_iter().collect();
        if action_names.is_empty() {
            return;
        }

        // Get module references (same source as invariant bytecode compilation).
        let (mut root, mut deps) = if let Some(tir) = &self.tir_parity {
            let (root, deps) = tir.clone_modules();
            (root, deps)
        } else {
            return;
        };

        // Resolve state vars in the AST (required for LoadVar/StoreVar opcodes).
        use tla_core::ast::Unit;
        let registry = self.ctx.var_registry().clone();
        for unit in &mut root.units {
            if let Unit::Operator(def) = &mut unit.node {
                tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
            }
        }
        for dep in &mut deps {
            for unit in &mut dep.units {
                if let Unit::Operator(def) = &mut unit.node {
                    tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
                }
            }
        }

        let dep_refs: Vec<&tla_core::ast::Module> = deps.iter().collect();
        let tir_callees =
            tla_eval::bytecode_vm::collect_bytecode_namespace_callees(&root, &dep_refs);
        let compiled = tla_eval::bytecode_vm::compile_operators_to_bytecode_full(
            &root,
            &dep_refs,
            &action_names,
            self.ctx.precomputed_constants(),
            Some(self.ctx.op_replacements()),
            Some(&tir_callees),
        );

        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        let reason_logs = stats_enabled || super::debug::debug_bytecode_vm();
        if reason_logs {
            eprintln!(
                "[bytecode] action compilation: {}/{} actions compiled ({} failed)",
                compiled.op_indices.len(),
                action_names.len(),
                compiled.failed.len(),
            );
            for (name, err) in &compiled.failed {
                eprintln!("[bytecode]   action skip {name}: {err}");
            }
        }

        if compiled.op_indices.is_empty() {
            return;
        }

        // Part of #3910: Transform action predicate bytecode into next-state
        // function bytecode. Rewrites `LoadPrime(x) + Eq` → `StoreVar(x, expr)`
        // so the JIT next-state cache can produce successor states.
        let mut transformed_count = 0usize;
        let mut transformed = compiled;
        let action_entries: Vec<(String, u16)> = transformed
            .op_indices
            .iter()
            .map(|(name, &func_idx)| (name.clone(), func_idx))
            .collect();
        let action_entry_count = action_entries.len();
        transformed.op_indices.clear();
        for (name, func_idx) in action_entries {
            let Some(original_instructions) = transformed
                .chunk
                .functions
                .get(func_idx as usize)
                .map(|func| func.instructions.clone())
            else {
                continue;
            };

            match tla_tir::bytecode::action_transform::transform_action_to_next_state(
                &original_instructions,
            ) {
                tla_tir::bytecode::action_transform::ActionTransformOutcome::Transformed(
                    new_instructions,
                ) => match super::validate_next_state_action_chunk(
                    func_idx,
                    &new_instructions,
                    &transformed.chunk,
                    self.module.vars.len(),
                ) {
                    Ok(()) => {
                        if let Some(func) = transformed.chunk.functions.get_mut(func_idx as usize) {
                            func.instructions = new_instructions;
                        }
                        transformed.op_indices.insert(name.clone(), func_idx);
                        transformed_count += 1;
                        if reason_logs {
                            eprintln!("[bytecode]   action '{name}': transformed to next-state");
                        }
                    }
                    Err(reason) => {
                        transformed.failed.push((
                            name.clone(),
                            tla_tir::bytecode::CompileError::Unsupported(format!(
                                "unsafe next-state transform: {reason}"
                            )),
                        ));
                        if reason_logs {
                            eprintln!("[bytecode]   action '{name}': skipped ({reason})");
                        }
                    }
                },
                tla_tir::bytecode::action_transform::ActionTransformOutcome::NoRewrite => {
                    transformed.failed.push((
                        name.clone(),
                        tla_tir::bytecode::CompileError::Unsupported(
                            "no safe next-state rewrite found".to_string(),
                        ),
                    ));
                    if reason_logs {
                        eprintln!(
                            "[bytecode]   action '{name}': skipped (no prime assignment pattern found)"
                        );
                    }
                }
                tla_tir::bytecode::action_transform::ActionTransformOutcome::Unsafe(reason) => {
                    transformed.failed.push((
                        name.clone(),
                        tla_tir::bytecode::CompileError::Unsupported(format!(
                            "unsafe next-state transform: {reason}"
                        )),
                    ));
                    if reason_logs {
                        eprintln!("[bytecode]   action '{name}': skipped ({reason})");
                    }
                }
            }
        }
        if reason_logs {
            eprintln!(
                "[bytecode] action transform: {transformed_count}/{} actions → next-state",
                action_entry_count,
            );
        }
        if !transformed.op_indices.is_empty() {
            self.action_bytecode = Some(transformed);
        }
    }

    /// Infer and store a `StateLayout` for flat i64 state representation.
    ///
    /// Called after init state solving when we have a concrete initial state
    /// to infer variable types from. The inferred layout maps each state
    /// variable to a contiguous region of i64 slots, enabling `FlatState`
    /// conversions for JIT-compiled transition functions and invariant checks.
    ///
    /// No-op when no initial states are available.
    ///
    /// Part of #3986: Wire FlatState into BFS path.
    pub(in crate::check) fn infer_flat_state_layout(
        &mut self,
        first_init_state: &crate::state::ArrayState,
    ) {
        let registry = self.ctx.var_registry().clone();
        let sequence_proofs = self.configured_sequence_capacity_proofs();
        let sequence_element_proofs = self.configured_sequence_element_layout_proofs();
        let sequence_fixed_domain_type_proofs = self.configured_sequence_fixed_domain_type_proofs();
        let layout = crate::state::infer_layout_with_sequence_layout_proofs(
            first_init_state,
            &registry,
            &sequence_proofs,
            &sequence_element_proofs,
            &sequence_fixed_domain_type_proofs,
        );

        let flat_bytes = crate::state::flat_state_bytes(&layout);
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        if stats_enabled {
            eprintln!(
                "[flat_state] inferred layout: {} vars, {} total slots, {} bytes/state, \
                 all_scalar={}, trivial={}, fully_flat={}, has_dynamic={}",
                layout.var_count(),
                layout.total_slots(),
                flat_bytes,
                layout.is_all_scalar(),
                layout.is_trivial(),
                layout.is_fully_flat(),
                layout.has_dynamic_vars(),
            );
        }

        let layout_arc = std::sync::Arc::new(layout);
        // Part of #3986: Create the FlatBfsBridge alongside the layout.
        let bridge = crate::state::FlatBfsBridge::new(std::sync::Arc::clone(&layout_arc));

        if stats_enabled {
            eprintln!(
                "[flat_state] bridge: fully_flat={}, num_slots={}, bytes_per_state={}",
                bridge.is_fully_flat(),
                bridge.num_slots(),
                bridge.bytes_per_state(),
            );
        }

        self.flat_state_layout = Some(layout_arc);
        // Part of #4126: Create adapter for Tier 0 interpreter sandwich.
        // Verify the first initial state roundtrips correctly through the flat
        // representation. This catches specs with string/model-value variables
        // that layout inference classifies as Scalar but the i64 roundtrip
        // would corrupt (e.g., "black" → 0 → SmallInt(0)).
        let mut adapter = crate::state::FlatBfsAdapter::new(bridge.clone());
        let mut verify_state = first_init_state.clone();
        let roundtrip_ok = adapter.verify_roundtrip(&mut verify_state, &registry);
        // Log roundtrip result: always log on failure (auto-detect may have
        // wanted to activate), or when stats are enabled. Include a diagnostic
        // summary on failure so the FAIL message is actionable (issue #4275).
        if stats_enabled || !roundtrip_ok {
            if roundtrip_ok {
                eprintln!("[flat_state] adapter roundtrip verification: PASS");
            } else {
                let detail = adapter
                    .diagnose_roundtrip(first_init_state, &registry)
                    .unwrap_or_else(|| "no detail available".to_string());
                eprintln!(
                    "[flat_state] adapter roundtrip verification: FAIL ({detail}) — flat BFS will fall back to Owned entries",
                );
            }
        }
        self.flat_bfs_adapter = Some(adapter);
        self.flat_bfs_bridge = Some(bridge);

        // Part of #3986/#4356: Detect if flat i64 state can be the primary
        // BFS representation.
        //
        // Conditions: fully-flat fixed layout, roundtrip verified, no VIEW,
        // no SYMMETRY, flat BFS enabled, and no full-state storage. Fully-flat
        // includes scalar vars plus fixed-size records/arrays whose complete
        // value is represented in the flat slot buffer; Dynamic layouts stay
        // on the adapter/interpreter-sandwich path.
        //
        // Part of #4298: Gate activation on `store_full_states == false`. Same
        // rationale as the #4281 fix for `jit_compiled_fp_active`: in full-state
        // mode the `seen` HashMap and `seen_fps` set are already populated with
        // FP64 fingerprints by `init_states_full_state()` before layout inference
        // runs here. If we now flip to flat-primary, successors would be
        // fingerprinted via `FlatState::fingerprint_compiled()` (xxh3 on raw i64
        // buffer) while init states remain under FP64 — the same state value
        // (e.g., stuttering `x=0`) gets two different fingerprints, inflating
        // the distinct-state count and breaking parity with TLC (e.g.,
        // `system_loop_no_fair_2w`).
        {
            let fully_flat = self
                .flat_state_layout
                .as_ref()
                .is_some_and(|l| l.is_fully_flat());
            let flat_primary_safe = self
                .flat_state_layout
                .as_ref()
                .is_some_and(|l| l.supports_flat_primary());
            self.flat_state_primary = roundtrip_ok
                && flat_primary_safe
                && self.compiled.cached_view_name.is_none()
                && self.symmetry.perms.is_empty()
                && self.should_use_flat_bfs()
                && !self.state_storage.store_full_states;
            eprintln!(
                "[flat_state] flat_state_primary={}: roundtrip_ok={}, fully_flat={}, flat_primary_safe={}, view={}, symmetry={}, flat_bfs={}, full_state_storage={}",
                self.flat_state_primary,
                roundtrip_ok,
                fully_flat,
                flat_primary_safe,
                self.compiled.cached_view_name.is_some(),
                !self.symmetry.perms.is_empty(),
                self.should_use_flat_bfs(),
                self.state_storage.store_full_states,
            );
            if stats_enabled && self.flat_state_primary {
                eprintln!(
                    "[flat_state] flat_state_primary=true: fully-flat fixed layout, \
                     no VIEW, no SYMMETRY — flat i64 is primary BFS representation",
                );
            }
        }
        self.invalidate_compiled_bfs_after_flat_primary_promotion();
    }

    /// Infer and store a `StateLayout` from a wavefront of initial states.
    ///
    /// Like `infer_flat_state_layout` but examines multiple states for
    /// robustness. If variable shapes disagree across states, the
    /// conflicting variable falls back to `Dynamic`.
    ///
    /// Part of #3986: Layout inference from first wavefront (~1000 states).
    pub(in crate::check) fn infer_flat_state_layout_from_wavefront(
        &mut self,
        states: &[crate::state::ArrayState],
    ) {
        if states.is_empty() {
            return;
        }

        let registry = self.ctx.var_registry().clone();
        let sequence_proofs = self.configured_sequence_capacity_proofs();
        let sequence_element_proofs = self.configured_sequence_element_layout_proofs();
        let sequence_fixed_domain_type_proofs = self.configured_sequence_fixed_domain_type_proofs();
        let layout = crate::state::infer_layout_from_wavefront_with_sequence_layout_proofs(
            states,
            &registry,
            &sequence_proofs,
            &sequence_element_proofs,
            &sequence_fixed_domain_type_proofs,
        );

        let flat_bytes = crate::state::flat_state_bytes(&layout);
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        if stats_enabled {
            eprintln!(
                "[flat_state] wavefront layout ({} states): {} vars, {} total slots, {} bytes/state, \
                 all_scalar={}, trivial={}, fully_flat={}, has_dynamic={}",
                states.len(),
                layout.var_count(),
                layout.total_slots(),
                flat_bytes,
                layout.is_all_scalar(),
                layout.is_trivial(),
                layout.is_fully_flat(),
                layout.has_dynamic_vars(),
            );
        }

        let layout_arc = std::sync::Arc::new(layout);
        let bridge = crate::state::FlatBfsBridge::new(std::sync::Arc::clone(&layout_arc));

        if stats_enabled {
            eprintln!(
                "[flat_state] wavefront bridge: fully_flat={}, num_slots={}, bytes_per_state={}",
                bridge.is_fully_flat(),
                bridge.num_slots(),
                bridge.bytes_per_state(),
            );
        }

        self.flat_state_layout = Some(layout_arc.clone());
        // Part of #4126: Create adapter for Tier 0 interpreter sandwich.
        let mut adapter = crate::state::FlatBfsAdapter::new(bridge.clone());
        let mut verify_state = states[0].clone();
        let roundtrip_ok = adapter.verify_roundtrip(&mut verify_state, &registry);
        if stats_enabled || !roundtrip_ok {
            if roundtrip_ok {
                eprintln!("[flat_state] wavefront adapter roundtrip verification: PASS");
            } else {
                let detail = adapter
                    .diagnose_roundtrip(&states[0], &registry)
                    .unwrap_or_else(|| "no detail available".to_string());
                eprintln!(
                    "[flat_state] wavefront adapter roundtrip verification: FAIL ({detail}) — flat BFS will fall back to Owned entries",
                );
            }
        }
        self.flat_bfs_adapter = Some(adapter);
        self.flat_bfs_bridge = Some(bridge);

        // Part of #3986/#4356: Detect if flat i64 state can be the primary
        // BFS representation. See the single-state setter above for the
        // full domain and full-state-storage rationale.
        // Part of #4298: Gate on `!store_full_states` — see the single-state
        // `infer_flat_state_layout` setter above for the full rationale. Flipping
        // the fingerprint algorithm after init states are already stored in the
        // `seen`/`seen_fps` domain inflates distinct-state counts (same state
        // value ends up with both an FP64 init fingerprint and an xxh3 successor
        // fingerprint).
        {
            let flat_primary_safe = layout_arc.supports_flat_primary();
            self.flat_state_primary = roundtrip_ok
                && flat_primary_safe
                && self.compiled.cached_view_name.is_none()
                && self.symmetry.perms.is_empty()
                && self.should_use_flat_bfs()
                && !self.state_storage.store_full_states;
            eprintln!(
                "[flat_state] flat_state_primary={}: roundtrip_ok={}, fully_flat={}, flat_primary_safe={}, view={}, symmetry={}, flat_bfs={}, full_state_storage={}",
                self.flat_state_primary,
                roundtrip_ok,
                layout_arc.is_fully_flat(),
                flat_primary_safe,
                self.compiled.cached_view_name.is_some(),
                !self.symmetry.perms.is_empty(),
                self.should_use_flat_bfs(),
                self.state_storage.store_full_states,
            );
            if stats_enabled && self.flat_state_primary {
                eprintln!(
                    "[flat_state] flat_state_primary=true (wavefront): fully-flat fixed layout, \
                     no VIEW, no SYMMETRY — flat i64 is primary BFS representation",
                );
            }
        }
        self.invalidate_compiled_bfs_after_flat_primary_promotion();
    }

    fn invalidate_compiled_bfs_after_flat_primary_promotion(&mut self) {
        if !self.flat_state_primary {
            return;
        }
        let promoted_non_scalar_layout = self
            .flat_state_layout
            .as_ref()
            .is_some_and(|layout| !layout.is_all_scalar());
        if !promoted_non_scalar_layout {
            return;
        }
        let flat_slots = self
            .flat_bfs_adapter
            .as_ref()
            .filter(|adapter| adapter.is_fully_flat())
            .map(|adapter| adapter.num_slots())
            .or_else(|| {
                self.flat_state_layout
                    .as_ref()
                    .map(|layout| layout.total_slots())
            });
        self.clear_layout_sensitive_compiled_bfs_artifacts(
            "flat_state_primary layout promotion",
            flat_slots,
        );
    }

    fn clear_layout_sensitive_compiled_bfs_artifacts(
        &mut self,
        reason: &str,
        flat_slots: Option<usize>,
    ) {
        let had_step = self.compiled_bfs_step.is_some();
        let had_level = self.compiled_bfs_level.is_some();
        #[cfg(feature = "llvm2")]
        let had_llvm2 = self.llvm2_cache.is_some() || self.llvm2_build_stats.is_some();
        #[cfg(not(feature = "llvm2"))]
        let had_llvm2 = false;

        if !had_step && !had_level && !had_llvm2 {
            return;
        }

        let width_detail = flat_slots
            .map(|slots| {
                format!(
                    ", flat_slots={slots}, logical_vars={}",
                    self.module.vars.len()
                )
            })
            .unwrap_or_default();

        #[cfg(feature = "llvm2")]
        eprintln!(
            "[compiled-bfs] clearing layout-sensitive compiled artifacts before rebuild: \
             reason={reason}{width_detail}, compiled_bfs_step={had_step}, \
             compiled_bfs_level={had_level}, llvm2_cache={}, llvm2_build_stats={}",
            self.llvm2_cache.is_some(),
            self.llvm2_build_stats.is_some(),
        );
        #[cfg(not(feature = "llvm2"))]
        eprintln!(
            "[compiled-bfs] clearing layout-sensitive compiled artifacts before rebuild: \
             reason={reason}{width_detail}, compiled_bfs_step={had_step}, \
             compiled_bfs_level={had_level}",
        );

        self.compiled_bfs_step = None;
        self.compiled_bfs_level = None;
        #[cfg(feature = "llvm2")]
        {
            self.llvm2_cache = None;
            self.llvm2_build_stats = None;
        }
    }

    /// Get the flat state layout, if inferred.
    ///
    /// Returns `None` before `infer_flat_state_layout` has been called.
    ///
    /// Part of #3986: Wire FlatState into BFS path.
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn flat_state_layout(
        &self,
    ) -> Option<&std::sync::Arc<crate::state::StateLayout>> {
        self.flat_state_layout.as_ref()
    }

    /// Get the FlatBfsBridge, if created.
    ///
    /// Returns `None` before `infer_flat_state_layout` has been called.
    /// The bridge provides cheap `ArrayState <-> FlatState` conversions
    /// and fingerprint bridging at the BFS boundary.
    ///
    /// Part of #3986: Wire FlatState into BFS engine.
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn flat_bfs_bridge(&self) -> Option<&crate::state::FlatBfsBridge> {
        self.flat_bfs_bridge.as_ref()
    }

    /// Get a clone of the FlatBfsAdapter, if created.
    ///
    /// Returns `None` before `infer_flat_state_layout` has been called.
    /// The adapter wraps the bridge with BFS-specific convenience methods
    /// for the interpreter sandwich (FlatState -> ArrayState -> eval ->
    /// ArrayState -> FlatState).
    ///
    /// Returns a clone because adapters are per-worker (mutable stats).
    ///
    /// Part of #4126: FlatState as native BFS representation (Phase E).
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn flat_bfs_adapter(&self) -> Option<crate::state::FlatBfsAdapter> {
        self.flat_bfs_adapter.clone()
    }

    /// Determine whether flat BFS should be used for this run.
    ///
    /// The decision hierarchy is:
    /// 1. `Config::use_flat_state = Some(false)` → disabled (programmatic override)
    /// 2. `TLA2_NO_FLAT_BFS=1` → disabled (env var override)
    /// 3. `Config::use_flat_state = Some(true)` → enabled if adapter ready
    /// 4. `TLA2_FLAT_BFS=1` → enabled if adapter ready (force-enable env var)
    /// 5. Auto-detect: enabled when adapter is present, roundtrip verified,
    ///    AND the layout is fully flat (all vars are scalar/IntArray/Record —
    ///    no Dynamic vars requiring ArrayState fallback).
    ///
    /// The auto-detect path (5) is the default for specs where all state
    /// variables are i64-representable (Int, Bool, ModelValue). This removes
    /// the need for `TLA2_FLAT_BFS=1` on typical scalar specs.
    ///
    /// Part of #4126: Auto-detect flat BFS for scalar specs.
    #[must_use]
    pub(in crate::check) fn should_use_flat_bfs(&self) -> bool {
        // 1. Programmatic force-disable
        if self.config.use_flat_state == Some(false) {
            return false;
        }
        // 2. Env var force-disable
        if crate::check::debug::flat_bfs_disabled() {
            return false;
        }

        let adapter_ready = self
            .flat_bfs_adapter
            .as_ref()
            .is_some_and(|a| a.roundtrip_verified());

        // 3. Programmatic force-enable
        if self.config.use_flat_state == Some(true) {
            return adapter_ready;
        }
        // 4. Env var force-enable
        if crate::check::debug::flat_bfs_enabled() {
            return adapter_ready;
        }

        // 5. Auto-detect: enable when fully flat and roundtrip verified
        if !adapter_ready {
            return false;
        }
        self.flat_bfs_adapter
            .as_ref()
            .is_some_and(|a| a.is_fully_flat())
    }

    /// Whether flat i64 state is the primary BFS representation for this run.
    ///
    /// True when ALL of:
    /// - The inferred layout is fully flat — `layout.is_fully_flat()`
    /// - Roundtrip verification passed
    /// - No VIEW expression configured
    /// - No SYMMETRY reduction active
    /// - Flat BFS is enabled
    /// - Full-state storage is disabled
    ///
    /// When true, the fingerprint-only BFS hot path can store states as
    /// contiguous `[i64]` buffers and use the flat compiled fingerprint
    /// domain. Scalar layouts remain the simple case; fixed-size records and
    /// arrays are also eligible when their slots are a complete state
    /// representation. Dynamic layouts are not eligible.
    ///
    /// Part of #3986: Flat i64 state as primary BFS representation.
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn is_flat_state_primary(&self) -> bool {
        self.flat_state_primary
    }

    /// Upgrade the JIT invariant cache with compound layout information.
    ///
    /// Called after init state solving when layout information is available.
    /// If the check-side flat layout is fully fixed, that authoritative layout
    /// is converted for JIT/LLVM2 use; otherwise this falls back to inferring
    /// from the concrete initial state. The initial `JitInvariantCache::build()`
    /// has no layout info, so compound-type variable accesses (records,
    /// functions, tuples) fall back to the interpreter. Rebuilding with
    /// `build_with_layout()` enables native compound access in JIT-compiled
    /// invariants.
    ///
    /// No-op when:
    /// - JIT feature is disabled
    /// - No JIT cache exists (no invariants were JIT-compiled)
    /// - No bytecode exists (no invariants were bytecode-compiled)
    /// - The initial state has no compound variables (layout upgrade is unnecessary)
    ///
    /// Part of #3910: JIT invariant layout upgrade for native compound access.
    pub(in crate::check) fn upgrade_jit_cache_with_layout(
        &mut self,
        first_init_state: &crate::state::ArrayState,
    ) {
        // Derive layout for BOTH invariant JIT and next-state JIT, so compute
        // it even when jit_cache (invariant) is None.
        let compact_values = first_init_state.values();
        let has_compound = compact_values
            .iter()
            .any(|cv| !cv.is_int() && !cv.is_bool());
        if !has_compound {
            // All variables are scalar — layout offers no benefit.
            return;
        }

        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        let state_layout = if let Some(flat_layout) = self
            .flat_state_layout
            .as_deref()
            .filter(|layout| layout.is_fully_flat())
        {
            let state_layout = crate::state::check_layout_to_jit_layout(flat_layout);
            if stats_enabled {
                eprintln!(
                    "[jit] using authoritative flat layout for JIT: {} vars, {} compact slots",
                    state_layout.var_count(),
                    crate::state::layout_bridge::jit_layout_compact_slot_count(&state_layout),
                );
            }
            state_layout
        } else {
            let var_layouts: Vec<tla_jit_abi::VarLayout> = compact_values
                .iter()
                .map(|cv| {
                    let value = tla_value::Value::from(cv);
                    tla_jit_runtime::infer_var_layout(&value)
                })
                .collect();
            tla_jit_abi::StateLayout::new(var_layouts)
        };

        // Store layout for next-state JIT compilation (Part of #3958).
        self.jit_state_layout = Some(state_layout.clone());

        #[cfg(feature = "llvm2")]
        {
            // LLVM2 action compilation currently runs during prepare(), before
            // the first init states exist. Compound specs only acquire
            // record/function layout information here, so the earlier
            // layout-blind build falls back to generic aggregate lowering.
            // Rebuild the LLVM2 cache once layout is known so action lowering
            // can take the fixed-layout fast paths.
            if super::llvm2_dispatch::should_use_llvm2() && self.action_bytecode.is_some() {
                let flat_slots = self
                    .flat_bfs_adapter
                    .as_ref()
                    .filter(|adapter| adapter.is_fully_flat())
                    .map(|adapter| adapter.num_slots());
                self.clear_layout_sensitive_compiled_bfs_artifacts(
                    "rebuild LLVM2 cache with promoted flat layout",
                    flat_slots,
                );
                self.initialize_llvm2_cache();
            }
        }

        // Upgrade the invariant JIT cache if it exists.
        let Some(ref bytecode) = self.bytecode else {
            return;
        };
        if self.jit_cache.is_none() {
            return;
        }

        match JitInvariantCacheImpl::build_with_layout(
            &bytecode.chunk,
            &bytecode.op_indices,
            &state_layout,
        ) {
            Ok(cache) => {
                let jit_count = cache.len();
                if jit_count > 0 {
                    if stats_enabled {
                        eprintln!(
                            "[jit] upgraded {jit_count} invariants with compound layout info",
                        );
                    }
                    let all = cache.covers_all(&self.config.invariants);
                    self.jit_all_compiled = all;
                    self.jit_resolved_fns = if all {
                        cache.resolve_ordered(&self.config.invariants)
                    } else {
                        None
                    };
                    self.jit_cache = Some(cache);
                }
            }
            Err(e) => {
                if stats_enabled {
                    eprintln!("[jit] layout upgrade failed (keeping basic cache): {e}");
                }
            }
        }
    }

    /// Attempt to activate compiled xxh3 fingerprinting for the BFS run.
    ///
    /// Checks all prerequisites:
    /// 1. All init state variables are scalar (Int/Bool) — compound values
    ///    cannot be represented as a single i64 for xxh3 hashing.
    /// 2. No VIEW expression configured — VIEW fingerprinting uses its own
    ///    custom computation path.
    /// 3. No SYMMETRY reduction — symmetry canonical fingerprinting is
    ///    incompatible with xxh3 raw-buffer hashing.
    /// 4. JIT state layout is available (needed for variable count).
    ///
    /// When all conditions are met, sets `jit_compiled_fp_active = true`.
    /// This flag MUST be set before any init states are fingerprinted.
    ///
    /// Part of #3987: Compiled xxh3 fingerprinting for the BFS hot path.
    pub(in crate::check) fn try_activate_compiled_fingerprinting(&mut self) {
        // Part of #4215: Structural guarantee that fingerprint algorithm cannot change
        // after BFS processing has started. If this fires, it means a code path is
        // attempting to switch fingerprint algorithms mid-run, which would cause
        // domain separation violations in the seen set.
        #[cfg(debug_assertions)]
        debug_assert!(
            !self.fp_algorithm_sealed,
            "BUG: try_activate_compiled_fingerprinting called after BFS loop started \
             (fingerprint algorithm sealed). This would mix xxh3 and FP64 fingerprints \
             in the same seen set, causing silent state loss. Part of #4215."
        );

        self.try_activate_compiled_fingerprinting_inner();

        // Part of #4319 Phase 0: fingerprint mixed-mode guard.
        //
        // Once activation decisions have been made, assert the invariant that
        // every fingerprint seen by the BFS comes from a single hash domain.
        //
        // When any LLVM2-compiled action is present, the BFS can emit two
        // classes of successors in the same run:
        //   (a) compiled successors produced by `try_llvm2_action`
        //       (unflattened from an i64 buffer), and
        //   (b) interpreter successors produced by the fallback path.
        // Both classes ultimately flow through `array_state_fingerprint`,
        // which either (i) routes everything through
        // `fingerprint_flat_compiled` when `jit_compiled_fp_active` is true
        // (xxh3 + FLAT_COMPILED_DOMAIN_SEED — single domain), or
        // (ii) routes everything through FP64/FNV when
        // `jit_compiled_fp_active` is false (single FP64 domain). Either
        // configuration is sound *as long as the flag is consistent for the
        // whole run* — which `fp_algorithm_sealed` enforces at the BFS
        // entry and the runtime assertion in `state_fingerprint` checks for
        // the OrdMap path.
        //
        // This guard runs after both `initialize_llvm2_cache` and
        // `try_activate_compiled_fingerprinting_inner`, so it observes the
        // final configuration.
        self.enforce_llvm2_fingerprint_guard();
    }

    /// Actual activation logic, separated so the post-decision guard in
    /// `try_activate_compiled_fingerprinting` can inspect the final state.
    ///
    /// Part of #4319 Phase 0 refactor — body is unchanged from the previous
    /// implementation.
    fn try_activate_compiled_fingerprinting_inner(&mut self) {
        // Condition 1: No VIEW
        if self.compiled.cached_view_name.is_some() {
            return;
        }

        // Condition 2: No SYMMETRY
        if !self.symmetry.perms.is_empty() {
            return;
        }

        // Condition 3: JIT state layout available OR flat_state_primary confirmed.
        // The jit_state_layout is only set for compound specs (upgrade path).
        // For all-scalar specs, flat_state_primary is the reliable indicator.
        // Part of #3986: Enable compiled fingerprinting for all-scalar specs
        // even without the JIT layout (which is only needed for compound access).
        if self.jit_state_layout.is_none() && !self.flat_state_primary {
            return;
        }

        // Condition 4: Check if all init state variables are scalar.
        // We check the first init state in the queue — all states share the
        // same variable types (TLA+ is unityped per variable).
        let all_scalar = if let Some(first_init) = self.get_first_init_state_for_layout() {
            first_init
                .values()
                .iter()
                .all(|cv| cv.is_int() || cv.is_bool())
        } else {
            // If no init state available for inspection, fall back to
            // flat_state_primary which was already verified via roundtrip.
            self.flat_state_primary
        };

        if !all_scalar {
            return;
        }

        // Part of #4281: Gate activation on absence of batch-path-triggering features.
        //
        // The successor-generation dispatcher in `full_state_successors.rs` routes
        // specs with implied actions, constraints, POR, or coverage collection
        // through the batch path. The batch path calls `array_state_fingerprint`
        // with successors produced by `ArrayState::from_successor_state`, which
        // unconditionally pre-caches an FP64 (`finalize_fingerprint_xor`)
        // fingerprint on the successor `ArrayState`. The `array_state_fingerprint`
        // fast path then short-circuits on that cached FP64 value and never
        // executes the xxh3 branch — even though `jit_compiled_fp_active` is
        // true. This mixes FP64 (successors) with xxh3 (init re-fingerprint) in
        // the same `seen_fps` set, causing successors to never match init
        // fingerprints → spurious duplicate inflation.
        //
        // Refusing activation here when any batch-path trigger is configured
        // keeps `seen_fps` in a single FP64 domain for these specs. The
        // performance cost is negligible (xxh3 provides ~5% speedup on
        // all-scalar specs; specs using these features already take the slower
        // batch path).
        if !self.compiled.eval_implied_actions.is_empty()
            || !self.config.constraints.is_empty()
            || !self.config.action_constraints.is_empty()
            || self.por.independence.is_some()
            || (self.coverage.collect && !self.coverage.actions.is_empty())
        {
            return;
        }

        // Part of #4281: Gate activation on `store_full_states == false`.
        //
        // When full-state storage is enabled (liveness, trace reconstruction,
        // fairness), the `seen` HashMap is already populated with FP64 keys by
        // `init_states_full_state()` before this function runs. Activating xxh3
        // here would cause successors to be looked up in `seen_fps` with xxh3
        // fingerprints while `seen` still holds FP64 keys, breaking downstream
        // consumers (`seen.get(fp)` in liveness/safety reconstruction, trace
        // replay). Re-keying the populated `seen` HashMap mid-run is invasive
        // and introduces its own correctness risks. Keep the full-state path on
        // FP64 for single-domain consistency across `seen` and `seen_fps`.
        if self.state_storage.store_full_states {
            return;
        }

        // All conditions met — activate compiled xxh3 fingerprinting.
        self.jit_compiled_fp_active = true;

        // Pre-allocate the flat fingerprint scratch buffer to avoid resize on first use.
        // Part of #3986: Eliminate per-state Vec<i64> allocation.
        let var_count = self.ctx.var_registry().len();
        self.flat_fp_scratch.resize(var_count, 0);

        // Log activation for diagnostics.
        if super::debug::bytecode_vm_stats_enabled() {
            eprintln!(
                "[jit-fp] Compiled xxh3 fingerprinting ACTIVATED (all-scalar, no VIEW/SYMMETRY)"
            );
        }
    }

    /// Enforce the fingerprint mixed-mode invariant for LLVM2 runs.
    ///
    /// When at least one action was compiled by the LLVM2 pipeline, the BFS
    /// dispatcher (`run_gen.rs`) can emit a per-state mixture of
    /// compiled-generated and interpreter-generated successors within the
    /// same run. The crucial question is not "was an action compiled?" but
    /// "which fingerprint domain actually owns BFS dedup for this run?".
    ///
    /// For the BFS seen-set to be sound, every fingerprint entered into
    /// `seen_fps` must come from a single hash domain. `bfs_fingerprint_domain`
    /// is that classifier:
    ///   * `CompiledFlat` — xxh3 over the flat i64 buffer.
    ///   * `View` / `SymmetryCanonical` — specialized canonical domains.
    ///   * `FullStateFp64` / `ArrayFp64` — plain FP64 domains.
    ///
    /// The important subtlety is `ArrayFp64`: constrained/per-action LLVM2
    /// runs can still be perfectly sound even when `jit_compiled_fp_active`
    /// is false, because compiled successors are unflattened back into
    /// `ArrayState` and fingerprinted through the same FP64 path as
    /// interpreter successors.
    ///
    /// Part of #4319 Phase 0 (Option D).
    fn enforce_llvm2_fingerprint_guard(&mut self) {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: self.llvm2_has_compiled_action(),
            bfs_fingerprint_domain: self.bfs_fingerprint_domain(),
        };

        match state.evaluate() {
            Llvm2FingerprintGuardOutcome::NotApplicable => {}
            Llvm2FingerprintGuardOutcome::SingleDomain { domain } => {
                if super::debug::bytecode_vm_stats_enabled() {
                    eprintln!(
                        "[llvm2] fingerprint mixed-mode guard OK: domain={domain} \
                         (compiled actions routed through single fingerprint domain)"
                    );
                }
            }
        }
    }

    /// Verify layout compatibility between the flat BFS bridge and the JIT
    /// state layout.
    ///
    /// When both `flat_bfs_bridge` and `jit_state_layout` have been created
    /// (after init state solving), this checks that their slot counts agree.
    /// This is a safety net: if the two independent inference paths produce
    /// incompatible layouts, we log a warning and disable the JIT BFS path.
    ///
    /// No-op when either layout is missing (JIT disabled or no compound vars).
    ///
    /// Part of #3986: Phase 3 layout bridge verification.
    pub(in crate::check) fn verify_layout_compatibility(&self) {
        let Some(ref bridge) = self.flat_bfs_bridge else {
            return;
        };
        let Some(ref jit_layout) = self.jit_state_layout else {
            return;
        };

        let compatible = bridge.is_compatible_with_jit(jit_layout);
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();

        if compatible {
            if stats_enabled {
                eprintln!(
                    "[flat_state] layout bridge verified: check layout ({} slots) \
                     compatible with JIT layout ({} vars)",
                    bridge.num_slots(),
                    jit_layout.var_count(),
                );
            }
        } else {
            // Log a warning. The JIT BFS path should not use the check layout's
            // buffer format if they disagree. The interpreter path is always safe.
            let jit_slots = crate::state::layout_bridge::jit_layout_compact_slot_count(jit_layout);
            let mismatch = crate::state::layout_bridge::first_layout_slot_mismatch(
                bridge.layout(),
                jit_layout,
            )
            .map(|(idx, check_slots, jit_slots)| {
                format!("; first slot mismatch var#{idx}: check={check_slots}, jit={jit_slots}")
            })
            .unwrap_or_default();
            eprintln!(
                "[flat_state] WARNING: layout mismatch between check ({} vars, {} compact slots) \
                 and JIT ({} vars, {} compact slots){}. JIT BFS will use its own layout.",
                bridge.layout().var_count(),
                bridge.num_slots(),
                jit_layout.var_count(),
                jit_slots,
                mismatch,
            );
        }
    }
}

/// Pure-data view of the inputs to the fingerprint mixed-mode guard.
///
/// Extracted from `ModelChecker` state so the decision logic in
/// [`Llvm2FingerprintGuardState::evaluate`] can be unit-tested without
/// constructing a full `ModelChecker`. See the design doc
/// `designs/2026-04-20-llvm2-fingerprint-unification.md` Phase 0 / Option D.
///
/// Part of #4319.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::check) struct Llvm2FingerprintGuardState {
    /// True iff `Llvm2NativeCache::has_any_compiled_action()` reports at least
    /// one successfully compiled next-state action.
    pub llvm2_has_compiled_action: bool,
    /// The actual BFS fingerprint domain selected for the current run.
    pub bfs_fingerprint_domain: BfsFingerprintDomain,
}

/// Outcome of the fingerprint mixed-mode guard.
///
/// Part of #4319 Phase 0 (Option D).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::check) enum Llvm2FingerprintGuardOutcome {
    /// No LLVM2 compiled action is present; the guard has nothing to check.
    /// (The pure BFS interpreter path uses a single FP64 domain throughout.)
    NotApplicable,
    /// At least one LLVM2 compiled action is present AND the configuration
    /// pins all successors to a single fingerprint domain. `domain` is a short
    /// human-readable tag identifying which branch took effect, used for
    /// diagnostic logging.
    SingleDomain { domain: &'static str },
}

impl Llvm2FingerprintGuardState {
    /// Classify the current fingerprint configuration.
    ///
    /// Part of #4319 Phase 0 (Option D).
    #[must_use]
    pub(in crate::check) fn evaluate(&self) -> Llvm2FingerprintGuardOutcome {
        if !self.llvm2_has_compiled_action {
            return Llvm2FingerprintGuardOutcome::NotApplicable;
        }
        Llvm2FingerprintGuardOutcome::SingleDomain {
            domain: self.bfs_fingerprint_domain.diagnostic_name(),
        }
    }
}

#[cfg(test)]
mod llvm2_fingerprint_guard_tests {
    //! Unit tests for the Phase 0 fingerprint mixed-mode guard.
    //!
    //! Part of #4319. See
    //! `designs/2026-04-20-llvm2-fingerprint-unification.md` Phase 0 / Option D.

    use super::{BfsFingerprintDomain, Llvm2FingerprintGuardOutcome, Llvm2FingerprintGuardState};

    /// Baseline: no compiled action, no single-domain flags — guard is inert.
    #[test]
    fn no_compiled_action_is_not_applicable() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: false,
            bfs_fingerprint_domain: BfsFingerprintDomain::ArrayFp64,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::NotApplicable
        );
    }

    /// Even if single-domain flags are set, a run without compiled actions
    /// never enters the guarded code path and must classify as NotApplicable.
    #[test]
    fn no_compiled_action_ignores_other_flags() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: false,
            bfs_fingerprint_domain: BfsFingerprintDomain::CompiledFlat,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::NotApplicable
        );
    }

    /// Compiled action + jit_compiled_fp_active = xxh3 single domain.
    #[test]
    fn compiled_with_jit_fp_active_is_xxh3_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            bfs_fingerprint_domain: BfsFingerprintDomain::CompiledFlat,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "xxh3_flat_compiled",
            }
        );
    }

    /// Compiled action + store_full_states = FP64 single domain.
    #[test]
    fn compiled_with_store_full_states_is_fp64_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            bfs_fingerprint_domain: BfsFingerprintDomain::FullStateFp64,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "fp64_full_states",
            }
        );
    }

    /// Compiled action + VIEW = VIEW single domain (all fps via VIEW output).
    #[test]
    fn compiled_with_view_is_view_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            bfs_fingerprint_domain: BfsFingerprintDomain::View,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain { domain: "view" }
        );
    }

    /// Compiled action + symmetry = symmetry-canonical single domain.
    #[test]
    fn compiled_with_symmetry_is_symmetry_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            bfs_fingerprint_domain: BfsFingerprintDomain::SymmetryCanonical,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "symmetry_canonical",
            }
        );
    }

    /// Regression for the constrained LLVM2 lane: compiled actions can still
    /// be sound on the plain ArrayState FP64 domain when constraints/implied
    /// actions force the per-action/full-state successor path.
    #[test]
    fn compiled_with_array_fp64_domain_is_still_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            bfs_fingerprint_domain: BfsFingerprintDomain::ArrayFp64,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "fp64_array_state",
            }
        );
    }

    /// Each BFS fingerprint domain should map to a stable diagnostic tag.
    #[test]
    fn domain_tags_are_stable() {
        let domains = [
            (BfsFingerprintDomain::CompiledFlat, "xxh3_flat_compiled"),
            (BfsFingerprintDomain::FullStateFp64, "fp64_full_states"),
            (BfsFingerprintDomain::View, "view"),
            (
                BfsFingerprintDomain::SymmetryCanonical,
                "symmetry_canonical",
            ),
            (BfsFingerprintDomain::ArrayFp64, "fp64_array_state"),
        ];

        for (domain, expected) in domains {
            let state = Llvm2FingerprintGuardState {
                llvm2_has_compiled_action: true,
                bfs_fingerprint_domain: domain,
            };
            assert_eq!(
                state.evaluate(),
                Llvm2FingerprintGuardOutcome::SingleDomain { domain: expected }
            );
        }
    }
}

#[cfg(test)]
#[path = "run_prepare_tests.rs"]
mod run_prepare_tests;
