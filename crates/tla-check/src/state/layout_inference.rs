// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Layout inference from initial state values.
//!
//! Given an `ArrayState` (typically the first initial state), infers a
//! `StateLayout` that maps each variable to its optimal flat representation.
//!
//! # Inference rules
//!
//! | Value type                     | VarLayoutKind            |
//! |-------------------------------|--------------------------|
//! | Bool                          | ScalarBool               |
//! | SmallInt / Int                | Scalar                   |
//! | IntFunc (int interval domain) | IntArray { lo, len }     |
//! | Record (all scalar fields)    | Record { field_names }   |
//! | Set                           | Dynamic (Bitmask deferred)|
//! | Everything else               | Dynamic                  |
//!
//! Part of #3986.

use super::array_state::ArrayState;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::state_layout::{
    ordered_dense_int_domain, FlatScalarValue, FlatValueLayout, SequenceBoundEvidence, SlotType,
    StateLayout, VarLayoutKind,
};
use crate::var_index::VarRegistry;
use crate::Value;
use tla_core::ast::{BoundPattern, BoundVar, Expr, OperatorDef};
use tla_core::name_intern::{intern_name, NameId};

/// A state-path step for a proven recursive sequence capacity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SequenceCapacityPathStep {
    /// Any key in a homogeneous function range, e.g. `network[p]`.
    HomogeneousRange { domain: Arc<[Value]> },
    /// A record field, e.g. `msg.clock`.
    RecordField(Arc<str>),
    /// Any sequence element.
    SequenceElement,
}

/// Source-level proof that every sequence at a state path has capacity `max_len`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SequenceCapacityProof {
    pub(crate) var_idx: usize,
    pub(crate) path: Vec<SequenceCapacityPathStep>,
    pub(crate) max_len: usize,
    pub(crate) invariant: Arc<str>,
}

/// Source-level proof of the element layout for every sequence at a state path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SequenceElementLayoutProof {
    pub(crate) var_idx: usize,
    pub(crate) path: Vec<SequenceCapacityPathStep>,
    pub(crate) element_layout: FlatValueLayout,
    pub(crate) invariant: Arc<str>,
}

/// Source-level proof that a TLA sequence-shaped value is really a fixed
/// function over a finite `1..N` domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SequenceFixedDomainTypeProof {
    pub(crate) var_idx: usize,
    pub(crate) path: Vec<SequenceCapacityPathStep>,
    pub(crate) domain: Arc<[Value]>,
    pub(crate) element_layout: SequenceTypeLayoutProof,
    pub(crate) invariant: Arc<str>,
}

/// Source-level proof of a sequence-shaped element layout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SequenceTypeLayoutProof {
    /// A concrete fixed flat layout for this value.
    Flat(FlatValueLayout),
    /// A TLA `Seq(T)` value. This proves element layout but not capacity.
    Sequence {
        element_layout: Box<SequenceTypeLayoutProof>,
    },
    /// A fixed `1..N` function domain that is represented as a TLA sequence.
    FixedDomainSequence {
        max_len: usize,
        element_layout: Box<SequenceTypeLayoutProof>,
    },
}

/// Infer a `StateLayout` from an initial state.
///
/// Examines each variable's value to determine the best flat representation.
/// The inferred layout is valid for all states in a model-checking run IF the
/// variable types are uniform (which is guaranteed by TLA+ typing: a variable
/// that starts as a function stays a function through all transitions).
///
/// # Arguments
///
/// * `initial_state` - The first initial state to analyze.
/// * `registry` - Variable name registry.
#[must_use]
pub(crate) fn infer_layout(initial_state: &ArrayState, registry: &VarRegistry) -> StateLayout {
    infer_layout_with_sequence_proofs(initial_state, registry, &[])
}

/// Infer a `StateLayout` from an initial state, applying proven sequence
/// capacities to matching recursive sequence paths.
#[must_use]
pub(crate) fn infer_layout_with_sequence_proofs(
    initial_state: &ArrayState,
    registry: &VarRegistry,
    sequence_proofs: &[SequenceCapacityProof],
) -> StateLayout {
    infer_layout_with_sequence_layout_proofs(initial_state, registry, sequence_proofs, &[], &[])
}

/// Infer a `StateLayout` from an initial state, applying proven sequence
/// capacities and element layouts to matching recursive sequence paths.
#[must_use]
pub(crate) fn infer_layout_with_sequence_layout_proofs(
    initial_state: &ArrayState,
    registry: &VarRegistry,
    sequence_proofs: &[SequenceCapacityProof],
    sequence_element_proofs: &[SequenceElementLayoutProof],
    sequence_fixed_domain_type_proofs: &[SequenceFixedDomainTypeProof],
) -> StateLayout {
    let compact_values = initial_state.values();
    let values: Vec<Value> = compact_values.iter().map(Value::from).collect();
    let context = LayoutInferenceContext::from_value_rows_and_sequence_layout_proofs(
        [values.as_slice()],
        sequence_proofs,
        sequence_element_proofs,
        sequence_fixed_domain_type_proofs,
    );
    let mut kinds = Vec::with_capacity(compact_values.len());

    for (var_idx, value) in values.iter().enumerate() {
        let path = SequencePath::root(var_idx);
        let kind = infer_kind_from_value_with_context(value, &context, &path);
        kinds.push(kind);
    }

    StateLayout::new(registry, kinds)
}

/// Infer a `StateLayout` from a wavefront of states (~first 1000 states).
///
/// Examines multiple states and merges their inferred layouts conservatively:
/// for each variable, if all sampled states agree on the layout kind, that kind
/// is used; if any state disagrees, the variable falls back to `Dynamic`.
///
/// This is more robust than single-state inference because it handles edge
/// cases where the first initial state might have an unusual shape (e.g.,
/// an empty function that later becomes non-empty, or a record with
/// different field sets across initial states).
///
/// # Arguments
///
/// * `states` - Slice of initial/wavefront states to analyze. Must be non-empty.
/// * `registry` - Variable name registry.
///
/// # Panics
///
/// Panics if `states` is empty.
///
/// Part of #3986: Layout inference from first wavefront (~1000 states).
#[must_use]
pub(crate) fn infer_layout_from_wavefront(
    states: &[ArrayState],
    registry: &VarRegistry,
) -> StateLayout {
    infer_layout_from_wavefront_with_sequence_proofs(states, registry, &[])
}

/// Infer a `StateLayout` from a wavefront, applying proven sequence capacities
/// to matching recursive sequence paths.
#[must_use]
pub(crate) fn infer_layout_from_wavefront_with_sequence_proofs(
    states: &[ArrayState],
    registry: &VarRegistry,
    sequence_proofs: &[SequenceCapacityProof],
) -> StateLayout {
    infer_layout_from_wavefront_with_sequence_layout_proofs(
        states,
        registry,
        sequence_proofs,
        &[],
        &[],
    )
}

/// Infer a `StateLayout` from a wavefront, applying proven sequence capacities
/// and element layouts to matching recursive sequence paths.
#[must_use]
pub(crate) fn infer_layout_from_wavefront_with_sequence_layout_proofs(
    states: &[ArrayState],
    registry: &VarRegistry,
    sequence_proofs: &[SequenceCapacityProof],
    sequence_element_proofs: &[SequenceElementLayoutProof],
    sequence_fixed_domain_type_proofs: &[SequenceFixedDomainTypeProof],
) -> StateLayout {
    assert!(
        !states.is_empty(),
        "infer_layout_from_wavefront requires at least one state"
    );

    let value_rows: Vec<Vec<Value>> = states
        .iter()
        .map(|state| state.values().iter().map(Value::from).collect())
        .collect();
    let row_refs: Vec<&[Value]> = value_rows.iter().map(Vec::as_slice).collect();
    let context = LayoutInferenceContext::from_value_rows_and_sequence_layout_proofs(
        row_refs.iter().copied(),
        sequence_proofs,
        sequence_element_proofs,
        sequence_fixed_domain_type_proofs,
    );

    // Start with the first state's layout.
    let first_values = &value_rows[0];
    let num_vars = first_values.len();
    let mut kinds: Vec<VarLayoutKind> = first_values
        .iter()
        .enumerate()
        .map(|(var_idx, value)| {
            let path = SequencePath::root(var_idx);
            infer_kind_from_value_with_context(value, &context, &path)
        })
        .collect();

    // Merge with subsequent states: if any disagree, downgrade to Dynamic.
    for values in &value_rows[1..] {
        debug_assert_eq!(
            values.len(),
            num_vars,
            "infer_layout_from_wavefront: all states must have the same number of variables"
        );

        for (var_idx, cv) in values.iter().enumerate() {
            // Skip variables already downgraded to Dynamic.
            if matches!(kinds[var_idx], VarLayoutKind::Dynamic) {
                continue;
            }

            let path = SequencePath::root(var_idx);
            let new_kind = infer_kind_from_value_with_context(cv, &context, &path);
            if let Some(merged) = merge_layout_kinds(&kinds[var_idx], &new_kind) {
                kinds[var_idx] = merged;
            } else {
                // Incompatible shapes: fall back to Dynamic.
                kinds[var_idx] = VarLayoutKind::Dynamic;
            }
        }
    }

    StateLayout::new(registry, kinds)
}

/// Check if two `VarLayoutKind`s are compatible (same structure).
///
/// Two kinds are compatible if they describe the same representation:
/// same variant, same dimensions, same field names. This is stricter
/// than just matching the variant — `IntArray{lo=0, len=3}` is NOT
/// compatible with `IntArray{lo=0, len=4}`.
fn layout_kinds_compatible(a: &VarLayoutKind, b: &VarLayoutKind) -> bool {
    match (a, b) {
        (VarLayoutKind::Scalar, VarLayoutKind::Scalar) => true,
        (VarLayoutKind::ScalarBool, VarLayoutKind::ScalarBool) => true,
        (VarLayoutKind::ScalarString, VarLayoutKind::ScalarString) => true,
        (VarLayoutKind::ScalarModelValue, VarLayoutKind::ScalarModelValue) => true,
        (
            VarLayoutKind::IntArray {
                lo: lo_a,
                len: len_a,
                elements_are_bool: eb_a,
                element_types: et_a,
                ..
            },
            VarLayoutKind::IntArray {
                lo: lo_b,
                len: len_b,
                elements_are_bool: eb_b,
                element_types: et_b,
                ..
            },
        ) => lo_a == lo_b && len_a == len_b && eb_a == eb_b && et_a == et_b,
        (
            VarLayoutKind::Record {
                field_names: fn_a,
                field_is_bool: fb_a,
                field_types: ft_a,
                ..
            },
            VarLayoutKind::Record {
                field_names: fn_b,
                field_is_bool: fb_b,
                field_types: ft_b,
                ..
            },
        ) => fn_a == fn_b && fb_a == fb_b && ft_a == ft_b,
        (
            VarLayoutKind::StringKeyedArray {
                domain_keys: dk_a,
                domain_types: dt_a,
                value_types: vt_a,
                ..
            },
            VarLayoutKind::StringKeyedArray {
                domain_keys: dk_b,
                domain_types: dt_b,
                value_types: vt_b,
                ..
            },
        ) => dk_a == dk_b && dt_a == dt_b && vt_a == vt_b,
        (
            VarLayoutKind::Bitmask { universe_size: ua },
            VarLayoutKind::Bitmask { universe_size: ub },
        ) => ua == ub,
        (VarLayoutKind::Recursive { layout: a }, VarLayoutKind::Recursive { layout: b }) => a == b,
        (VarLayoutKind::Dynamic, VarLayoutKind::Dynamic) => true,
        _ => false,
    }
}

/// Merge two layout kinds inferred from different sampled states.
///
/// Most legacy layouts require exact structural equality. Recursive bounded
/// sequence layouts are allowed to grow to the largest sampled capacity, and
/// bitmask set universes may union while they still fit in one i64.
fn merge_layout_kinds(a: &VarLayoutKind, b: &VarLayoutKind) -> Option<VarLayoutKind> {
    match (a, b) {
        (VarLayoutKind::Recursive { layout: a }, VarLayoutKind::Recursive { layout: b }) => {
            merge_flat_value_layouts(a, b).map(|layout| VarLayoutKind::Recursive { layout })
        }
        _ if layout_kinds_compatible(a, b) => Some(a.clone()),
        _ => None,
    }
}

#[derive(Default)]
struct LayoutInferenceContext {
    scalar_domain_candidates: Vec<Vec<FlatScalarValue>>,
    sequence_hints: Vec<SequenceHint>,
    sequence_proofs: Vec<SequenceProofHint>,
    sequence_element_proofs: Vec<SequenceElementProofHint>,
    sequence_fixed_domain_type_proofs: Vec<SequenceFixedDomainTypeProofHint>,
}

#[derive(Clone, PartialEq, Eq)]
struct SequenceHint {
    path: SequencePath,
    max_len: usize,
    element_layout: FlatValueLayout,
}

#[derive(Clone, PartialEq, Eq)]
struct SequenceProofHint {
    path: SequencePath,
    max_len: usize,
    invariant: Arc<str>,
}

#[derive(Clone, PartialEq, Eq)]
struct SequenceElementProofHint {
    path: SequencePath,
    element_layout: FlatValueLayout,
    invariant: Arc<str>,
}

#[derive(Clone, PartialEq, Eq)]
struct SequenceFixedDomainTypeProofHint {
    path: SequencePath,
    domain: Arc<[Value]>,
    element_layout: SequenceTypeLayoutProof,
    invariant: Arc<str>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SequencePath(Vec<SequencePathStep>);

#[derive(Debug, Clone, PartialEq, Eq)]
enum SequencePathStep {
    Var(usize),
    HomogeneousRange(Arc<[Value]>),
    RecordField(Arc<str>),
    SequenceElement,
    SetElement,
}

impl SequencePath {
    fn root(var_idx: usize) -> Self {
        Self(vec![SequencePathStep::Var(var_idx)])
    }

    fn child(&self, step: SequencePathStep) -> Self {
        let mut path = self.0.clone();
        path.push(step);
        Self(path)
    }
}

impl LayoutInferenceContext {
    fn from_value_rows<'a, I>(rows: I) -> Self
    where
        I: IntoIterator<Item = &'a [Value]>,
    {
        Self::from_value_rows_and_sequence_proofs(rows, &[])
    }

    fn from_value_rows_and_sequence_proofs<'a, I>(
        rows: I,
        sequence_proofs: &[SequenceCapacityProof],
    ) -> Self
    where
        I: IntoIterator<Item = &'a [Value]>,
    {
        Self::from_value_rows_and_sequence_layout_proofs(rows, sequence_proofs, &[], &[])
    }

    fn from_value_rows_and_sequence_layout_proofs<'a, I>(
        rows: I,
        sequence_proofs: &[SequenceCapacityProof],
        sequence_element_proofs: &[SequenceElementLayoutProof],
        sequence_fixed_domain_type_proofs: &[SequenceFixedDomainTypeProof],
    ) -> Self
    where
        I: IntoIterator<Item = &'a [Value]>,
    {
        let rows: Vec<&[Value]> = rows.into_iter().collect();
        let mut context = LayoutInferenceContext {
            sequence_proofs: dedup_exact(
                sequence_proofs
                    .iter()
                    .flat_map(sequence_proof_to_hints)
                    .collect(),
            ),
            sequence_element_proofs: dedup_exact(
                sequence_element_proofs
                    .iter()
                    .flat_map(sequence_element_proof_to_hints)
                    .collect(),
            ),
            sequence_fixed_domain_type_proofs: dedup_exact(
                sequence_fixed_domain_type_proofs
                    .iter()
                    .flat_map(sequence_fixed_domain_type_proof_to_hints)
                    .collect(),
            ),
            ..LayoutInferenceContext::default()
        };

        for row in &rows {
            for value in *row {
                collect_scalar_domain_candidates(value, &mut context.scalar_domain_candidates);
            }
        }

        loop {
            let before = context.sequence_hints.clone();
            let mut sequence_hints = before.clone();
            for row in &rows {
                for (var_idx, value) in row.iter().enumerate() {
                    let path = SequencePath::root(var_idx);
                    collect_sequence_hints(value, &context, &mut sequence_hints, &path);
                }
            }
            if sequence_hints == before {
                break;
            }
            context.sequence_hints = sequence_hints;
        }
        context
    }

    fn unique_scalar_domain_covering(
        &self,
        elements: &[FlatScalarValue],
    ) -> Option<Vec<FlatScalarValue>> {
        let matches: Vec<&Vec<FlatScalarValue>> = self
            .scalar_domain_candidates
            .iter()
            .filter(|candidate| {
                candidate.len() <= 63 && elements.iter().all(|elem| candidate.contains(elem))
            })
            .collect();
        let mut dominant = matches.iter().copied().filter(|candidate| {
            matches
                .iter()
                .all(|other| other.iter().all(|elem| candidate.contains(elem)))
        });
        let first = dominant.next()?;
        dominant.next().is_none().then(|| first.clone())
    }

    fn unique_sequence_hint(&self, path: &SequencePath) -> Option<&SequenceHint> {
        let mut hints = self.sequence_hints.iter().filter(|hint| &hint.path == path);
        let first = hints.next()?;
        hints.all(|hint| hint == first).then_some(first)
    }

    fn unique_sequence_proof(
        &self,
        path: &SequencePath,
        observed_len: usize,
    ) -> Option<&SequenceProofHint> {
        let mut hints = self
            .sequence_proofs
            .iter()
            .filter(|hint| &hint.path == path && hint.max_len >= observed_len);
        let first = hints.next()?;
        hints.all(|hint| hint == first).then_some(first)
    }

    fn unique_sequence_element_proof(
        &self,
        path: &SequencePath,
    ) -> Option<&SequenceElementProofHint> {
        let mut hints = self
            .sequence_element_proofs
            .iter()
            .filter(|hint| &hint.path == path);
        let first = hints.next()?;
        hints.all(|hint| hint == first).then_some(first)
    }

    fn unique_sequence_fixed_domain_type_proof(
        &self,
        path: &SequencePath,
    ) -> Option<&SequenceFixedDomainTypeProofHint> {
        let mut hints = self
            .sequence_fixed_domain_type_proofs
            .iter()
            .filter(|hint| &hint.path == path);
        let first = hints.next()?;
        hints.all(|hint| hint == first).then_some(first)
    }
}

fn dedup_exact<T: PartialEq>(hints: Vec<T>) -> Vec<T> {
    let mut deduped = Vec::with_capacity(hints.len());
    for hint in hints {
        if !deduped.iter().any(|existing| existing == &hint) {
            deduped.push(hint);
        }
    }
    deduped
}

fn sequence_proof_to_hints(proof: &SequenceCapacityProof) -> Vec<SequenceProofHint> {
    sequence_capacity_path_aliases(proof.var_idx, &proof.path)
        .into_iter()
        .map(|path| SequenceProofHint {
            path,
            max_len: proof.max_len,
            invariant: Arc::clone(&proof.invariant),
        })
        .collect()
}

fn sequence_element_proof_to_hints(
    proof: &SequenceElementLayoutProof,
) -> Vec<SequenceElementProofHint> {
    sequence_capacity_path_aliases(proof.var_idx, &proof.path)
        .into_iter()
        .map(|path| SequenceElementProofHint {
            path,
            element_layout: proof.element_layout.clone(),
            invariant: Arc::clone(&proof.invariant),
        })
        .collect()
}

fn sequence_fixed_domain_type_proof_to_hints(
    proof: &SequenceFixedDomainTypeProof,
) -> Vec<SequenceFixedDomainTypeProofHint> {
    sequence_capacity_path_aliases(proof.var_idx, &proof.path)
        .into_iter()
        .map(|path| SequenceFixedDomainTypeProofHint {
            path,
            domain: Arc::clone(&proof.domain),
            element_layout: proof.element_layout.clone(),
            invariant: Arc::clone(&proof.invariant),
        })
        .collect()
}

fn domain_is_one_based_int_interval(domain: &[Value], lo: i64, len: usize) -> bool {
    if domain.is_empty() || len == 0 || lo != 1 || domain.len() != len {
        return false;
    }
    domain
        .iter()
        .enumerate()
        .all(|(index, value)| matches!(value, Value::SmallInt(n) if *n == index as i64 + 1))
}

fn contiguous_int_value_domain(domain: &[Value]) -> Option<(i64, usize)> {
    let mut ints: Vec<i64> = domain
        .iter()
        .map(|value| match value {
            Value::SmallInt(n) => Some(*n),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    if ints.is_empty() {
        return None;
    }
    ints.sort_unstable();
    ints.dedup();
    if ints.len() != domain.len() {
        return None;
    }
    let lo = ints[0];
    let hi = *ints.last()?;
    let len = usize::try_from(hi.checked_sub(lo)? + 1).ok()?;
    (len == ints.len()).then_some((lo, len))
}

fn sequence_capacity_path_aliases(
    var_idx: usize,
    proof_path: &[SequenceCapacityPathStep],
) -> Vec<SequencePath> {
    let mut paths = vec![vec![SequencePathStep::Var(var_idx)]];
    for step in proof_path {
        let mut next_paths = Vec::with_capacity(paths.len() * 2);
        match step {
            SequenceCapacityPathStep::HomogeneousRange { domain } => {
                let sequence_shaped_domain = contiguous_int_value_domain(domain)
                    .is_some_and(|(lo, len)| domain_is_one_based_int_interval(domain, lo, len));
                for path in paths {
                    let mut function_path = path.clone();
                    function_path.push(SequencePathStep::HomogeneousRange(Arc::clone(domain)));
                    next_paths.push(function_path);

                    if sequence_shaped_domain {
                        let mut sequence_path = path;
                        sequence_path.push(SequencePathStep::SequenceElement);
                        next_paths.push(sequence_path);
                    }
                }
            }
            SequenceCapacityPathStep::RecordField(name) => {
                for mut path in paths {
                    path.push(SequencePathStep::RecordField(Arc::clone(name)));
                    next_paths.push(path);
                }
            }
            SequenceCapacityPathStep::SequenceElement => {
                for mut path in paths {
                    path.push(SequencePathStep::SequenceElement);
                    next_paths.push(path);
                }
            }
        }
        paths = next_paths;
    }
    dedup_exact(paths.into_iter().map(SequencePath).collect())
}

fn sequence_bound_evidence_for_path(
    context: &LayoutInferenceContext,
    path: &SequencePath,
    observed_len: usize,
    element_invariant: Option<&Arc<str>>,
) -> (SequenceBoundEvidence, usize) {
    if let Some(proof) = context.unique_sequence_proof(path, observed_len) {
        let bound = if let Some(element_invariant) = element_invariant {
            SequenceBoundEvidence::ProvenInvariantWithElementLayout {
                invariant: Arc::clone(&proof.invariant),
                element_invariant: Arc::clone(element_invariant),
            }
        } else {
            SequenceBoundEvidence::ProvenInvariant {
                invariant: Arc::clone(&proof.invariant),
            }
        };
        (bound, proof.max_len)
    } else {
        (SequenceBoundEvidence::Observed, observed_len)
    }
}

fn fixed_domain_sequence_layout_for_path(
    context: &LayoutInferenceContext,
    path: &SequencePath,
    observed_len: usize,
    element_layout: &FlatValueLayout,
) -> Option<(SequenceBoundEvidence, usize, FlatValueLayout)> {
    let proof = context.unique_sequence_fixed_domain_type_proof(path)?;
    if proof.domain.is_empty() {
        return None;
    }
    let element_layout =
        sequence_type_layout_proof_apply_flat_layout(&proof.element_layout, element_layout)?;
    (observed_len == proof.domain.len()).then(|| {
        (
            SequenceBoundEvidence::FixedDomainTypeLayout {
                invariant: Arc::clone(&proof.invariant),
            },
            proof.domain.len(),
            element_layout,
        )
    })
}

pub(crate) fn collect_sequence_element_layout_proofs(
    expr: &Expr,
    invariant: &str,
    registry: &VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    out: &mut Vec<SequenceElementLayoutProof>,
) {
    collect_sequence_element_layout_proofs_inner(
        expr,
        invariant,
        registry,
        constants,
        proof_domains,
        None,
        None,
        &mut ElementProofScope::default(),
        &mut BTreeSet::new(),
        out,
    );
}

pub(crate) fn collect_sequence_element_layout_proofs_with_ops(
    expr: &Expr,
    invariant: &str,
    registry: &VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    out: &mut Vec<SequenceElementLayoutProof>,
) {
    collect_sequence_element_layout_proofs_inner(
        expr,
        invariant,
        registry,
        constants,
        proof_domains,
        Some(op_defs),
        Some(op_replacements),
        &mut ElementProofScope::default(),
        &mut BTreeSet::new(),
        out,
    );
}

pub(crate) fn collect_sequence_fixed_domain_type_proofs_with_ops(
    expr: &Expr,
    invariant: &str,
    registry: &VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    out: &mut Vec<SequenceFixedDomainTypeProof>,
) {
    collect_sequence_fixed_domain_type_proofs_inner(
        expr,
        invariant,
        registry,
        constants,
        proof_domains,
        op_defs,
        op_replacements,
        &mut ElementProofScope::default(),
        &mut BTreeSet::new(),
        out,
    );
}

fn collect_sequence_fixed_domain_type_proofs_inner(
    expr: &Expr,
    invariant: &str,
    registry: &VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    scope: &mut ElementProofScope,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<SequenceFixedDomainTypeProof>,
) {
    match expr {
        Expr::And(left, right) => {
            collect_sequence_fixed_domain_type_proofs_inner(
                &left.node,
                invariant,
                registry,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                scope,
                visiting,
                out,
            );
            collect_sequence_fixed_domain_type_proofs_inner(
                &right.node,
                invariant,
                registry,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                scope,
                visiting,
                out,
            );
        }
        Expr::Forall(vars, body) => {
            if let Some(added) = push_element_bounded_quantifier_names(vars, proof_domains, scope) {
                collect_sequence_fixed_domain_type_proofs_inner(
                    &body.node,
                    invariant,
                    registry,
                    constants,
                    proof_domains,
                    op_defs,
                    op_replacements,
                    scope,
                    visiting,
                    out,
                );
                for name in added {
                    scope.pop(&name);
                }
            }
        }
        Expr::In(left, right) => {
            let mut used_bindings = BTreeSet::new();
            if let Some((var_idx, path)) =
                extract_type_state_path(&left.node, registry, scope, &mut used_bindings)
            {
                collect_sequence_fixed_domain_type_proofs_from_type_expr(
                    &right.node,
                    invariant,
                    var_idx,
                    path,
                    constants,
                    proof_domains,
                    op_defs,
                    op_replacements,
                    visiting,
                    out,
                );
            }
        }
        Expr::Ident(name, _) if !scope.is_bound(name) => {
            collect_sequence_fixed_domain_type_proofs_from_zero_arg_op(
                name,
                invariant,
                registry,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                scope,
                visiting,
                out,
            );
        }
        Expr::OpRef(name) => collect_sequence_fixed_domain_type_proofs_from_zero_arg_op(
            name,
            invariant,
            registry,
            constants,
            proof_domains,
            op_defs,
            op_replacements,
            scope,
            visiting,
            out,
        ),
        _ => {}
    }
}

fn collect_sequence_fixed_domain_type_proofs_from_zero_arg_op(
    name: &str,
    invariant: &str,
    registry: &VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    scope: &mut ElementProofScope,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<SequenceFixedDomainTypeProof>,
) {
    let Some((resolved_name, def)) = layout_safe_op_def(name, op_defs, Some(op_replacements))
    else {
        return;
    };
    if !def.params.is_empty() {
        return;
    }
    if !visiting.insert(resolved_name.to_owned()) {
        return;
    }
    collect_sequence_fixed_domain_type_proofs_inner(
        &def.body.node,
        invariant,
        registry,
        constants,
        proof_domains,
        op_defs,
        op_replacements,
        scope,
        visiting,
        out,
    );
    visiting.remove(resolved_name);
}

fn collect_sequence_element_layout_proofs_inner(
    expr: &Expr,
    invariant: &str,
    registry: &VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: Option<&tla_core::OpEnv>,
    op_replacements: Option<&tla_core::kani_types::HashMap<String, String>>,
    scope: &mut ElementProofScope,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<SequenceElementLayoutProof>,
) {
    match expr {
        Expr::And(left, right) => {
            collect_sequence_element_layout_proofs_inner(
                &left.node,
                invariant,
                registry,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                scope,
                visiting,
                out,
            );
            collect_sequence_element_layout_proofs_inner(
                &right.node,
                invariant,
                registry,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                scope,
                visiting,
                out,
            );
        }
        Expr::Forall(vars, body) => {
            if let Some(added) = push_element_bounded_quantifier_names(vars, proof_domains, scope) {
                collect_sequence_element_layout_proofs_inner(
                    &body.node,
                    invariant,
                    registry,
                    constants,
                    proof_domains,
                    op_defs,
                    op_replacements,
                    scope,
                    visiting,
                    out,
                );
                for name in added {
                    scope.pop(&name);
                }
            }
        }
        Expr::In(left, right) => {
            let mut used_bindings = BTreeSet::new();
            if let Some((var_idx, path)) =
                extract_type_state_path(&left.node, registry, scope, &mut used_bindings)
            {
                collect_sequence_element_layout_proofs_from_type_expr(
                    &right.node,
                    invariant,
                    var_idx,
                    path,
                    constants,
                    proof_domains,
                    op_defs,
                    op_replacements,
                    out,
                );
            }
        }
        Expr::Ident(name, _) if !scope.is_bound(name) => {
            collect_sequence_element_layout_proofs_from_zero_arg_op(
                name,
                invariant,
                registry,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                scope,
                visiting,
                out,
            );
        }
        Expr::OpRef(name) => collect_sequence_element_layout_proofs_from_zero_arg_op(
            name,
            invariant,
            registry,
            constants,
            proof_domains,
            op_defs,
            op_replacements,
            scope,
            visiting,
            out,
        ),
        _ => {}
    }
}

fn collect_sequence_element_layout_proofs_from_zero_arg_op(
    name: &str,
    invariant: &str,
    registry: &VarRegistry,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: Option<&tla_core::OpEnv>,
    op_replacements: Option<&tla_core::kani_types::HashMap<String, String>>,
    scope: &mut ElementProofScope,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<SequenceElementLayoutProof>,
) {
    let Some(op_defs) = op_defs else {
        return;
    };
    let Some((resolved_name, def)) = layout_safe_op_def(name, op_defs, op_replacements) else {
        return;
    };
    if !visiting.insert(resolved_name.to_owned()) {
        return;
    }
    collect_sequence_element_layout_proofs_inner(
        &def.body.node,
        invariant,
        registry,
        constants,
        proof_domains,
        Some(op_defs),
        op_replacements,
        scope,
        visiting,
        out,
    );
    visiting.remove(resolved_name);
}

fn collect_sequence_element_layout_proofs_from_type_expr(
    expr: &Expr,
    invariant: &str,
    var_idx: usize,
    path: Vec<SequenceCapacityPathStep>,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: Option<&tla_core::OpEnv>,
    op_replacements: Option<&tla_core::kani_types::HashMap<String, String>>,
    out: &mut Vec<SequenceElementLayoutProof>,
) {
    match expr {
        Expr::FuncSet(domain, range) => {
            let Some(domain) = type_domain_values_with_replacements(
                &domain.node,
                constants,
                proof_domains,
                op_replacements,
            ) else {
                return;
            };
            let mut child_path = path;
            child_path.push(SequenceCapacityPathStep::HomogeneousRange { domain });
            collect_sequence_element_layout_proofs_from_type_expr(
                &range.node,
                invariant,
                var_idx,
                child_path,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                out,
            );
        }
        Expr::Apply(op, args) if args.len() == 1 && is_seq_operator(&op.node, op_replacements) => {
            if let Some(element_layout) = flat_layout_from_type_set_expr_with_ops(
                &args[0].node,
                constants,
                op_defs,
                op_replacements,
            ) {
                push_sequence_element_layout_proof(
                    out,
                    SequenceElementLayoutProof {
                        var_idx,
                        path,
                        element_layout,
                        invariant: Arc::from(invariant),
                    },
                );
            }
        }
        _ => {}
    }
}

fn push_sequence_element_layout_proof(
    out: &mut Vec<SequenceElementLayoutProof>,
    proof: SequenceElementLayoutProof,
) {
    if !out.iter().any(|existing| existing == &proof) {
        out.push(proof);
    }
}

fn collect_sequence_fixed_domain_type_proofs_from_type_expr(
    expr: &Expr,
    invariant: &str,
    var_idx: usize,
    path: Vec<SequenceCapacityPathStep>,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<SequenceFixedDomainTypeProof>,
) {
    match expr {
        Expr::FuncSet(domain, range) => {
            let Some(domain) = type_domain_values_with_replacements(
                &domain.node,
                constants,
                proof_domains,
                Some(op_replacements),
            ) else {
                return;
            };
            let element_layout = sequence_type_layout_proof_from_type_set_expr(
                &range.node,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                visiting,
            );
            if domain_is_one_based_int_interval(&domain, 1, domain.len()) {
                if let Some(element_layout) = element_layout.clone() {
                    push_sequence_fixed_domain_type_proof(
                        out,
                        SequenceFixedDomainTypeProof {
                            var_idx,
                            path: path.clone(),
                            domain: Arc::clone(&domain),
                            element_layout,
                            invariant: Arc::from(invariant),
                        },
                    );
                }
            }
            let mut child_path = path;
            child_path.push(SequenceCapacityPathStep::HomogeneousRange { domain });
            collect_sequence_fixed_domain_type_proofs_from_type_expr(
                &range.node,
                invariant,
                var_idx,
                child_path,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                visiting,
                out,
            );
        }
        Expr::Ident(name, _) | Expr::OpRef(name) => {
            collect_sequence_fixed_domain_type_proofs_from_type_alias(
                name,
                invariant,
                var_idx,
                path,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                visiting,
                out,
            );
        }
        _ => {}
    }
}

fn collect_sequence_fixed_domain_type_proofs_from_type_alias(
    name: &str,
    invariant: &str,
    var_idx: usize,
    path: Vec<SequenceCapacityPathStep>,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<SequenceFixedDomainTypeProof>,
) {
    let Some((resolved_name, def)) = layout_safe_op_def(name, op_defs, Some(op_replacements))
    else {
        return;
    };
    if !visiting.insert(resolved_name.to_owned()) {
        return;
    }
    collect_sequence_fixed_domain_type_proofs_from_type_expr(
        &def.body.node,
        invariant,
        var_idx,
        path,
        constants,
        proof_domains,
        op_defs,
        op_replacements,
        visiting,
        out,
    );
    visiting.remove(resolved_name);
}

fn sequence_type_layout_proof_from_type_set_expr(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    visiting: &mut BTreeSet<String>,
) -> Option<SequenceTypeLayoutProof> {
    match expr {
        Expr::Apply(op, args)
            if args.len() == 1 && is_seq_operator(&op.node, Some(op_replacements)) =>
        {
            let element_layout = sequence_type_layout_proof_from_type_set_expr(
                &args[0].node,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                visiting,
            )?;
            Some(SequenceTypeLayoutProof::Sequence {
                element_layout: Box::new(element_layout),
            })
        }
        Expr::FuncSet(domain, range) => {
            let domain = type_domain_values_with_replacements(
                &domain.node,
                constants,
                proof_domains,
                Some(op_replacements),
            )?;
            let element_layout = sequence_type_layout_proof_from_type_set_expr(
                &range.node,
                constants,
                proof_domains,
                op_defs,
                op_replacements,
                visiting,
            )?;
            if domain_is_one_based_int_interval(&domain, 1, domain.len()) {
                Some(SequenceTypeLayoutProof::FixedDomainSequence {
                    max_len: domain.len(),
                    element_layout: Box::new(element_layout),
                })
            } else {
                flat_layout_from_type_set_expr_with_ops(
                    expr,
                    constants,
                    Some(op_defs),
                    Some(op_replacements),
                )
                .map(SequenceTypeLayoutProof::Flat)
            }
        }
        Expr::Ident(name, _) | Expr::OpRef(name) => sequence_type_layout_proof_from_type_alias(
            name,
            constants,
            proof_domains,
            op_defs,
            op_replacements,
            visiting,
        )
        .or_else(|| {
            flat_layout_from_type_set_expr_with_ops(
                expr,
                constants,
                Some(op_defs),
                Some(op_replacements),
            )
            .map(SequenceTypeLayoutProof::Flat)
        }),
        _ => flat_layout_from_type_set_expr_with_ops(
            expr,
            constants,
            Some(op_defs),
            Some(op_replacements),
        )
        .map(SequenceTypeLayoutProof::Flat),
    }
}

fn sequence_type_layout_proof_from_type_alias(
    name: &str,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_defs: &tla_core::OpEnv,
    op_replacements: &tla_core::kani_types::HashMap<String, String>,
    visiting: &mut BTreeSet<String>,
) -> Option<SequenceTypeLayoutProof> {
    let (resolved_name, def) = layout_safe_op_def(name, op_defs, Some(op_replacements))?;
    if !def.params.is_empty() {
        return None;
    }
    if !visiting.insert(resolved_name.to_owned()) {
        return None;
    }
    let result = sequence_type_layout_proof_from_type_set_expr(
        &def.body.node,
        constants,
        proof_domains,
        op_defs,
        op_replacements,
        visiting,
    );
    visiting.remove(resolved_name);
    result
}

fn sequence_type_layout_proof_apply_flat_layout(
    proof: &SequenceTypeLayoutProof,
    observed: &FlatValueLayout,
) -> Option<FlatValueLayout> {
    match proof {
        SequenceTypeLayoutProof::Flat(proven) => {
            flat_layout_proof_apply_flat_layout(proven, observed)
        }
        SequenceTypeLayoutProof::Sequence { element_layout } => {
            let FlatValueLayout::Sequence {
                bound,
                max_len,
                element_layout: observed_element,
            } = observed
            else {
                return None;
            };
            let element_layout =
                sequence_type_layout_proof_apply_flat_layout(element_layout, observed_element)?;
            Some(FlatValueLayout::Sequence {
                bound: bound.clone(),
                max_len: *max_len,
                element_layout: Box::new(element_layout),
            })
        }
        SequenceTypeLayoutProof::FixedDomainSequence {
            max_len,
            element_layout,
        } => {
            let FlatValueLayout::Sequence {
                bound,
                max_len: observed_max_len,
                element_layout: observed_element,
            } = observed
            else {
                return None;
            };
            if max_len != observed_max_len {
                return None;
            }
            let element_layout =
                sequence_type_layout_proof_apply_flat_layout(element_layout, observed_element)?;
            Some(FlatValueLayout::Sequence {
                bound: bound.clone(),
                max_len: *observed_max_len,
                element_layout: Box::new(element_layout),
            })
        }
    }
}

fn flat_function_layout(
    domain: Vec<FlatScalarValue>,
    value_layout: FlatValueLayout,
) -> FlatValueLayout {
    if let Some((lo, len)) = ordered_dense_int_domain(&domain) {
        FlatValueLayout::IntFunction {
            lo,
            len,
            value_layout: Box::new(value_layout),
        }
    } else {
        FlatValueLayout::Function {
            domain,
            value_layout: Box::new(value_layout),
        }
    }
}

fn flat_layout_proof_apply_flat_layout(
    proven: &FlatValueLayout,
    observed: &FlatValueLayout,
) -> Option<FlatValueLayout> {
    match (proven, observed) {
        (FlatValueLayout::Scalar(proven), FlatValueLayout::Scalar(observed))
            if proven == observed =>
        {
            Some(FlatValueLayout::Scalar(*proven))
        }
        (
            FlatValueLayout::SetBitmask {
                universe: proven_universe,
            },
            FlatValueLayout::SetBitmask {
                universe: observed_universe,
            },
        ) if observed_universe
            .iter()
            .all(|value| proven_universe.contains(value)) =>
        {
            Some(FlatValueLayout::SetBitmask {
                universe: proven_universe.clone(),
            })
        }
        (
            FlatValueLayout::Record {
                field_names: proven_names,
                field_layouts: proven_fields,
            },
            FlatValueLayout::Record {
                field_names: observed_names,
                field_layouts: observed_fields,
            },
        ) if proven_names == observed_names && proven_fields.len() == observed_fields.len() => {
            let mut field_layouts = Vec::with_capacity(proven_fields.len());
            for (proven_field, observed_field) in proven_fields.iter().zip(observed_fields.iter()) {
                field_layouts.push(flat_layout_proof_apply_flat_layout(
                    proven_field,
                    observed_field,
                )?);
            }
            Some(FlatValueLayout::Record {
                field_names: proven_names.clone(),
                field_layouts,
            })
        }
        (
            FlatValueLayout::IntFunction {
                lo: proven_lo,
                len: proven_len,
                value_layout: proven_value,
            },
            FlatValueLayout::IntFunction {
                lo: observed_lo,
                len: observed_len,
                value_layout: observed_value,
            },
        ) if proven_lo == observed_lo && proven_len == observed_len => {
            let value_layout = flat_layout_proof_apply_flat_layout(proven_value, observed_value)?;
            Some(FlatValueLayout::IntFunction {
                lo: *proven_lo,
                len: *proven_len,
                value_layout: Box::new(value_layout),
            })
        }
        (
            FlatValueLayout::IntFunction {
                lo: proven_lo,
                len: proven_len,
                value_layout: proven_value,
            },
            FlatValueLayout::Function {
                domain: observed_domain,
                value_layout: observed_value,
            },
        ) if ordered_dense_int_domain(observed_domain) == Some((*proven_lo, *proven_len)) => {
            let value_layout = flat_layout_proof_apply_flat_layout(proven_value, observed_value)?;
            Some(FlatValueLayout::IntFunction {
                lo: *proven_lo,
                len: *proven_len,
                value_layout: Box::new(value_layout),
            })
        }
        (
            FlatValueLayout::Function {
                domain: proven_domain,
                value_layout: proven_value,
            },
            FlatValueLayout::IntFunction {
                lo: observed_lo,
                len: observed_len,
                value_layout: observed_value,
            },
        ) if ordered_dense_int_domain(proven_domain) == Some((*observed_lo, *observed_len)) => {
            let value_layout = flat_layout_proof_apply_flat_layout(proven_value, observed_value)?;
            Some(FlatValueLayout::IntFunction {
                lo: *observed_lo,
                len: *observed_len,
                value_layout: Box::new(value_layout),
            })
        }
        (
            FlatValueLayout::IntFunction {
                lo,
                len,
                value_layout: proven_value,
            },
            FlatValueLayout::Sequence {
                bound,
                max_len,
                element_layout: observed_element,
            },
        ) if *lo == 1 && len == max_len => {
            let element_layout =
                flat_layout_proof_apply_flat_layout(proven_value, observed_element)?;
            Some(FlatValueLayout::Sequence {
                bound: bound.clone(),
                max_len: *max_len,
                element_layout: Box::new(element_layout),
            })
        }
        (
            FlatValueLayout::Function {
                domain: proven_domain,
                value_layout: proven_value,
            },
            FlatValueLayout::Function {
                domain: observed_domain,
                value_layout: observed_value,
            },
        ) if proven_domain == observed_domain => {
            let value_layout = flat_layout_proof_apply_flat_layout(proven_value, observed_value)?;
            Some(flat_function_layout(proven_domain.clone(), value_layout))
        }
        (
            FlatValueLayout::Sequence {
                bound,
                max_len: proven_max_len,
                element_layout: proven_element,
            },
            FlatValueLayout::Sequence {
                max_len: observed_max_len,
                element_layout: observed_element,
                ..
            },
        ) if observed_max_len <= proven_max_len => {
            let element_layout =
                flat_layout_proof_apply_flat_layout(proven_element, observed_element)?;
            Some(FlatValueLayout::Sequence {
                bound: bound.clone(),
                max_len: *proven_max_len,
                element_layout: Box::new(element_layout),
            })
        }
        _ => None,
    }
}

fn push_sequence_fixed_domain_type_proof(
    out: &mut Vec<SequenceFixedDomainTypeProof>,
    proof: SequenceFixedDomainTypeProof,
) {
    if !out.iter().any(|existing| existing == &proof) {
        out.push(proof);
    }
}

#[derive(Default)]
struct ElementProofScope {
    bindings: BTreeMap<String, Vec<Option<Arc<[Value]>>>>,
}

impl ElementProofScope {
    fn push(&mut self, name: String, homogeneous_domain: Option<Arc<[Value]>>) {
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

    fn homogeneous_bound_domain(&self, name: &str) -> Option<Arc<[Value]>> {
        self.bindings
            .get(name)
            .and_then(|stack| stack.last())
            .and_then(|domain| domain.as_ref().map(Arc::clone))
    }
}

fn push_element_bounded_quantifier_names(
    vars: &[BoundVar],
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    scope: &mut ElementProofScope,
) -> Option<Vec<String>> {
    let mut added = Vec::new();
    for var in vars {
        let homogeneous_domain = element_bound_var_domain(var, proof_domains, scope);
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

fn element_bound_var_domain(
    var: &BoundVar,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    scope: &ElementProofScope,
) -> Option<Arc<[Value]>> {
    var.domain.as_ref().and_then(|domain| {
        element_full_homogeneous_domain_values(&domain.node, proof_domains, scope)
    })
}

fn element_full_homogeneous_domain_values(
    expr: &Expr,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    scope: &ElementProofScope,
) -> Option<Arc<[Value]>> {
    match expr {
        Expr::Ident(name, _) if !scope.is_bound(name) => proof_domains.get(name).cloned(),
        _ => None,
    }
}

fn extract_type_state_path(
    expr: &Expr,
    registry: &VarRegistry,
    scope: &ElementProofScope,
    used_bindings: &mut BTreeSet<String>,
) -> Option<(usize, Vec<SequenceCapacityPathStep>)> {
    match expr {
        Expr::StateVar(_, idx, _) => Some((*idx as usize, Vec::new())),
        Expr::Ident(name, _) if !scope.is_bound(name) => {
            registry.get(name).map(|idx| (idx.0 as usize, Vec::new()))
        }
        Expr::FuncApply(func, arg) => {
            let (binding, domain) = element_bound_subscript_arg(&arg.node, scope)?;
            if !used_bindings.insert(binding) {
                return None;
            }
            let (var_idx, mut path) =
                extract_type_state_path(&func.node, registry, scope, used_bindings)?;
            path.push(SequenceCapacityPathStep::HomogeneousRange { domain });
            Some((var_idx, path))
        }
        Expr::RecordAccess(base, field) => {
            let (var_idx, mut path) =
                extract_type_state_path(&base.node, registry, scope, used_bindings)?;
            path.push(SequenceCapacityPathStep::RecordField(Arc::from(
                field.name.node.as_str(),
            )));
            Some((var_idx, path))
        }
        _ => None,
    }
}

fn element_bound_subscript_arg(
    expr: &Expr,
    scope: &ElementProofScope,
) -> Option<(String, Arc<[Value]>)> {
    match expr {
        Expr::Ident(name, _) => Some((name.clone(), scope.homogeneous_bound_domain(name)?)),
        _ => None,
    }
}

fn type_domain_values_with_replacements(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    proof_domains: &BTreeMap<String, Arc<[Value]>>,
    op_replacements: Option<&OpReplacements>,
) -> Option<Arc<[Value]>> {
    match expr {
        Expr::Ident(name, _) => {
            let resolved = resolve_layout_op_name(name, op_replacements)?;
            proof_domains
                .get(resolved)
                .cloned()
                .or_else(|| {
                    (!is_replaced_layout_name(name, op_replacements))
                        .then(|| proof_domains.get(name).cloned())
                        .flatten()
                })
                .or_else(|| {
                    const_expr_to_value_with_replacements(expr, constants, op_replacements)
                        .and_then(|value| {
                            value
                                .to_sorted_set()
                                .map(|set| Arc::from(set.iter().cloned().collect::<Vec<_>>()))
                        })
                })
        }
        Expr::Range(left, right) => {
            let lo = const_expr_to_value_with_replacements(&left.node, constants, op_replacements)?;
            let hi =
                const_expr_to_value_with_replacements(&right.node, constants, op_replacements)?;
            let (Some(FlatScalarValue::Int(lo)), Some(FlatScalarValue::Int(hi))) =
                (flat_scalar_from_value(&lo), flat_scalar_from_value(&hi))
            else {
                return None;
            };
            (lo <= hi).then(|| Arc::from((lo..=hi).map(Value::SmallInt).collect::<Vec<_>>()))
        }
        Expr::SetEnum(elems) => {
            let mut values = Vec::with_capacity(elems.len());
            for elem in elems {
                values.push(const_expr_to_value_with_replacements(
                    &elem.node,
                    constants,
                    op_replacements,
                )?);
            }
            values.sort();
            values.dedup();
            Some(Arc::from(values))
        }
        _ => None,
    }
}

fn is_seq_operator(expr: &Expr, op_replacements: Option<&OpReplacements>) -> bool {
    matches!(
        expr,
        Expr::Ident(name, _) | Expr::OpRef(name)
            if matches!(resolve_layout_op_name(name, op_replacements), Some("Seq"))
    )
}

fn flat_layout_from_type_set_expr(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
) -> Option<FlatValueLayout> {
    if let Some(value) = precomputed_constant_value(expr, constants) {
        if let Some(layout) = flat_layout_from_type_value(value) {
            return Some(layout);
        }
    }

    match expr {
        Expr::Ident(name, _) if name == "Nat" || name == "Int" => {
            Some(FlatValueLayout::Scalar(SlotType::Int))
        }
        Expr::Ident(name, _) if name == "BOOLEAN" => Some(FlatValueLayout::Scalar(SlotType::Bool)),
        Expr::Ident(name, _) if name == "STRING" => Some(FlatValueLayout::Scalar(SlotType::String)),
        Expr::Range(_, _) => Some(FlatValueLayout::Scalar(SlotType::Int)),
        Expr::SetEnum(elems) => {
            let values: Option<Vec<Value>> = elems
                .iter()
                .map(|elem| const_expr_to_value(&elem.node, constants))
                .collect();
            flat_layout_from_type_values(values?.iter())
        }
        Expr::Powerset(base) => {
            let universe = scalar_domain_from_type_set_expr(&base.node, constants)?;
            Some(FlatValueLayout::SetBitmask { universe })
        }
        Expr::RecordSet(fields) => {
            let mut field_pairs: Vec<(NameId, Arc<str>, FlatValueLayout)> =
                Vec::with_capacity(fields.len());
            for (name, field_set) in fields {
                let field_name = Arc::from(name.node.as_str());
                let layout = flat_layout_from_type_set_expr(&field_set.node, constants)?;
                field_pairs.push((intern_name(&field_name), field_name, layout));
            }
            field_pairs.sort_by_key(|(name_id, _, _)| *name_id);
            Some(FlatValueLayout::Record {
                field_names: field_pairs
                    .iter()
                    .map(|(_, name, _)| Arc::clone(name))
                    .collect(),
                field_layouts: field_pairs
                    .into_iter()
                    .map(|(_, _, layout)| layout)
                    .collect(),
            })
        }
        Expr::FuncSet(domain, range) => {
            let domain = scalar_domain_from_type_set_expr(&domain.node, constants)?;
            let value_layout = flat_layout_from_type_set_expr(&range.node, constants)?;
            contiguous_int_flat_domain(&domain)
                .map(|(lo, len)| FlatValueLayout::IntFunction {
                    lo,
                    len,
                    value_layout: Box::new(value_layout.clone()),
                })
                .or_else(|| {
                    Some(FlatValueLayout::Function {
                        domain,
                        value_layout: Box::new(value_layout),
                    })
                })
        }
        _ => None,
    }
}

type LayoutScope = BTreeMap<String, FlatValueLayout>;
type OpReplacements = tla_core::kani_types::HashMap<String, String>;

fn flat_layout_from_type_set_expr_with_ops(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    op_defs: Option<&tla_core::OpEnv>,
    op_replacements: Option<&OpReplacements>,
) -> Option<FlatValueLayout> {
    let Some(op_defs) = op_defs else {
        return flat_layout_from_type_set_expr(expr, constants);
    };
    flat_layout_from_type_set_expr_scoped(
        expr,
        constants,
        op_defs,
        op_replacements,
        &LayoutScope::new(),
        &mut BTreeSet::new(),
    )
}

fn flat_layout_from_type_set_expr_scoped(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    op_defs: &tla_core::OpEnv,
    op_replacements: Option<&OpReplacements>,
    scope: &LayoutScope,
    visiting: &mut BTreeSet<String>,
) -> Option<FlatValueLayout> {
    if let Some(value) =
        precomputed_constant_value_with_replacements(expr, constants, op_replacements)
    {
        if let Some(layout) = flat_layout_from_type_value(value) {
            return Some(layout);
        }
    }

    match expr {
        Expr::Ident(name, _)
            if !is_replaced_layout_name(name, op_replacements)
                && (name == "Nat" || name == "Int") =>
        {
            Some(FlatValueLayout::Scalar(SlotType::Int))
        }
        Expr::Ident(name, _)
            if !is_replaced_layout_name(name, op_replacements) && name == "BOOLEAN" =>
        {
            Some(FlatValueLayout::Scalar(SlotType::Bool))
        }
        Expr::Ident(name, _)
            if !is_replaced_layout_name(name, op_replacements) && name == "STRING" =>
        {
            Some(FlatValueLayout::Scalar(SlotType::String))
        }
        Expr::Ident(name, _) => {
            infer_zero_arg_type_layout(name, constants, op_defs, op_replacements, scope, visiting)
        }
        Expr::Range(_, _) => Some(FlatValueLayout::Scalar(SlotType::Int)),
        Expr::Union(left, right) => {
            let left_layout = flat_layout_from_type_set_expr_scoped(
                &left.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            let right_layout = flat_layout_from_type_set_expr_scoped(
                &right.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            merge_flat_value_layouts(&left_layout, &right_layout)
        }
        Expr::SetMinus(left, _) => flat_layout_from_type_set_expr_scoped(
            &left.node,
            constants,
            op_defs,
            op_replacements,
            scope,
            visiting,
        ),
        Expr::SetEnum(elems) => {
            let values: Option<Vec<Value>> = elems
                .iter()
                .map(|elem| {
                    const_expr_to_value_with_replacements(&elem.node, constants, op_replacements)
                })
                .collect();
            if let Some(values) = values {
                return flat_layout_from_type_values(values.iter());
            }

            let mut iter = elems.iter();
            let first = iter.next()?;
            let mut layout = flat_layout_from_value_expr_scoped(
                &first.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            for elem in iter {
                let next = flat_layout_from_value_expr_scoped(
                    &elem.node,
                    constants,
                    op_defs,
                    op_replacements,
                    scope,
                    visiting,
                )?;
                layout = merge_flat_value_layouts(&layout, &next)?;
            }
            Some(layout)
        }
        Expr::SetBuilder(body, bounds) => {
            let mut child_scope = scope.clone();
            for bound in bounds {
                let domain = bound.domain.as_ref()?;
                let layout = flat_layout_from_type_set_expr_scoped(
                    &domain.node,
                    constants,
                    op_defs,
                    op_replacements,
                    scope,
                    visiting,
                )?;
                bind_bound_layout(bound, layout, &mut child_scope)?;
            }
            flat_layout_from_value_expr_scoped(
                &body.node,
                constants,
                op_defs,
                op_replacements,
                &child_scope,
                visiting,
            )
        }
        Expr::Powerset(base) => {
            let universe = scalar_domain_from_type_set_expr_scoped(
                &base.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            Some(FlatValueLayout::SetBitmask { universe })
        }
        Expr::RecordSet(fields) => {
            let mut field_pairs: Vec<(NameId, Arc<str>, FlatValueLayout)> =
                Vec::with_capacity(fields.len());
            for (name, field_set) in fields {
                let field_name = Arc::from(name.node.as_str());
                let layout = flat_layout_from_type_set_expr_scoped(
                    &field_set.node,
                    constants,
                    op_defs,
                    op_replacements,
                    scope,
                    visiting,
                )?;
                field_pairs.push((intern_name(&field_name), field_name, layout));
            }
            field_pairs.sort_by_key(|(name_id, _, _)| *name_id);
            Some(FlatValueLayout::Record {
                field_names: field_pairs
                    .iter()
                    .map(|(_, name, _)| Arc::clone(name))
                    .collect(),
                field_layouts: field_pairs
                    .into_iter()
                    .map(|(_, _, layout)| layout)
                    .collect(),
            })
        }
        Expr::FuncSet(domain, range) => {
            let domain = scalar_domain_from_type_set_expr_scoped(
                &domain.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            let value_layout = flat_layout_from_type_set_expr_scoped(
                &range.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            contiguous_int_flat_domain(&domain)
                .map(|(lo, len)| FlatValueLayout::IntFunction {
                    lo,
                    len,
                    value_layout: Box::new(value_layout.clone()),
                })
                .or_else(|| {
                    Some(FlatValueLayout::Function {
                        domain,
                        value_layout: Box::new(value_layout),
                    })
                })
        }
        _ => None,
    }
}

fn flat_layout_from_value_expr_scoped(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    op_defs: &tla_core::OpEnv,
    op_replacements: Option<&OpReplacements>,
    scope: &LayoutScope,
    visiting: &mut BTreeSet<String>,
) -> Option<FlatValueLayout> {
    if let Some(value) =
        precomputed_constant_value_with_replacements(expr, constants, op_replacements)
    {
        if let Some(layout) = infer_fixed_value_layout(
            value,
            &LayoutInferenceContext::default(),
            &SequencePath::root(usize::MAX),
        ) {
            return Some(layout);
        }
    }

    match expr {
        Expr::Bool(_) => Some(FlatValueLayout::Scalar(SlotType::Bool)),
        Expr::Int(_) => Some(FlatValueLayout::Scalar(SlotType::Int)),
        Expr::String(_) => Some(FlatValueLayout::Scalar(SlotType::String)),
        Expr::Ident(name, _) => scope.get(name).cloned().or_else(|| {
            infer_zero_arg_value_layout(name, constants, op_defs, op_replacements, scope, visiting)
        }),
        Expr::Record(fields) => {
            let mut field_pairs: Vec<(NameId, Arc<str>, FlatValueLayout)> =
                Vec::with_capacity(fields.len());
            for (name, value_expr) in fields {
                let field_name = Arc::from(name.node.as_str());
                let layout = flat_layout_from_value_expr_scoped(
                    &value_expr.node,
                    constants,
                    op_defs,
                    op_replacements,
                    scope,
                    visiting,
                )?;
                field_pairs.push((intern_name(&field_name), field_name, layout));
            }
            field_pairs.sort_by_key(|(name_id, _, _)| *name_id);
            Some(FlatValueLayout::Record {
                field_names: field_pairs
                    .iter()
                    .map(|(_, name, _)| Arc::clone(name))
                    .collect(),
                field_layouts: field_pairs
                    .into_iter()
                    .map(|(_, _, layout)| layout)
                    .collect(),
            })
        }
        Expr::Apply(op, args) => {
            let name = operator_ident_name(&op.node)?;
            let (resolved_name, def) = layout_safe_op_def(name, op_defs, op_replacements)?;
            if def.params.len() != args.len() || visiting.contains(resolved_name) {
                return None;
            }
            let mut child_scope = scope.clone();
            for (param, arg) in def.params.iter().zip(args.iter()) {
                if param.arity != 0 {
                    return None;
                }
                let layout = flat_layout_from_value_expr_scoped(
                    &arg.node,
                    constants,
                    op_defs,
                    op_replacements,
                    scope,
                    visiting,
                )
                .or_else(|| {
                    flat_layout_from_type_set_expr_scoped(
                        &arg.node,
                        constants,
                        op_defs,
                        op_replacements,
                        scope,
                        visiting,
                    )
                })?;
                child_scope.insert(param.name.node.clone(), layout);
            }
            visiting.insert(resolved_name.to_owned());
            let result = flat_layout_from_value_expr_scoped(
                &def.body.node,
                constants,
                op_defs,
                op_replacements,
                &child_scope,
                visiting,
            );
            visiting.remove(resolved_name);
            result
        }
        Expr::If(_, then_expr, else_expr) => {
            let then_layout = flat_layout_from_value_expr_scoped(
                &then_expr.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            let else_layout = flat_layout_from_value_expr_scoped(
                &else_expr.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            merge_flat_value_layouts(&then_layout, &else_layout)
        }
        Expr::SetEnum(_) | Expr::SetBuilder(_, _) | Expr::Powerset(_) => {
            flat_layout_from_type_set_expr_scoped(
                expr,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )
        }
        _ => None,
    }
}

fn infer_zero_arg_type_layout(
    name: &str,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    op_defs: &tla_core::OpEnv,
    op_replacements: Option<&OpReplacements>,
    scope: &LayoutScope,
    visiting: &mut BTreeSet<String>,
) -> Option<FlatValueLayout> {
    let (resolved_name, def) = layout_safe_op_def(name, op_defs, op_replacements)?;
    if !def.params.is_empty() || visiting.contains(resolved_name) {
        return None;
    }
    visiting.insert(resolved_name.to_owned());
    let result = flat_layout_from_type_set_expr_scoped(
        &def.body.node,
        constants,
        op_defs,
        op_replacements,
        scope,
        visiting,
    );
    visiting.remove(resolved_name);
    result
}

fn infer_zero_arg_value_layout(
    name: &str,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    op_defs: &tla_core::OpEnv,
    op_replacements: Option<&OpReplacements>,
    scope: &LayoutScope,
    visiting: &mut BTreeSet<String>,
) -> Option<FlatValueLayout> {
    let (resolved_name, def) = layout_safe_op_def(name, op_defs, op_replacements)?;
    if !def.params.is_empty() || visiting.contains(resolved_name) {
        return None;
    }
    visiting.insert(resolved_name.to_owned());
    let result = flat_layout_from_value_expr_scoped(
        &def.body.node,
        constants,
        op_defs,
        op_replacements,
        scope,
        visiting,
    )
    .or_else(|| {
        flat_layout_from_type_set_expr_scoped(
            &def.body.node,
            constants,
            op_defs,
            op_replacements,
            scope,
            visiting,
        )
    });
    visiting.remove(resolved_name);
    result
}

fn scalar_domain_from_type_set_expr_scoped(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    op_defs: &tla_core::OpEnv,
    op_replacements: Option<&OpReplacements>,
    scope: &LayoutScope,
    visiting: &mut BTreeSet<String>,
) -> Option<Vec<FlatScalarValue>> {
    if let Some(value) =
        precomputed_constant_value_with_replacements(expr, constants, op_replacements)
    {
        if let Some(domain) = scalar_domain_from_type_value(value) {
            return Some(domain);
        }
    }

    match expr {
        Expr::Ident(name, _) => {
            let (resolved_name, def) = layout_safe_op_def(name, op_defs, op_replacements)?;
            if !def.params.is_empty() || visiting.contains(resolved_name) {
                return None;
            }
            visiting.insert(resolved_name.to_owned());
            let result = scalar_domain_from_type_set_expr_scoped(
                &def.body.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            );
            visiting.remove(resolved_name);
            result
        }
        Expr::SetEnum(elems) => {
            let mut values = Vec::with_capacity(elems.len());
            for elem in elems {
                values.push(flat_scalar_from_value(
                    &const_expr_to_value_with_replacements(&elem.node, constants, op_replacements)?,
                )?);
            }
            normalize_flat_scalar_domain(values)
        }
        Expr::Range(left, right) => {
            let lo = const_expr_to_value_with_replacements(&left.node, constants, op_replacements)?;
            let hi =
                const_expr_to_value_with_replacements(&right.node, constants, op_replacements)?;
            let (Some(FlatScalarValue::Int(lo)), Some(FlatScalarValue::Int(hi))) =
                (flat_scalar_from_value(&lo), flat_scalar_from_value(&hi))
            else {
                return None;
            };
            if hi < lo || hi - lo >= 63 {
                return None;
            }
            normalize_flat_scalar_domain((lo..=hi).map(FlatScalarValue::Int).collect())
        }
        Expr::SetMinus(left, right) => {
            let mut domain = scalar_domain_from_type_set_expr_scoped(
                &left.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            let remove = scalar_domain_from_type_set_expr_scoped(
                &right.node,
                constants,
                op_defs,
                op_replacements,
                scope,
                visiting,
            )?;
            domain.retain(|value| !remove.contains(value));
            normalize_flat_scalar_domain(domain)
        }
        _ => None,
    }
}

fn bind_bound_layout(
    bound: &tla_core::ast::BoundVar,
    layout: FlatValueLayout,
    scope: &mut LayoutScope,
) -> Option<()> {
    match &bound.pattern {
        Some(BoundPattern::Tuple(_)) => None,
        Some(BoundPattern::Var(var)) => {
            scope.insert(var.node.clone(), layout);
            Some(())
        }
        None => {
            scope.insert(bound.name.node.clone(), layout);
            Some(())
        }
    }
}

fn operator_ident_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Ident(name, _) | Expr::OpRef(name) => Some(name.as_str()),
        _ => None,
    }
}

fn resolve_layout_op_name<'a>(
    name: &'a str,
    op_replacements: Option<&'a OpReplacements>,
) -> Option<&'a str> {
    let Some(op_replacements) = op_replacements else {
        return Some(name);
    };
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

fn is_replaced_layout_name(name: &str, op_replacements: Option<&OpReplacements>) -> bool {
    op_replacements.is_some_and(|op_replacements| op_replacements.contains_key(name))
}

fn layout_safe_op_def<'a>(
    name: &'a str,
    op_defs: &'a tla_core::OpEnv,
    op_replacements: Option<&'a OpReplacements>,
) -> Option<(&'a str, &'a OperatorDef)> {
    let resolved = resolve_layout_op_name(name, op_replacements)?;
    let def = op_defs.get(resolved)?.as_ref();
    (!def.contains_prime
        && !def.has_primed_param
        && !def.is_recursive
        && def.params.iter().all(|param| param.arity == 0))
    .then_some((resolved, def))
}

fn precomputed_constant_value<'a>(
    expr: &Expr,
    constants: &'a tla_core::kani_types::HashMap<NameId, Value>,
) -> Option<&'a Value> {
    let Expr::Ident(name, name_id) = expr else {
        return None;
    };
    let id = if *name_id == NameId::INVALID {
        intern_name(name)
    } else {
        *name_id
    };
    constants.get(&id)
}

fn precomputed_constant_value_with_replacements<'a>(
    expr: &Expr,
    constants: &'a tla_core::kani_types::HashMap<NameId, Value>,
    op_replacements: Option<&OpReplacements>,
) -> Option<&'a Value> {
    let Expr::Ident(name, name_id) = expr else {
        return None;
    };
    let resolved = resolve_layout_op_name(name, op_replacements)?;
    if resolved != name {
        if let Some(value) = constants.get(&intern_name(resolved)) {
            return Some(value);
        }
        return None;
    }
    let id = if *name_id == NameId::INVALID {
        intern_name(name)
    } else {
        *name_id
    };
    constants.get(&id)
}

fn const_expr_to_value(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
) -> Option<Value> {
    match expr {
        Expr::Bool(value) => Some(Value::Bool(*value)),
        Expr::Int(value) => {
            use num_traits::ToPrimitive;

            value
                .to_i64()
                .map(Value::SmallInt)
                .or_else(|| Some(Value::Int(Arc::new(value.clone()))))
        }
        Expr::String(value) => Some(Value::String(Arc::from(value.as_str()))),
        Expr::Ident(_, _) => precomputed_constant_value(expr, constants).cloned(),
        Expr::Record(fields) => {
            let mut entries = Vec::with_capacity(fields.len());
            for (name, value_expr) in fields {
                entries.push((
                    Arc::from(name.node.as_str()),
                    const_expr_to_value(&value_expr.node, constants)?,
                ));
            }
            Some(Value::Record(
                tla_value::value::RecordValue::from_sorted_str_entries(entries),
            ))
        }
        _ => None,
    }
}

fn const_expr_to_value_with_replacements(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
    op_replacements: Option<&OpReplacements>,
) -> Option<Value> {
    match expr {
        Expr::Ident(name, name_id) => {
            let resolved = resolve_layout_op_name(name, op_replacements)?;
            let resolved_id = intern_name(resolved);
            if resolved != name {
                return constants.get(&resolved_id).cloned();
            }
            let id = if *name_id == NameId::INVALID {
                intern_name(name)
            } else {
                *name_id
            };
            constants.get(&id).cloned()
        }
        Expr::Record(fields) => {
            let mut entries = Vec::with_capacity(fields.len());
            for (name, value_expr) in fields {
                entries.push((
                    Arc::from(name.node.as_str()),
                    const_expr_to_value_with_replacements(
                        &value_expr.node,
                        constants,
                        op_replacements,
                    )?,
                ));
            }
            Some(Value::Record(
                tla_value::value::RecordValue::from_sorted_str_entries(entries),
            ))
        }
        _ => const_expr_to_value(expr, constants),
    }
}

fn flat_layout_from_type_value(value: &Value) -> Option<FlatValueLayout> {
    match value {
        Value::StringSet => Some(FlatValueLayout::Scalar(SlotType::String)),
        Value::Interval(_) => Some(FlatValueLayout::Scalar(SlotType::Int)),
        Value::Set(set) => flat_layout_from_type_values(set.iter()),
        Value::Subset(subset) => {
            let universe = scalar_domain_from_type_value(subset.base())?;
            Some(FlatValueLayout::SetBitmask { universe })
        }
        Value::FuncSet(func_set) => {
            let domain = scalar_domain_from_type_value(func_set.domain())?;
            let value_layout = flat_layout_from_type_value(func_set.codomain())?;
            contiguous_int_flat_domain(&domain)
                .map(|(lo, len)| FlatValueLayout::IntFunction {
                    lo,
                    len,
                    value_layout: Box::new(value_layout.clone()),
                })
                .or_else(|| {
                    Some(FlatValueLayout::Function {
                        domain,
                        value_layout: Box::new(value_layout),
                    })
                })
        }
        _ => value
            .to_sorted_set()
            .and_then(|set| flat_layout_from_type_values(set.iter())),
    }
}

fn flat_layout_from_type_values<'a, I>(values: I) -> Option<FlatValueLayout>
where
    I: IntoIterator<Item = &'a Value>,
{
    infer_common_flat_layout(
        values,
        &LayoutInferenceContext::default(),
        &SequencePath::root(usize::MAX),
    )
}

fn scalar_domain_from_type_set_expr(
    expr: &Expr,
    constants: &tla_core::kani_types::HashMap<NameId, Value>,
) -> Option<Vec<FlatScalarValue>> {
    if let Some(value) = precomputed_constant_value(expr, constants) {
        return scalar_domain_from_type_value(value);
    }

    match expr {
        Expr::SetEnum(elems) => {
            let mut values = Vec::with_capacity(elems.len());
            for elem in elems {
                values.push(flat_scalar_from_value(&const_expr_to_value(
                    &elem.node, constants,
                )?)?);
            }
            normalize_flat_scalar_domain(values)
        }
        Expr::Range(left, right) => {
            let lo = const_expr_to_value(&left.node, constants)?;
            let hi = const_expr_to_value(&right.node, constants)?;
            let (Some(FlatScalarValue::Int(lo)), Some(FlatScalarValue::Int(hi))) =
                (flat_scalar_from_value(&lo), flat_scalar_from_value(&hi))
            else {
                return None;
            };
            if hi < lo || hi - lo >= 63 {
                return None;
            }
            normalize_flat_scalar_domain((lo..=hi).map(FlatScalarValue::Int).collect())
        }
        _ => None,
    }
}

fn scalar_domain_from_type_value(value: &Value) -> Option<Vec<FlatScalarValue>> {
    use num_traits::ToPrimitive;

    if value.set_len()?.to_usize()? > 63 {
        return None;
    }
    let set = value.to_sorted_set()?;
    let values: Option<Vec<FlatScalarValue>> = set.iter().map(flat_scalar_from_value).collect();
    normalize_flat_scalar_domain(values?)
}

fn normalize_flat_scalar_domain(mut values: Vec<FlatScalarValue>) -> Option<Vec<FlatScalarValue>> {
    values.sort();
    values.dedup();
    (!values.is_empty() && values.len() <= 63).then_some(values)
}

fn contiguous_int_flat_domain(domain: &[FlatScalarValue]) -> Option<(i64, usize)> {
    ordered_dense_int_domain(domain)
}

fn collect_scalar_domain_candidates(value: &Value, out: &mut Vec<Vec<FlatScalarValue>>) {
    match value {
        Value::IntFunc(func) => {
            if !func.is_empty() && func.len() <= 63 {
                let domain: Vec<FlatScalarValue> = (0..func.len())
                    .map(|i| FlatScalarValue::Int(func.as_ref().min() + i as i64))
                    .collect();
                push_unique_domain_candidate(out, domain);
            }
            for value in func.values() {
                collect_scalar_domain_candidates(value, out);
            }
        }
        Value::Func(func) => {
            if !func.domain_is_empty() && func.domain_len() <= 63 {
                let mut domain = Vec::with_capacity(func.domain_len());
                let mut all_scalar = true;
                for key in func.domain_iter() {
                    if let Some(key) = flat_scalar_from_value(key) {
                        domain.push(key);
                    } else {
                        all_scalar = false;
                        break;
                    }
                }
                if all_scalar {
                    push_unique_domain_candidate(out, domain);
                }
            }
            for (_, value) in func.iter() {
                collect_scalar_domain_candidates(value, out);
            }
        }
        Value::Record(record) => {
            for (_, value) in record.iter() {
                collect_scalar_domain_candidates(value, out);
            }
        }
        Value::Set(set) => {
            for value in set.iter() {
                collect_scalar_domain_candidates(value, out);
            }
        }
        Value::Seq(seq) => {
            if !seq.is_empty() && seq.len() <= 63 {
                let domain: Vec<FlatScalarValue> = (1..=seq.len())
                    .map(|i| FlatScalarValue::Int(i as i64))
                    .collect();
                push_unique_domain_candidate(out, domain);
            }
            for value in seq.iter() {
                collect_scalar_domain_candidates(value, out);
            }
        }
        Value::Tuple(elems) => {
            if !elems.is_empty() && elems.len() <= 63 {
                let domain: Vec<FlatScalarValue> = (1..=elems.len())
                    .map(|i| FlatScalarValue::Int(i as i64))
                    .collect();
                push_unique_domain_candidate(out, domain);
            }
            for value in elems.iter() {
                collect_scalar_domain_candidates(value, out);
            }
        }
        _ => {}
    }
}

fn push_unique_domain_candidate(
    out: &mut Vec<Vec<FlatScalarValue>>,
    mut domain: Vec<FlatScalarValue>,
) {
    domain.sort();
    domain.dedup();
    if !domain.is_empty() && !out.iter().any(|existing| *existing == domain) {
        out.push(domain);
    }
}

fn collect_sequence_hints(
    value: &Value,
    context: &LayoutInferenceContext,
    out: &mut Vec<SequenceHint>,
    path: &SequencePath,
) {
    match value {
        Value::Seq(seq) => {
            if !seq.is_empty() {
                let element_path = path.child(SequencePathStep::SequenceElement);
                if let Some(element_layout) =
                    infer_common_flat_layout(seq.iter(), context, &element_path)
                {
                    push_sequence_hint(
                        out,
                        SequenceHint {
                            path: path.clone(),
                            max_len: seq.len(),
                            element_layout,
                        },
                    );
                }
            }
            let element_path = path.child(SequencePathStep::SequenceElement);
            for value in seq.iter() {
                collect_sequence_hints(value, context, out, &element_path);
            }
        }
        Value::Tuple(elems) => {
            if !elems.is_empty() {
                let element_path = path.child(SequencePathStep::SequenceElement);
                if let Some(element_layout) =
                    infer_common_flat_layout(elems.iter(), context, &element_path)
                {
                    push_sequence_hint(
                        out,
                        SequenceHint {
                            path: path.clone(),
                            max_len: elems.len(),
                            element_layout,
                        },
                    );
                }
            }
            let element_path = path.child(SequencePathStep::SequenceElement);
            for value in elems.iter() {
                collect_sequence_hints(value, context, out, &element_path);
            }
        }
        Value::IntFunc(func) => {
            if func.is_empty() {
                return;
            }
            let value_path = path.child(int_func_domain_path_step(func));
            for value in func.values() {
                collect_sequence_hints(value, context, out, &value_path);
            }
        }
        Value::Func(func) => {
            if let Some(value_path) = func_domain_path_step(func).map(|step| path.child(step)) {
                for (_, value) in func.iter() {
                    collect_sequence_hints(value, context, out, &value_path);
                }
            }
        }
        Value::Record(record) => {
            for (name_id, value) in record.iter() {
                let field_path = path.child(SequencePathStep::RecordField(
                    tla_core::resolve_name_id(name_id),
                ));
                collect_sequence_hints(value, context, out, &field_path);
            }
        }
        Value::Set(set) => {
            let element_path = path.child(SequencePathStep::SetElement);
            for value in set.iter() {
                collect_sequence_hints(value, context, out, &element_path);
            }
        }
        _ => {}
    }
}

fn push_sequence_hint(out: &mut Vec<SequenceHint>, hint: SequenceHint) {
    for existing in out.iter_mut() {
        if existing.path != hint.path {
            continue;
        }
        if let Some(element_layout) =
            merge_flat_value_layouts(&existing.element_layout, &hint.element_layout)
        {
            existing.max_len = existing.max_len.max(hint.max_len);
            existing.element_layout = element_layout;
            return;
        }
    }
    out.push(hint);
}

/// Infer the layout kind for a single variable from its CompactValue.
fn infer_var_kind(cv: &tla_value::CompactValue) -> VarLayoutKind {
    if cv.is_bool() {
        return VarLayoutKind::ScalarBool;
    }
    if cv.is_int() {
        return VarLayoutKind::Scalar;
    }

    // For heap values, convert to Value and inspect the structure.
    if cv.is_heap() {
        let value = Value::from(cv);
        return infer_kind_from_value(&value);
    }

    // String: use ScalarString to preserve type through roundtrip.
    // Part of #3908.
    if cv.is_string() {
        return VarLayoutKind::ScalarString;
    }

    // ModelValue: use ScalarModelValue to preserve type through roundtrip.
    // Part of #3908.
    if cv.is_model_value() {
        return VarLayoutKind::ScalarModelValue;
    }

    VarLayoutKind::Dynamic
}

/// Infer layout kind from a full Value.
fn infer_kind_from_value(value: &Value) -> VarLayoutKind {
    infer_kind_from_value_with_context(
        value,
        &LayoutInferenceContext::default(),
        &SequencePath::root(0),
    )
}

/// Infer layout kind from a full Value using finite-domain context gathered
/// across the sampled states.
fn infer_kind_from_value_with_context(
    value: &Value,
    context: &LayoutInferenceContext,
    path: &SequencePath,
) -> VarLayoutKind {
    match value {
        Value::Bool(_) => VarLayoutKind::ScalarBool,
        Value::SmallInt(_) | Value::Int(_) => VarLayoutKind::Scalar,
        Value::String(_) => VarLayoutKind::ScalarString,
        Value::ModelValue(_) => VarLayoutKind::ScalarModelValue,

        // Integer-indexed function: flatten to IntArray if all values are scalar.
        Value::IntFunc(func) => {
            let f = func.as_ref();
            let all_scalar = f.values().iter().all(is_scalar_value);
            if all_scalar && f.len() > 0 {
                let elements_are_bool = f.values().iter().all(|v| matches!(v, Value::Bool(_)));
                let has_string = f
                    .values()
                    .iter()
                    .any(|v| matches!(v, Value::String(_) | Value::ModelValue(_)));
                let element_types = if has_string || !elements_are_bool {
                    // Track per-element types when there are mixed types.
                    Some(f.values().iter().map(slot_type_from_value).collect())
                } else {
                    None
                };
                VarLayoutKind::IntArray {
                    lo: f.min(),
                    len: f.len(),
                    elements_are_bool,
                    element_types,
                }
            } else if let Some(layout) = infer_fixed_value_layout(value, context, path) {
                VarLayoutKind::Recursive { layout }
            } else if f.len() == 0 {
                // Empty function: treat as scalar (zero slots would be odd).
                VarLayoutKind::Dynamic
            } else {
                VarLayoutKind::Dynamic
            }
        }

        // General function: flatten to IntArray if domain is integer interval
        // and all range values are scalar, or StringKeyedArray if domain is
        // strings/model-values.
        Value::Func(func) => {
            if func.domain_is_empty() {
                return VarLayoutKind::Dynamic;
            }

            // Check if domain is contiguous integers.
            let mut is_int_domain = true;
            let mut is_string_domain = true;
            let mut min_key = i64::MAX;
            let mut max_key = i64::MIN;
            for key in func.domain_iter() {
                match key {
                    Value::SmallInt(n) => {
                        is_string_domain = false;
                        min_key = min_key.min(*n);
                        max_key = max_key.max(*n);
                    }
                    Value::String(_) | Value::ModelValue(_) => {
                        is_int_domain = false;
                    }
                    _ => {
                        is_int_domain = false;
                        is_string_domain = false;
                        break;
                    }
                }
            }

            if is_int_domain {
                let expected_len = (max_key - min_key + 1) as usize;
                if expected_len == func.domain_len() {
                    // Contiguous integer domain. Check range values.
                    if let Some(int_array) = try_int_array_from_func(func, min_key, expected_len) {
                        return int_array;
                    }
                }
            }

            // String-keyed function: flatten to StringKeyedArray.
            // Part of #3908: compound type flat state roundtrip.
            if is_string_domain {
                let all_range_scalar = func.iter().all(|(_, v)| is_scalar_value(v));
                if all_range_scalar {
                    let mut domain_keys: Vec<Arc<str>> = Vec::with_capacity(func.domain_len());
                    let mut domain_types: Vec<SlotType> = Vec::with_capacity(func.domain_len());
                    let mut value_types: Vec<SlotType> = Vec::with_capacity(func.domain_len());
                    for (key, val) in func.iter() {
                        let (key_str, key_ty) = match key {
                            Value::String(s) => (Arc::clone(s), SlotType::String),
                            Value::ModelValue(s) => (Arc::clone(s), SlotType::ModelValue),
                            _ => unreachable!("checked is_string_domain above"),
                        };
                        domain_keys.push(key_str);
                        domain_types.push(key_ty);
                        value_types.push(slot_type_from_value(val));
                    }
                    return VarLayoutKind::StringKeyedArray {
                        domain_keys,
                        domain_types,
                        value_types,
                    };
                }
            }

            if let Some(layout) = infer_fixed_value_layout(value, context, path) {
                VarLayoutKind::Recursive { layout }
            } else {
                VarLayoutKind::Dynamic
            }
        }

        // Record: flatten if all fields are scalar.
        Value::Record(rec) => {
            let mut all_scalar = true;
            let mut field_names = Vec::with_capacity(rec.len());
            let mut field_is_bool = Vec::with_capacity(rec.len());
            let mut field_types = Vec::with_capacity(rec.len());

            for (nid, val) in rec.iter() {
                field_names.push(tla_core::resolve_name_id(nid));
                field_is_bool.push(matches!(val, Value::Bool(_)));
                field_types.push(slot_type_from_value(val));
                if !is_scalar_value(val) {
                    all_scalar = false;
                    break;
                }
            }

            if all_scalar && !field_names.is_empty() {
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                    field_types,
                }
            } else if let Some(layout) = infer_fixed_value_layout(value, context, path) {
                VarLayoutKind::Recursive { layout }
            } else {
                VarLayoutKind::Dynamic
            }
        }

        Value::Set(_) | Value::Seq(_) | Value::Tuple(_) => {
            if let Some(layout) = infer_fixed_value_layout(value, context, path) {
                VarLayoutKind::Recursive { layout }
            } else {
                VarLayoutKind::Dynamic
            }
        }

        // Everything else: Dynamic fallback.
        _ => VarLayoutKind::Dynamic,
    }
}

fn infer_fixed_value_layout(
    value: &Value,
    context: &LayoutInferenceContext,
    path: &SequencePath,
) -> Option<FlatValueLayout> {
    match value {
        Value::Bool(_) => Some(FlatValueLayout::Scalar(SlotType::Bool)),
        Value::SmallInt(_) | Value::Int(_) => Some(FlatValueLayout::Scalar(SlotType::Int)),
        Value::String(_) => Some(FlatValueLayout::Scalar(SlotType::String)),
        Value::ModelValue(_) => Some(FlatValueLayout::Scalar(SlotType::ModelValue)),

        Value::IntFunc(func) => {
            if func.is_empty() {
                return None;
            }
            let value_path = path.child(int_func_domain_path_step(func));
            let value_layout =
                infer_common_flat_layout(func.values().iter(), context, &value_path)?;
            Some(FlatValueLayout::IntFunction {
                lo: func.as_ref().min(),
                len: func.len(),
                value_layout: Box::new(value_layout),
            })
        }

        Value::Func(func) => {
            if func.domain_is_empty() {
                return None;
            }
            let value_path = path.child(func_domain_path_step(func)?);
            let value_layout =
                infer_common_flat_layout(func.mapping_values(), context, &value_path)?;
            if let Some((lo, len)) = contiguous_int_domain(func) {
                return Some(FlatValueLayout::IntFunction {
                    lo,
                    len,
                    value_layout: Box::new(value_layout),
                });
            }

            let mut domain = Vec::with_capacity(func.domain_len());
            for key in func.domain_iter() {
                domain.push(flat_scalar_from_value(key)?);
            }
            Some(FlatValueLayout::Function {
                domain,
                value_layout: Box::new(value_layout),
            })
        }

        Value::Record(record) => {
            if record.is_empty() {
                return None;
            }
            let mut field_names = Vec::with_capacity(record.len());
            let mut field_layouts = Vec::with_capacity(record.len());
            for (name_id, field_value) in record.iter() {
                let field_name = tla_core::resolve_name_id(name_id);
                let field_path = path.child(SequencePathStep::RecordField(Arc::clone(&field_name)));
                field_names.push(field_name);
                field_layouts.push(infer_fixed_value_layout(field_value, context, &field_path)?);
            }
            Some(FlatValueLayout::Record {
                field_names,
                field_layouts,
            })
        }

        Value::Set(set) => infer_set_bitmask_layout(set, context),

        Value::Seq(seq) => {
            if seq.is_empty() {
                let proven_element = context.unique_sequence_element_proof(path);
                let (observed_len, element_layout) = if let Some(proof) = proven_element {
                    (0, proof.element_layout.clone())
                } else if let Some(hint) = context.unique_sequence_hint(path) {
                    (hint.max_len, hint.element_layout.clone())
                } else {
                    (0, FlatValueLayout::Scalar(SlotType::Int))
                };
                let (bound, max_len, element_layout) = fixed_domain_sequence_layout_for_path(
                    context,
                    path,
                    observed_len,
                    &element_layout,
                )
                .unwrap_or_else(|| {
                    let (bound, max_len) = sequence_bound_evidence_for_path(
                        context,
                        path,
                        observed_len,
                        proven_element.map(|proof| &proof.invariant),
                    );
                    (bound, max_len, element_layout)
                });
                return Some(FlatValueLayout::Sequence {
                    bound,
                    max_len,
                    element_layout: Box::new(element_layout),
                });
            }
            let element_path = path.child(SequencePathStep::SequenceElement);
            let observed_element_layout =
                infer_common_flat_layout(seq.iter(), context, &element_path)?;
            let proven_element = context.unique_sequence_element_proof(path).filter(|proof| {
                seq.iter()
                    .all(|value| value_fits_flat_value_layout(value, &proof.element_layout))
            });
            let element_layout = proven_element
                .map(|proof| proof.element_layout.clone())
                .unwrap_or(observed_element_layout);
            let (bound, max_len, element_layout) =
                fixed_domain_sequence_layout_for_path(context, path, seq.len(), &element_layout)
                    .unwrap_or_else(|| {
                        let (bound, max_len) = sequence_bound_evidence_for_path(
                            context,
                            path,
                            seq.len(),
                            proven_element.map(|proof| &proof.invariant),
                        );
                        (bound, max_len, element_layout)
                    });
            Some(FlatValueLayout::Sequence {
                bound,
                max_len,
                element_layout: Box::new(element_layout),
            })
        }

        Value::Tuple(elems) => {
            if elems.is_empty() {
                let proven_element = context.unique_sequence_element_proof(path);
                let (observed_len, element_layout) = if let Some(proof) = proven_element {
                    (0, proof.element_layout.clone())
                } else if let Some(hint) = context.unique_sequence_hint(path) {
                    (hint.max_len, hint.element_layout.clone())
                } else {
                    (0, FlatValueLayout::Scalar(SlotType::Int))
                };
                let (bound, max_len, element_layout) = fixed_domain_sequence_layout_for_path(
                    context,
                    path,
                    observed_len,
                    &element_layout,
                )
                .unwrap_or_else(|| {
                    let (bound, max_len) = sequence_bound_evidence_for_path(
                        context,
                        path,
                        observed_len,
                        proven_element.map(|proof| &proof.invariant),
                    );
                    (bound, max_len, element_layout)
                });
                return Some(FlatValueLayout::Sequence {
                    bound,
                    max_len,
                    element_layout: Box::new(element_layout),
                });
            }
            let element_path = path.child(SequencePathStep::SequenceElement);
            let observed_element_layout =
                infer_common_flat_layout(elems.iter(), context, &element_path)?;
            let proven_element = context.unique_sequence_element_proof(path).filter(|proof| {
                elems
                    .iter()
                    .all(|value| value_fits_flat_value_layout(value, &proof.element_layout))
            });
            let element_layout = proven_element
                .map(|proof| proof.element_layout.clone())
                .unwrap_or(observed_element_layout);
            let (bound, max_len, element_layout) =
                fixed_domain_sequence_layout_for_path(context, path, elems.len(), &element_layout)
                    .unwrap_or_else(|| {
                        let (bound, max_len) = sequence_bound_evidence_for_path(
                            context,
                            path,
                            elems.len(),
                            proven_element.map(|proof| &proof.invariant),
                        );
                        (bound, max_len, element_layout)
                    });
            Some(FlatValueLayout::Sequence {
                bound,
                max_len,
                element_layout: Box::new(element_layout),
            })
        }

        _ => None,
    }
}

fn infer_common_flat_layout<'a, I>(
    values: I,
    context: &LayoutInferenceContext,
    path: &SequencePath,
) -> Option<FlatValueLayout>
where
    I: IntoIterator<Item = &'a Value>,
{
    let mut iter = values.into_iter();
    let first = iter.next()?;
    let mut layout = infer_fixed_value_layout(first, context, path)?;
    for value in iter {
        let next = infer_fixed_value_layout(value, context, path)?;
        layout = merge_flat_value_layouts(&layout, &next)?;
    }
    Some(layout)
}

fn infer_set_bitmask_layout(
    set: &tla_value::value::SortedSet,
    context: &LayoutInferenceContext,
) -> Option<FlatValueLayout> {
    let mut elements = Vec::with_capacity(set.len());
    for value in set.iter() {
        elements.push(flat_scalar_from_value(value)?);
    }
    let universe = context.unique_scalar_domain_covering(&elements)?;
    Some(FlatValueLayout::SetBitmask { universe })
}

fn int_func_domain_path_step(func: &tla_value::value::IntIntervalFunc) -> SequencePathStep {
    let domain: Vec<Value> = (func.min()..=func.max()).map(Value::SmallInt).collect();
    SequencePathStep::HomogeneousRange(Arc::from(domain.into_boxed_slice()))
}

fn func_domain_path_step(func: &tla_value::value::FuncValue) -> Option<SequencePathStep> {
    let domain: Vec<Value> = func.domain_iter().cloned().collect();
    normalized_scalar_domain_values(domain)
        .map(|domain| SequencePathStep::HomogeneousRange(Arc::from(domain.into_boxed_slice())))
}

fn normalized_scalar_domain_values(mut values: Vec<Value>) -> Option<Vec<Value>> {
    if values.is_empty() {
        return None;
    }
    if !values.iter().all(is_scalar_value) {
        return None;
    }
    values.sort();
    values.dedup();
    Some(values)
}

fn contiguous_int_domain(func: &tla_value::value::FuncValue) -> Option<(i64, usize)> {
    let mut min_key = i64::MAX;
    let mut max_key = i64::MIN;
    for key in func.domain_iter() {
        match key {
            Value::SmallInt(n) => {
                min_key = min_key.min(*n);
                max_key = max_key.max(*n);
            }
            _ => return None,
        }
    }
    let len = (max_key - min_key + 1) as usize;
    (len == func.domain_len()).then_some((min_key, len))
}

fn merge_flat_value_layouts(a: &FlatValueLayout, b: &FlatValueLayout) -> Option<FlatValueLayout> {
    match (a, b) {
        (FlatValueLayout::Scalar(a), FlatValueLayout::Scalar(b)) if a == b => {
            Some(FlatValueLayout::Scalar(*a))
        }
        (
            FlatValueLayout::IntFunction {
                lo: lo_a,
                len: len_a,
                value_layout: value_a,
            },
            FlatValueLayout::IntFunction {
                lo: lo_b,
                len: len_b,
                value_layout: value_b,
            },
        ) if lo_a == lo_b && len_a == len_b => {
            let value_layout = merge_flat_value_layouts(value_a, value_b)?;
            Some(FlatValueLayout::IntFunction {
                lo: *lo_a,
                len: *len_a,
                value_layout: Box::new(value_layout),
            })
        }
        (
            FlatValueLayout::IntFunction {
                lo: lo_a,
                len: len_a,
                value_layout: value_a,
            },
            FlatValueLayout::Function {
                domain: domain_b,
                value_layout: value_b,
            },
        ) if ordered_dense_int_domain(domain_b) == Some((*lo_a, *len_a)) => {
            let value_layout = merge_flat_value_layouts(value_a, value_b)?;
            Some(FlatValueLayout::IntFunction {
                lo: *lo_a,
                len: *len_a,
                value_layout: Box::new(value_layout),
            })
        }
        (
            FlatValueLayout::Function {
                domain: domain_a,
                value_layout: value_a,
            },
            FlatValueLayout::IntFunction {
                lo: lo_b,
                len: len_b,
                value_layout: value_b,
            },
        ) if ordered_dense_int_domain(domain_a) == Some((*lo_b, *len_b)) => {
            let value_layout = merge_flat_value_layouts(value_a, value_b)?;
            Some(FlatValueLayout::IntFunction {
                lo: *lo_b,
                len: *len_b,
                value_layout: Box::new(value_layout),
            })
        }
        (
            FlatValueLayout::Function {
                domain: domain_a,
                value_layout: value_a,
            },
            FlatValueLayout::Function {
                domain: domain_b,
                value_layout: value_b,
            },
        ) if domain_a == domain_b => {
            let value_layout = merge_flat_value_layouts(value_a, value_b)?;
            Some(flat_function_layout(domain_a.clone(), value_layout))
        }
        (
            FlatValueLayout::Record {
                field_names: names_a,
                field_layouts: fields_a,
            },
            FlatValueLayout::Record {
                field_names: names_b,
                field_layouts: fields_b,
            },
        ) if names_a == names_b && fields_a.len() == fields_b.len() => {
            let mut field_layouts = Vec::with_capacity(fields_a.len());
            for (field_a, field_b) in fields_a.iter().zip(fields_b.iter()) {
                field_layouts.push(merge_flat_value_layouts(field_a, field_b)?);
            }
            Some(FlatValueLayout::Record {
                field_names: names_a.clone(),
                field_layouts,
            })
        }
        (
            FlatValueLayout::SetBitmask {
                universe: universe_a,
            },
            FlatValueLayout::SetBitmask {
                universe: universe_b,
            },
        ) => {
            let mut universe = universe_a.clone();
            universe.extend(universe_b.iter().cloned());
            universe.sort();
            universe.dedup();
            (universe.len() <= 63).then_some(FlatValueLayout::SetBitmask { universe })
        }
        (
            FlatValueLayout::Sequence {
                bound: bound_a,
                max_len: max_a,
                element_layout: elem_a,
            },
            FlatValueLayout::Sequence {
                bound: bound_b,
                max_len: max_b,
                element_layout: elem_b,
            },
        ) => {
            if *max_a == 0 {
                return Some(FlatValueLayout::Sequence {
                    bound: bound_b.clone(),
                    max_len: *max_b,
                    element_layout: elem_b.clone(),
                });
            }
            if *max_b == 0 {
                return Some(FlatValueLayout::Sequence {
                    bound: bound_a.clone(),
                    max_len: *max_a,
                    element_layout: elem_a.clone(),
                });
            }
            let element_layout = merge_flat_value_layouts(elem_a, elem_b)?;
            Some(FlatValueLayout::Sequence {
                bound: merge_sequence_bound_evidence(bound_a, bound_b),
                max_len: (*max_a).max(*max_b),
                element_layout: Box::new(element_layout),
            })
        }
        _ => None,
    }
}

fn merge_sequence_bound_evidence(
    a: &SequenceBoundEvidence,
    b: &SequenceBoundEvidence,
) -> SequenceBoundEvidence {
    if a == b && a.is_proven() {
        a.clone()
    } else {
        SequenceBoundEvidence::Observed
    }
}

fn value_fits_flat_value_layout(value: &Value, layout: &FlatValueLayout) -> bool {
    match layout {
        FlatValueLayout::Scalar(slot_type) => value_fits_slot_type(value, *slot_type),
        FlatValueLayout::IntFunction {
            lo,
            len,
            value_layout,
        } => value_fits_recursive_int_function(value, *lo, *len, value_layout),
        FlatValueLayout::Function {
            domain,
            value_layout,
        } => value_fits_recursive_function(value, domain, value_layout),
        FlatValueLayout::Record {
            field_names,
            field_layouts,
        } => {
            let Value::Record(record) = value else {
                return false;
            };
            record.len() == field_names.len()
                && field_names
                    .iter()
                    .zip(field_layouts.iter())
                    .all(|(field_name, field_layout)| {
                        record
                            .get(field_name)
                            .is_some_and(|child| value_fits_flat_value_layout(child, field_layout))
                    })
        }
        FlatValueLayout::SetBitmask { universe } => {
            let Value::Set(set) = value else {
                return false;
            };
            universe.len() <= 63
                && set
                    .iter()
                    .all(|elem| universe.iter().any(|u| flat_scalar_to_value(u) == *elem))
        }
        FlatValueLayout::Sequence {
            max_len,
            element_layout,
            ..
        } => match value {
            Value::Seq(seq) => {
                seq.len() <= *max_len
                    && seq
                        .iter()
                        .all(|child| value_fits_flat_value_layout(child, element_layout))
            }
            Value::Tuple(elems) => {
                elems.len() <= *max_len
                    && elems
                        .iter()
                        .all(|child| value_fits_flat_value_layout(child, element_layout))
            }
            _ => false,
        },
    }
}

fn value_fits_slot_type(value: &Value, slot_type: SlotType) -> bool {
    matches!(
        (value, slot_type),
        (Value::SmallInt(_) | Value::Int(_), SlotType::Int)
            | (Value::Bool(_), SlotType::Bool)
            | (Value::String(_), SlotType::String)
            | (Value::ModelValue(_), SlotType::ModelValue)
    )
}

fn value_fits_recursive_int_function(
    value: &Value,
    lo: i64,
    len: usize,
    value_layout: &FlatValueLayout,
) -> bool {
    match value {
        Value::IntFunc(func) => {
            let expected_hi = if len == 0 {
                lo.checked_sub(1)
            } else {
                lo.checked_add(len as i64 - 1)
            };
            expected_hi.is_some_and(|hi| func.as_ref().min() == lo && func.as_ref().max() == hi)
                && func
                    .values()
                    .iter()
                    .all(|child| value_fits_flat_value_layout(child, value_layout))
        }
        Value::Func(func) => {
            if func.domain_len() != len {
                return false;
            }
            (0..len).all(|index| {
                let key = Value::SmallInt(lo + index as i64);
                func.mapping_get(&key)
                    .is_some_and(|child| value_fits_flat_value_layout(child, value_layout))
            })
        }
        _ => false,
    }
}

fn value_fits_recursive_function(
    value: &Value,
    domain: &[FlatScalarValue],
    value_layout: &FlatValueLayout,
) -> bool {
    let Value::Func(func) = value else {
        return false;
    };
    func.domain_len() == domain.len()
        && domain.iter().all(|key| {
            let key_value = flat_scalar_to_value(key);
            func.mapping_get(&key_value)
                .is_some_and(|child| value_fits_flat_value_layout(child, value_layout))
        })
}

fn flat_scalar_to_value(value: &FlatScalarValue) -> Value {
    match value {
        FlatScalarValue::Int(n) => Value::SmallInt(*n),
        FlatScalarValue::Bool(b) => Value::Bool(*b),
        FlatScalarValue::String(s) => Value::String(Arc::clone(s)),
        FlatScalarValue::ModelValue(s) => Value::ModelValue(Arc::clone(s)),
    }
}

fn flat_scalar_from_value(value: &Value) -> Option<FlatScalarValue> {
    match value {
        Value::SmallInt(n) => Some(FlatScalarValue::Int(*n)),
        Value::Int(n) => {
            use num_traits::ToPrimitive;
            n.to_i64().map(FlatScalarValue::Int)
        }
        Value::Bool(b) => Some(FlatScalarValue::Bool(*b)),
        Value::String(s) => Some(FlatScalarValue::String(Arc::clone(s))),
        Value::ModelValue(s) => Some(FlatScalarValue::ModelValue(Arc::clone(s))),
        _ => None,
    }
}

/// Try to create an IntArray layout from a Func with contiguous integer domain.
fn try_int_array_from_func(
    func: &tla_value::value::FuncValue,
    min_key: i64,
    expected_len: usize,
) -> Option<VarLayoutKind> {
    let mut all_scalar = true;
    let mut all_bool = true;
    let mut has_string = false;
    for (_key, val) in func.iter() {
        if !is_scalar_value(val) {
            all_scalar = false;
            break;
        }
        if !matches!(val, Value::Bool(_)) {
            all_bool = false;
        }
        if matches!(val, Value::String(_) | Value::ModelValue(_)) {
            has_string = true;
        }
    }
    if all_scalar {
        let element_types = if has_string || !all_bool {
            // Collect per-element types for reconstruction.
            let mut types = Vec::with_capacity(expected_len);
            for i in 0..expected_len {
                let key = Value::SmallInt(min_key + i as i64);
                if let Some(val) = func.apply(&key) {
                    types.push(slot_type_from_value(val));
                } else {
                    types.push(SlotType::Int);
                }
            }
            Some(types)
        } else {
            None
        };
        Some(VarLayoutKind::IntArray {
            lo: min_key,
            len: expected_len,
            elements_are_bool: all_bool,
            element_types,
        })
    } else {
        None
    }
}

/// Check if a Value is a scalar that fits in a single i64.
fn is_scalar_value(value: &Value) -> bool {
    matches!(
        value,
        Value::Bool(_)
            | Value::SmallInt(_)
            | Value::Int(_)
            | Value::String(_)
            | Value::ModelValue(_)
    )
}

/// Determine the SlotType for a scalar Value.
/// Part of #3908.
fn slot_type_from_value(value: &Value) -> SlotType {
    match value {
        Value::Bool(_) => SlotType::Bool,
        Value::String(_) => SlotType::String,
        Value::ModelValue(_) => SlotType::ModelValue,
        _ => SlotType::Int,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::var_index::VarRegistry;
    use std::sync::Arc;
    use tla_value::value::{IntIntervalFunc, RecordValue, SortedSet};

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_all_scalar() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let state = ArrayState::from_values(vec![
            Value::SmallInt(1),
            Value::Bool(true),
            Value::SmallInt(-5),
        ]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 3);
        assert_eq!(layout.total_slots(), 3);
        assert!(layout.is_all_scalar());

        // Bool variable gets ScalarBool, not Scalar.
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::ScalarBool
        ));
        assert!(matches!(
            layout.var_layout(2).unwrap().kind,
            VarLayoutKind::Scalar
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_int_func() {
        let registry = VarRegistry::from_names(["active"]);
        // active = [0 |-> FALSE, 1 |-> TRUE, 2 |-> FALSE]
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(false), Value::Bool(true), Value::Bool(false)],
        );
        let state = ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 1);
        assert_eq!(layout.total_slots(), 3);

        let vl = layout.var_layout(0).unwrap();
        match &vl.kind {
            VarLayoutKind::IntArray {
                lo,
                len,
                elements_are_bool,
                ..
            } => {
                assert_eq!(*lo, 0);
                assert_eq!(*len, 3);
                assert!(
                    *elements_are_bool,
                    "Bool-valued IntFunc should have elements_are_bool=true"
                );
            }
            other => panic!("expected IntArray, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_record_all_scalar() {
        let registry = VarRegistry::from_names(["msg"]);
        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("src"), Value::SmallInt(1)),
            (Arc::from("type"), Value::SmallInt(0)),
        ]);
        let state = ArrayState::from_values(vec![Value::Record(rec)]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 1);

        let vl = layout.var_layout(0).unwrap();
        match &vl.kind {
            VarLayoutKind::Record { field_names, .. } => {
                assert_eq!(field_names.len(), 2);
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_small_set_as_dynamic() {
        // Sets are always Dynamic until bitmask encoding is implemented (Phase 6).
        // See #4007.
        let registry = VarRegistry::from_names(["nodes"]);
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let state = ArrayState::from_values(vec![Value::Set(Arc::new(set))]);

        let layout = infer_layout(&state, &registry);
        let vl = layout.var_layout(0).unwrap();
        assert!(
            matches!(&vl.kind, VarLayoutKind::Dynamic),
            "expected Dynamic for set, got {:?}",
            vl.kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_recursive_mcl_req_shape() {
        let registry = VarRegistry::from_names(["req"]);
        let inner = || {
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                1,
                3,
                vec![Value::SmallInt(0), Value::SmallInt(1), Value::SmallInt(2)],
            )))
        };
        let req = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            3,
            vec![inner(), inner(), inner()],
        )));
        let state = ArrayState::from_values(vec![req]);

        let layout = infer_layout(&state, &registry);

        assert!(layout.is_fully_flat());
        assert_eq!(layout.total_slots(), 9);
        match &layout.var_layout(0).unwrap().kind {
            VarLayoutKind::Recursive {
                layout:
                    FlatValueLayout::IntFunction {
                        lo,
                        len,
                        value_layout,
                    },
            } => {
                assert_eq!((*lo, *len), (1, 3));
                match value_layout.as_ref() {
                    FlatValueLayout::IntFunction {
                        lo,
                        len,
                        value_layout,
                    } => {
                        assert_eq!((*lo, *len), (1, 3));
                        assert_eq!(**value_layout, FlatValueLayout::Scalar(SlotType::Int));
                    }
                    other => panic!("expected nested IntFunction, got {other:?}"),
                }
            }
            other => panic!("expected recursive req layout, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_recursive_mcl_subset_proc_shapes() {
        let registry = VarRegistry::from_names(["clock", "ack", "crit"]);
        let clock = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            3,
            vec![Value::SmallInt(1), Value::SmallInt(1), Value::SmallInt(1)],
        )));
        let empty_proc_set = || Value::Set(Arc::new(SortedSet::from_sorted_vec(vec![])));
        let ack = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            3,
            vec![empty_proc_set(), empty_proc_set(), empty_proc_set()],
        )));
        let crit = empty_proc_set();
        let state = ArrayState::from_values(vec![clock, ack, crit]);

        let layout = infer_layout(&state, &registry);

        assert!(layout.is_fully_flat());
        assert_eq!(layout.total_slots(), 7);
        match &layout.var_layout(1).unwrap().kind {
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction { value_layout, .. },
            } => match value_layout.as_ref() {
                FlatValueLayout::SetBitmask { universe } => assert_eq!(universe.len(), 3),
                other => panic!("expected ack values as SetBitmask, got {other:?}"),
            },
            other => panic!("expected recursive ack layout, got {other:?}"),
        }
        match &layout.var_layout(2).unwrap().kind {
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::SetBitmask { universe },
            } => assert_eq!(universe.len(), 3),
            other => panic!("expected recursive crit bitmask, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_recursive_mcl_seq_subset_proc_shapes() {
        use tla_value::value::SeqValue;

        let registry = VarRegistry::from_names(["clock", "ack", "crit"]);
        let clock = Value::Seq(Arc::new(SeqValue::from_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ])));
        let empty_proc_set = || Value::Set(Arc::new(SortedSet::from_sorted_vec(vec![])));
        let ack = Value::Seq(Arc::new(SeqValue::from_vec(vec![
            empty_proc_set(),
            empty_proc_set(),
            empty_proc_set(),
        ])));
        let crit = empty_proc_set();
        let state = ArrayState::from_values(vec![clock, ack, crit]);

        let layout = infer_layout(&state, &registry);

        assert!(
            layout.is_fully_flat(),
            "sequence-indexed Proc domains should let empty SUBSET Proc values flatten: {:?}",
            layout.var_layout(1).unwrap().kind
        );
        assert_eq!(layout.total_slots(), 9);
        match &layout.var_layout(1).unwrap().kind {
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence { element_layout, .. },
            } => match element_layout.as_ref() {
                FlatValueLayout::SetBitmask { universe } => assert_eq!(universe.len(), 3),
                other => panic!("expected ack sequence values as SetBitmask, got {other:?}"),
            },
            other => panic!("expected recursive ack sequence layout, got {other:?}"),
        }
        match &layout.var_layout(2).unwrap().kind {
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::SetBitmask { universe },
            } => assert_eq!(universe.len(), 3),
            other => panic!("expected recursive crit bitmask, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_recursive_mcl_init_tuple_channel_shapes() {
        use tla_value::value::SeqValue;

        fn seq(values: Vec<Value>) -> Value {
            Value::Seq(Arc::new(SeqValue::from_vec(values)))
        }

        let registry = VarRegistry::from_names(["clock", "req", "ack", "network", "crit"]);
        let clock = seq(vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]);
        let req_row = || {
            seq(vec![
                Value::SmallInt(0),
                Value::SmallInt(0),
                Value::SmallInt(0),
            ])
        };
        let req = seq(vec![req_row(), req_row(), req_row()]);
        let empty_proc_set = || Value::Set(Arc::new(SortedSet::from_sorted_vec(vec![])));
        let ack = seq(vec![empty_proc_set(), empty_proc_set(), empty_proc_set()]);
        let empty_channel = || Value::tuple(Vec::<Value>::new());
        let network_row = || seq(vec![empty_channel(), empty_channel(), empty_channel()]);
        let network = seq(vec![network_row(), network_row(), network_row()]);
        let crit = empty_proc_set();
        let state = ArrayState::from_values(vec![clock, req, ack, network, crit]);

        let layout = infer_layout(&state, &registry);

        assert!(
            layout.is_fully_flat(),
            "MCL init shape should be fully flat, got {:?}",
            layout.var_layout(3).unwrap().kind
        );
        assert_eq!(layout.total_slots(), 35);
        assert_eq!(layout.var_layout(0).unwrap().slot_count, 4);
        assert_eq!(layout.var_layout(1).unwrap().slot_count, 13);
        assert_eq!(layout.var_layout(2).unwrap().slot_count, 4);
        assert_eq!(layout.var_layout(3).unwrap().slot_count, 13);
        assert_eq!(layout.var_layout(4).unwrap().slot_count, 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_recursive_mcl_network_shape_with_observed_message() {
        use tla_value::value::SeqValue;

        let registry = VarRegistry::from_names(["network"]);
        let msg = Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("clock"), Value::SmallInt(1)),
            (Arc::from("type"), Value::String(Arc::from("req"))),
        ]));
        let nonempty = Value::Seq(Arc::new(SeqValue::from_vec(vec![msg])));
        let empty = || Value::Seq(Arc::new(SeqValue::from_vec(vec![])));
        let row1 = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![empty(), nonempty],
        )));
        let row2 = Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 2, vec![empty(), empty()])));
        let network = Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 2, vec![row1, row2])));
        let state = ArrayState::from_values(vec![network]);

        let layout = infer_layout(&state, &registry);

        assert!(layout.is_fully_flat());
        assert_eq!(layout.total_slots(), 12);
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Recursive { .. }
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_wavefront_recursive_network_empty_then_observed_message() {
        use tla_value::value::SeqValue;

        let registry = VarRegistry::from_names(["network"]);
        let empty = || Value::Seq(Arc::new(SeqValue::from_vec(vec![])));
        let empty_row =
            || Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 2, vec![empty(), empty()])));
        let empty_network = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![empty_row(), empty_row()],
        )));

        let msg = Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("clock"), Value::SmallInt(1)),
            (Arc::from("type"), Value::String(Arc::from("req"))),
        ]));
        let observed_row = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![empty(), Value::Seq(Arc::new(SeqValue::from_vec(vec![msg])))],
        )));
        let observed_network = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![observed_row, empty_row()],
        )));
        let states = vec![
            ArrayState::from_values(vec![empty_network]),
            ArrayState::from_values(vec![observed_network]),
        ];

        let layout = infer_layout_from_wavefront(&states, &registry);

        assert!(layout.is_fully_flat());
        assert_eq!(layout.total_slots(), 12);
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Recursive { .. }
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_wavefront_empty_sequence_uses_path_scoped_element_hint() {
        use tla_value::value::SeqValue;

        let registry = VarRegistry::from_names(["network", "log"]);
        let empty = || Value::Seq(Arc::new(SeqValue::from_vec(vec![])));
        let empty_row =
            || Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 2, vec![empty(), empty()])));
        let empty_network = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![empty_row(), empty_row()],
        )));

        let msg = Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("clock"), Value::SmallInt(1)),
            (Arc::from("type"), Value::String(Arc::from("req"))),
        ]));
        let observed_row = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![Value::Seq(Arc::new(SeqValue::from_vec(vec![msg]))), empty()],
        )));
        let observed_network = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![observed_row, empty_row()],
        )));

        let states = vec![
            ArrayState::from_values(vec![
                empty_network,
                Value::Seq(Arc::new(SeqValue::from_vec(vec![Value::SmallInt(1)]))),
            ]),
            ArrayState::from_values(vec![
                observed_network,
                Value::Seq(Arc::new(SeqValue::from_vec(vec![
                    Value::SmallInt(2),
                    Value::SmallInt(3),
                ]))),
            ]),
        ];

        let layout = infer_layout_from_wavefront(&states, &registry);

        assert!(
            layout.is_fully_flat(),
            "path-scoped sequence hints should avoid falling back to Dynamic: {:?}",
            layout.var_layout(0).unwrap().kind
        );
        assert_eq!(layout.total_slots(), 15);
        match &layout.var_layout(0).unwrap().kind {
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction { value_layout, .. },
            } => match value_layout.as_ref() {
                FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                    FlatValueLayout::Sequence {
                        max_len,
                        element_layout,
                        ..
                    } => {
                        assert_eq!(*max_len, 1);
                        assert!(matches!(
                            element_layout.as_ref(),
                            FlatValueLayout::Record { .. }
                        ));
                    }
                    other => panic!("expected network channel sequence layout, got {other:?}"),
                },
                other => panic!("expected nested network function layout, got {other:?}"),
            },
            other => panic!("expected recursive network layout, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_mixed() {
        let registry = VarRegistry::from_names(["pc", "network", "msgs"]);

        // pc = 0 (scalar)
        // network = [0 |-> 0, 1 |-> 0, 2 |-> 0] (IntArray)
        // msgs = <<1, 2>> (fixed sequence)
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let seq =
            tla_value::value::SeqValue::from_vec(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let state = ArrayState::from_values(vec![
            Value::SmallInt(0),
            Value::IntFunc(Arc::new(func)),
            Value::Seq(Arc::new(seq)),
        ]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 3);
        // pc: 1 slot + network: 3 slots + msgs: 3 slots (len + 2 elems) = 7
        assert_eq!(layout.total_slots(), 7);
        assert!(!layout.is_all_scalar());
        assert!(!layout.is_trivial());

        // Verify kinds
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::IntArray { lo: 0, len: 3, .. }
        ));
        assert!(matches!(
            layout.var_layout(2).unwrap().kind,
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence { max_len: 2, .. }
            }
        ));
    }

    // ====================================================================
    // Wavefront inference tests (Part of #3986)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_single_state() {
        // Wavefront with one state should match single-state inference.
        let registry = VarRegistry::from_names(["x", "y"]);
        let state = ArrayState::from_values(vec![Value::SmallInt(1), Value::Bool(true)]);

        let single = infer_layout(&state, &registry);
        let wavefront = infer_layout_from_wavefront(&[state], &registry);

        assert_eq!(single.var_count(), wavefront.var_count());
        assert_eq!(single.total_slots(), wavefront.total_slots());
        for i in 0..single.var_count() {
            assert_eq!(
                single.var_layout(i).unwrap().kind,
                wavefront.var_layout(i).unwrap().kind,
                "var {i} layout kind mismatch between single and wavefront"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_consistent_states() {
        // Multiple states with the same structure should produce the same layout.
        let registry = VarRegistry::from_names(["x", "y"]);
        let states = vec![
            ArrayState::from_values(vec![Value::SmallInt(1), Value::Bool(true)]),
            ArrayState::from_values(vec![Value::SmallInt(2), Value::Bool(false)]),
            ArrayState::from_values(vec![Value::SmallInt(3), Value::Bool(true)]),
        ];

        let layout = infer_layout_from_wavefront(&states, &registry);

        assert_eq!(layout.var_count(), 2);
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::ScalarBool
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_int_array_consistent() {
        // Multiple states with compatible IntFunc should keep IntArray layout.
        let registry = VarRegistry::from_names(["arr"]);
        let mk_state = |a: i64, b: i64, c: i64| {
            let func = IntIntervalFunc::new(
                0,
                2,
                vec![Value::SmallInt(a), Value::SmallInt(b), Value::SmallInt(c)],
            );
            ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))])
        };

        let states = vec![mk_state(1, 2, 3), mk_state(4, 5, 6), mk_state(7, 8, 9)];
        let layout = infer_layout_from_wavefront(&states, &registry);

        assert_eq!(layout.total_slots(), 3);
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
                ..
            }
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_incompatible_downgrades() {
        // If one state has a Scalar but another has a different shape,
        // the wavefront should downgrade to Dynamic.
        let registry = VarRegistry::from_names(["x"]);
        let state_int = ArrayState::from_values(vec![Value::SmallInt(42)]);
        let state_bool = ArrayState::from_values(vec![Value::Bool(true)]);

        // SmallInt -> Scalar, Bool -> ScalarBool: these are incompatible.
        let layout = infer_layout_from_wavefront(&[state_int, state_bool], &registry);

        assert!(
            matches!(layout.var_layout(0).unwrap().kind, VarLayoutKind::Dynamic),
            "incompatible Scalar vs ScalarBool should downgrade to Dynamic, got {:?}",
            layout.var_layout(0).unwrap().kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_int_array_length_mismatch() {
        // IntArray with different lengths should downgrade to Dynamic.
        let registry = VarRegistry::from_names(["arr"]);
        let func3 = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)],
        );
        let func4 = IntIntervalFunc::new(
            0,
            3,
            vec![
                Value::SmallInt(1),
                Value::SmallInt(2),
                Value::SmallInt(3),
                Value::SmallInt(4),
            ],
        );

        let states = vec![
            ArrayState::from_values(vec![Value::IntFunc(Arc::new(func3))]),
            ArrayState::from_values(vec![Value::IntFunc(Arc::new(func4))]),
        ];
        let layout = infer_layout_from_wavefront(&states, &registry);

        assert!(
            matches!(layout.var_layout(0).unwrap().kind, VarLayoutKind::Dynamic),
            "IntArray with different lengths should downgrade to Dynamic, got {:?}",
            layout.var_layout(0).unwrap().kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_mixed_keeps_stable() {
        // A wavefront where some vars are stable and others are not.
        let registry = VarRegistry::from_names(["stable_int", "unstable"]);
        let states = vec![
            ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(10)]),
            ArrayState::from_values(vec![Value::SmallInt(2), Value::Bool(true)]),
        ];

        let layout = infer_layout_from_wavefront(&states, &registry);

        // stable_int: Scalar in both states -> stays Scalar
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        // unstable: Scalar in first, ScalarBool in second -> Dynamic
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::Dynamic
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_record_field_type_mismatch_downgrades() {
        let registry = VarRegistry::from_names(["msg"]);
        let string_state = ArrayState::from_values(vec![Value::Record(
            RecordValue::from_sorted_str_entries(vec![
                (Arc::from("kind"), Value::String(Arc::from("ready"))),
                (Arc::from("round"), Value::SmallInt(1)),
            ]),
        )]);
        let model_value_state = ArrayState::from_values(vec![Value::Record(
            RecordValue::from_sorted_str_entries(vec![
                (Arc::from("kind"), Value::ModelValue(Arc::from("ready"))),
                (Arc::from("round"), Value::SmallInt(2)),
            ]),
        )]);

        let layout = infer_layout_from_wavefront(&[string_state, model_value_state], &registry);

        assert!(
            matches!(layout.var_layout(0).unwrap().kind, VarLayoutKind::Dynamic),
            "record slot type mismatches must downgrade to Dynamic, got {:?}",
            layout.var_layout(0).unwrap().kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dense_ordered_function_layout_normalizes_to_int_function() {
        let dense_function = FlatValueLayout::Function {
            domain: vec![
                FlatScalarValue::Int(2),
                FlatScalarValue::Int(3),
                FlatScalarValue::Int(4),
            ],
            value_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
        };
        let observed = FlatValueLayout::IntFunction {
            lo: 2,
            len: 3,
            value_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
        };

        let proven_applied =
            flat_layout_proof_apply_flat_layout(&dense_function, &observed).unwrap();
        assert_eq!(proven_applied, observed);

        let merged = merge_flat_value_layouts(&dense_function, &dense_function).unwrap();
        assert_eq!(merged, observed);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dense_function_layout_normalization_requires_domain_order() {
        let wrong_order = FlatValueLayout::Function {
            domain: vec![
                FlatScalarValue::Int(2),
                FlatScalarValue::Int(4),
                FlatScalarValue::Int(3),
            ],
            value_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
        };
        let ordered_int_function = FlatValueLayout::IntFunction {
            lo: 2,
            len: 3,
            value_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
        };

        assert!(
            flat_layout_proof_apply_flat_layout(&wrong_order, &ordered_int_function).is_none(),
            "wrong-order generic function domains must not prove IntFunction layout"
        );

        let merged = merge_flat_value_layouts(&wrong_order, &wrong_order).unwrap();
        assert_eq!(merged, wrong_order);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layout_kinds_compatible_same() {
        assert!(layout_kinds_compatible(
            &VarLayoutKind::Scalar,
            &VarLayoutKind::Scalar
        ));
        assert!(layout_kinds_compatible(
            &VarLayoutKind::ScalarBool,
            &VarLayoutKind::ScalarBool
        ));
        assert!(layout_kinds_compatible(
            &VarLayoutKind::Dynamic,
            &VarLayoutKind::Dynamic
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layout_kinds_compatible_different_variant() {
        assert!(!layout_kinds_compatible(
            &VarLayoutKind::Scalar,
            &VarLayoutKind::ScalarBool
        ));
        assert!(!layout_kinds_compatible(
            &VarLayoutKind::Scalar,
            &VarLayoutKind::Dynamic
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layout_kinds_compatible_rejects_slot_type_mismatches() {
        assert!(!layout_kinds_compatible(
            &VarLayoutKind::IntArray {
                lo: 0,
                len: 2,
                elements_are_bool: false,
                element_types: Some(vec![SlotType::String, SlotType::Int]),
            },
            &VarLayoutKind::IntArray {
                lo: 0,
                len: 2,
                elements_are_bool: false,
                element_types: Some(vec![SlotType::ModelValue, SlotType::Int]),
            }
        ));

        assert!(!layout_kinds_compatible(
            &VarLayoutKind::Record {
                field_names: vec![Arc::from("kind")],
                field_is_bool: vec![false],
                field_types: vec![SlotType::String],
            },
            &VarLayoutKind::Record {
                field_names: vec![Arc::from("kind")],
                field_is_bool: vec![false],
                field_types: vec![SlotType::ModelValue],
            }
        ));

        assert!(!layout_kinds_compatible(
            &VarLayoutKind::StringKeyedArray {
                domain_keys: vec![Arc::from("kind")],
                domain_types: vec![SlotType::String],
                value_types: vec![SlotType::String],
            },
            &VarLayoutKind::StringKeyedArray {
                domain_keys: vec![Arc::from("kind")],
                domain_types: vec![SlotType::String],
                value_types: vec![SlotType::ModelValue],
            }
        ));
    }

    #[test]
    fn fixed_domain_sequence_layout_rejects_empty_proof_domain() {
        use tla_value::value::SeqValue;

        let registry = VarRegistry::from_names(["clock"]);
        let state =
            ArrayState::from_values(vec![Value::Seq(Arc::new(SeqValue::from_vec(Vec::new())))]);
        let proofs = vec![SequenceFixedDomainTypeProof {
            var_idx: 0,
            path: vec![],
            domain: Arc::from(Vec::<Value>::new().into_boxed_slice()),
            element_layout: SequenceTypeLayoutProof::Flat(FlatValueLayout::Scalar(SlotType::Int)),
            invariant: Arc::from("TypeOK"),
        }];

        let layout = infer_layout_with_sequence_layout_proofs(&state, &registry, &[], &[], &proofs);

        match &layout.var_layout(0).unwrap().kind {
            VarLayoutKind::Recursive {
                layout:
                    FlatValueLayout::Sequence {
                        bound,
                        max_len,
                        element_layout,
                    },
            } => {
                assert_eq!(*bound, SequenceBoundEvidence::Observed);
                assert_eq!(*max_len, 0);
                assert_eq!(**element_layout, FlatValueLayout::Scalar(SlotType::Int));
            }
            other => panic!("expected observed empty sequence layout, got {other:?}"),
        }
        assert!(!layout.supports_flat_primary());
    }
}
