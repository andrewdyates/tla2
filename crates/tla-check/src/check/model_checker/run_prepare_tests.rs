// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `precompute_constant_operators` — the setup-time constant-folding
//! pass that mirrors TLC's `SpecProcessor.processConstantDefns()`.
//!
//! Part of #3125: replaced shallow `body_references_state_var` tests with
//! semantic level classification tests against the actual precompute pass.

use super::super::bfs::compiled_step_trait::{CompiledBfsLevel, CompiledBfsStep};
use super::super::bfs::flat_frontier::FlatBfsFrontier;
use super::super::bfs::storage_modes::NoTraceQueueEntry;
use super::super::frontier::BfsFrontier;
use super::super::mc_struct::ActionInstanceMeta;
use super::ModelChecker;
use crate::check::model_checker::precompute::{
    precompute_constant_operators, promote_env_constants_to_precomputed,
};
use crate::config::{Config, ConstantValue};
use crate::constants::bind_constants_from_config;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, FlatValueLayout, SequenceBoundEvidence, SlotType, VarLayoutKind};
use crate::test_support::parse_module;
use crate::value::{FuncValue, IntIntervalFunc, RecordValue, SeqValue, SortedSet, Value};
use std::sync::Arc;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::name_intern::intern_name;
use tla_core::span::Spanned;
use tla_tir::bytecode::CompileError;

fn make_op(name: &str, body: Expr) -> OperatorDef {
    OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

fn seed_split_action_meta(checker: &mut ModelChecker<'_>, names: &[&str]) {
    checker.compiled.split_action_meta = Some(
        names
            .iter()
            .map(|name| ActionInstanceMeta {
                name: Some((*name).to_string()),
                bindings: Vec::new(),
                formal_bindings: Vec::new(),
                expr: None,
            })
            .collect(),
    );
}

struct TestCompiledBfsStep {
    state_len: usize,
}

impl CompiledBfsStep for TestCompiledBfsStep {
    fn state_len(&self) -> usize {
        self.state_len
    }

    fn step_flat(
        &self,
        _state: &[i64],
    ) -> Result<tla_jit_runtime::FlatBfsStepOutput, tla_jit_runtime::BfsStepError> {
        Err(tla_jit_runtime::BfsStepError::RuntimeError)
    }
}

struct TestCompiledBfsLevel;

impl CompiledBfsLevel for TestCompiledBfsLevel {
    fn has_fused_level(&self) -> bool {
        true
    }

    fn run_level_fused_arena(
        &self,
        _arena: &[i64],
        _parent_count: usize,
    ) -> Option<
        Result<
            super::super::bfs::compiled_step_trait::CompiledLevelResult,
            tla_jit_runtime::BfsStepError,
        >,
    > {
        Some(Err(tla_jit_runtime::BfsStepError::RuntimeError))
    }
}

fn unsupported_failure_message(
    compiled: &tla_eval::bytecode_vm::CompiledBytecode,
    action_name: &str,
) -> String {
    match compiled
        .failed
        .iter()
        .find(|(name, _)| name == action_name)
        .map(|(_, err)| err)
    {
        Some(CompileError::Unsupported(message)) => message.clone(),
        Some(other) => panic!("expected Unsupported failure for {action_name}, got {other:?}"),
        None => panic!("missing failed compile entry for {action_name}"),
    }
}

fn assert_failed_message_contains(
    compiled: &tla_eval::bytecode_vm::CompiledBytecode,
    action_name: &str,
    expected_fragment: &str,
) {
    let message = unsupported_failure_message(compiled, action_name);
    assert!(
        message.contains(expected_fragment),
        "{action_name} should report {expected_fragment:?}, got: {message}",
    );
}

fn scalar_init_state() -> ArrayState {
    ArrayState::from_values(vec![Value::SmallInt(1), Value::Bool(true)])
}

fn fixed_record_init_state() -> ArrayState {
    let rec = RecordValue::from_sorted_str_entries(vec![
        (Arc::from("flag"), Value::Bool(true)),
        (Arc::from("count"), Value::SmallInt(7)),
    ]);
    ArrayState::from_values(vec![Value::Record(rec)])
}

fn fixed_array_init_state(values: [i64; 3]) -> ArrayState {
    let func = IntIntervalFunc::new(0, 2, values.into_iter().map(Value::SmallInt).collect());
    ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))])
}

fn sequence_init_state() -> ArrayState {
    ArrayState::from_values(vec![Value::Seq(Arc::new(SeqValue::from_vec(vec![
        Value::SmallInt(1),
    ])))])
}

fn observed_network_value() -> Value {
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
    Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 2, vec![row1, row2])))
}

fn empty_network_value() -> Value {
    let empty = || Value::Seq(Arc::new(SeqValue::from_vec(vec![])));
    let empty_row = || Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 2, vec![empty(), empty()])));
    Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![empty_row(), empty_row()],
    )))
}

fn empty_sequence_network_value() -> Value {
    let empty_channel = || Value::Seq(Arc::new(SeqValue::from_vec(Vec::new())));
    let empty_row = || {
        Value::Seq(Arc::new(SeqValue::from_vec(vec![
            empty_channel(),
            empty_channel(),
        ])))
    };
    Value::Seq(Arc::new(SeqValue::from_vec(vec![empty_row(), empty_row()])))
}

fn full_mcl_sequence_init_state(checker: &ModelChecker<'_>) -> ArrayState {
    fn seq(values: Vec<Value>) -> Value {
        Value::Seq(Arc::new(SeqValue::from_vec(values)))
    }

    let empty_proc_set = || Value::Set(Arc::new(SortedSet::from_sorted_vec(vec![])));
    let mut values = vec![Value::SmallInt(0); checker.ctx.var_registry().len()];
    let mut set_var = |name: &str, value: Value| {
        let idx = checker
            .ctx
            .var_registry()
            .get(name)
            .unwrap_or_else(|| panic!("missing variable {name}"))
            .as_usize();
        values[idx] = value;
    };

    set_var(
        "clock",
        seq(vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]),
    );
    let req_row = || {
        seq(vec![
            Value::SmallInt(0),
            Value::SmallInt(0),
            Value::SmallInt(0),
        ])
    };
    set_var("req", seq(vec![req_row(), req_row(), req_row()]));
    set_var(
        "ack",
        seq(vec![empty_proc_set(), empty_proc_set(), empty_proc_set()]),
    );
    let empty_channel = || Value::tuple(Vec::<Value>::new());
    let network_row = || seq(vec![empty_channel(), empty_channel(), empty_channel()]);
    set_var(
        "network",
        seq(vec![network_row(), network_row(), network_row()]),
    );
    set_var("crit", empty_proc_set());
    ArrayState::from_values(values)
}

fn assert_network_channel_bound_observed(layout: &crate::state::StateLayout, message: &str) {
    assert_network_channel_bound_observed_at(layout, 0, message);
}

fn assert_network_channel_bound_observed_at(
    layout: &crate::state::StateLayout,
    var_idx: usize,
    message: &str,
) {
    assert!(
        !layout.supports_flat_primary(),
        "{message}: invalid proof must not make network primary-safe"
    );
    match &layout.var_layout(var_idx).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence { bound, max_len, .. } => {
                    assert_eq!(*bound, SequenceBoundEvidence::Observed, "{message}");
                    assert_eq!(*max_len, 1, "{message}");
                }
                other => {
                    panic!("{message}: expected network channel sequence layout, got {other:?}")
                }
            },
            other => panic!("{message}: expected nested network function layout, got {other:?}"),
        },
        other => panic!("{message}: expected recursive network layout, got {other:?}"),
    }
}

fn assert_message_record_layout(layout: &FlatValueLayout, message: &str) {
    let FlatValueLayout::Record {
        field_names,
        field_layouts,
    } = layout
    else {
        panic!("{message}: expected proven message record layout, got {layout:?}");
    };
    assert_eq!(
        field_layouts.len(),
        field_names.len(),
        "{message}: message field layout count"
    );
    assert_eq!(field_names.len(), 2, "{message}: message fields");
    let clock_pos = field_names
        .iter()
        .position(|name| name.as_ref() == "clock")
        .unwrap_or_else(|| panic!("{message}: missing message clock field"));
    let type_pos = field_names
        .iter()
        .position(|name| name.as_ref() == "type")
        .unwrap_or_else(|| panic!("{message}: missing message type field"));
    assert_eq!(
        field_layouts[clock_pos],
        FlatValueLayout::Scalar(SlotType::Int),
        "{message}: message clock field"
    );
    assert_eq!(
        field_layouts[type_pos],
        FlatValueLayout::Scalar(SlotType::String),
        "{message}: message type field"
    );
}

fn assert_network_channel_capacity_only_at(
    layout: &crate::state::StateLayout,
    var_idx: usize,
    message: &str,
) {
    match &layout.var_layout(var_idx).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence { bound, max_len, .. } => {
                    assert_eq!(
                        *bound,
                        SequenceBoundEvidence::ProvenInvariant {
                            invariant: Arc::from("BoundedNetwork"),
                        },
                        "{message}: invalid TypeOK must leave only capacity evidence"
                    );
                    assert_eq!(*max_len, 3, "{message}: BoundedNetwork capacity");
                }
                other => {
                    panic!("{message}: expected network channel sequence layout, got {other:?}")
                }
            },
            other => panic!("{message}: expected nested network function layout, got {other:?}"),
        },
        other => panic!("{message}: expected recursive network layout, got {other:?}"),
    }
}

fn assert_sequence_network_parent_bounds_observed(
    layout: &crate::state::StateLayout,
    message: &str,
) {
    assert!(
        !layout.supports_flat_primary(),
        "{message}: element-only proof must not make network primary-safe"
    );
    let VarLayoutKind::Recursive {
        layout:
            FlatValueLayout::Sequence {
                bound: network_bound,
                element_layout: row_layout,
                ..
            },
    } = &layout.var_layout(0).unwrap().kind
    else {
        panic!("{message}: expected outer sequence network layout");
    };
    assert_eq!(
        *network_bound,
        SequenceBoundEvidence::Observed,
        "{message}: parent network sequence domain was not proven"
    );
    let FlatValueLayout::Sequence {
        bound: row_bound,
        element_layout: channel_layout,
        ..
    } = row_layout.as_ref()
    else {
        panic!("{message}: expected network row sequence layout, got {row_layout:?}");
    };
    assert_eq!(
        *row_bound,
        SequenceBoundEvidence::Observed,
        "{message}: parent network row sequence domain was not proven"
    );
    let FlatValueLayout::Sequence {
        bound: channel_bound,
        max_len: channel_len,
        element_layout: message_layout,
    } = channel_layout.as_ref()
    else {
        panic!("{message}: expected channel sequence layout, got {channel_layout:?}");
    };
    assert_eq!(
        *channel_bound,
        SequenceBoundEvidence::ProvenInvariantWithElementLayout {
            invariant: Arc::from("BoundedNetwork"),
            element_invariant: Arc::from("TypeOK"),
        },
        "{message}: channel should keep capacity plus element-layout proof"
    );
    assert_eq!(*channel_len, 3, "{message}: channel capacity");
    assert_message_record_layout(message_layout, message);
}

fn assert_single_sequence_bound_observed(layout: &crate::state::StateLayout, message: &str) {
    assert!(
        !layout.supports_flat_primary(),
        "{message}: invalid fixed-domain TypeOK must not activate flat-primary"
    );
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout:
                FlatValueLayout::Sequence {
                    bound,
                    element_layout,
                    ..
                },
        } => {
            assert_eq!(
                *bound,
                SequenceBoundEvidence::Observed,
                "{message}: fixed-domain evidence should not attach"
            );
            assert_eq!(
                element_layout.as_ref(),
                &FlatValueLayout::Scalar(SlotType::Int),
                "{message}: observed integer element layout should remain"
            );
        }
        other => panic!("{message}: expected recursive sequence layout, got {other:?}"),
    }
}

fn assert_fixed_int_sequence_layout(
    layout: &crate::state::StateLayout,
    max_len: usize,
    message: &str,
) {
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout:
                FlatValueLayout::Sequence {
                    bound,
                    max_len: actual_len,
                    element_layout,
                },
        } => {
            assert_eq!(
                *actual_len, max_len,
                "{message}: fixed-domain sequence length"
            );
            assert_eq!(
                *bound,
                SequenceBoundEvidence::FixedDomainTypeLayout {
                    invariant: Arc::from("TypeOK")
                },
                "{message}: fixed-domain sequence bound"
            );
            assert_eq!(
                element_layout.as_ref(),
                &FlatValueLayout::Scalar(SlotType::Int),
                "{message}: fixed-domain sequence element layout"
            );
        }
        other => panic!("{message}: expected recursive sequence layout, got {other:?}"),
    }
}

fn assert_fixed_nested_int_sequence_layout(
    layout: &crate::state::StateLayout,
    outer_len: usize,
    row_len: usize,
    message: &str,
) {
    let VarLayoutKind::Recursive { layout: req } = &layout.var_layout(0).unwrap().kind else {
        panic!("{message}: expected recursive nested sequence layout");
    };
    let FlatValueLayout::Sequence {
        bound: outer_bound,
        max_len: actual_outer_len,
        element_layout: row_layout,
    } = req
    else {
        panic!("{message}: expected outer sequence layout, got {req:?}");
    };
    assert_eq!(
        *outer_bound,
        SequenceBoundEvidence::FixedDomainTypeLayout {
            invariant: Arc::from("TypeOK")
        },
        "{message}: outer fixed-domain bound"
    );
    assert_eq!(
        *actual_outer_len, outer_len,
        "{message}: outer fixed-domain length"
    );
    let FlatValueLayout::Sequence {
        bound: row_bound,
        max_len: actual_row_len,
        element_layout: cell_layout,
    } = row_layout.as_ref()
    else {
        panic!("{message}: expected row sequence layout, got {row_layout:?}");
    };
    assert_eq!(
        *row_bound,
        SequenceBoundEvidence::FixedDomainTypeLayout {
            invariant: Arc::from("TypeOK")
        },
        "{message}: row fixed-domain bound"
    );
    assert_eq!(
        *actual_row_len, row_len,
        "{message}: row fixed-domain length"
    );
    assert_eq!(
        cell_layout.as_ref(),
        &FlatValueLayout::Scalar(SlotType::Int),
        "{message}: row cell layout"
    );
}

fn assert_sequence_network_type_layout_not_proven(
    layout: &crate::state::StateLayout,
    message: &str,
) {
    assert!(
        !layout.supports_flat_primary(),
        "{message}: invalid type alias must not make network primary-safe"
    );
    let VarLayoutKind::Recursive {
        layout:
            FlatValueLayout::Sequence {
                bound: network_bound,
                element_layout: row_layout,
                ..
            },
    } = &layout.var_layout(0).unwrap().kind
    else {
        panic!("{message}: expected outer sequence network layout");
    };
    assert_eq!(
        *network_bound,
        SequenceBoundEvidence::Observed,
        "{message}: invalid alias must not prove outer network domain"
    );
    let FlatValueLayout::Sequence {
        bound: row_bound,
        element_layout: channel_layout,
        ..
    } = row_layout.as_ref()
    else {
        panic!("{message}: expected network row sequence layout, got {row_layout:?}");
    };
    assert_eq!(
        *row_bound,
        SequenceBoundEvidence::Observed,
        "{message}: invalid alias must not prove row domain"
    );
    let FlatValueLayout::Sequence { bound, max_len, .. } = channel_layout.as_ref() else {
        panic!("{message}: expected channel sequence layout, got {channel_layout:?}");
    };
    assert_eq!(
        *bound,
        SequenceBoundEvidence::ProvenInvariant {
            invariant: Arc::from("BoundedNetwork")
        },
        "{message}: channel should retain capacity-only evidence"
    );
    assert_eq!(*max_len, 3, "{message}: channel capacity");
}

#[test]
fn test_flat_state_primary_still_promotes_scalar_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryScalarActivation ----
VARIABLES x, ok
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    let init = scalar_init_state();

    checker.infer_flat_state_layout(&init);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for scalar state");
    assert!(layout.is_all_scalar());
    assert!(layout.is_fully_flat());
    assert!(
        checker.is_flat_state_primary(),
        "verified all-scalar layouts remain flat_state_primary"
    );
}

#[test]
fn test_flat_state_primary_rejects_scalar_model_value_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryModelValueGuard ----
VARIABLE state
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    let init = ArrayState::from_values(vec![Value::ModelValue(Arc::from("NULL"))]);

    checker.infer_flat_state_layout(&init);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for model-value state");
    assert!(layout.is_fully_flat());
    assert!(
        !layout.supports_flat_primary(),
        "model-value scalar slots are adapter-safe but not raw flat-primary safe"
    );
    assert!(
        !checker.is_flat_state_primary(),
        "model-value scalar slots must not promote to flat_state_primary"
    );
}

#[test]
fn test_flat_state_primary_promotes_fixed_record_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryRecordActivation ----
VARIABLE rec
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    let init = fixed_record_init_state();

    checker.infer_flat_state_layout(&init);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for record state");
    assert!(
        layout.is_fully_flat(),
        "fixed scalar-field records are complete flat layouts"
    );
    assert!(
        !layout.is_all_scalar(),
        "record layout must exercise the fully-flat non-scalar path"
    );
    assert!(
        checker.is_flat_state_primary(),
        "verified fully-flat records should become flat_state_primary"
    );
}

#[test]
fn test_flat_state_primary_promotion_clears_stale_compiled_bfs_artifacts() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryRecordClearsStaleCompiledBfs ----
VARIABLE rec
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    checker.compiled_bfs_step = Some(Box::new(TestCompiledBfsStep { state_len: 1 }));
    checker.compiled_bfs_level = Some(Box::new(TestCompiledBfsLevel));
    #[cfg(feature = "llvm2")]
    {
        checker.llvm2_build_stats = Some(Default::default());
    }

    checker.infer_flat_state_layout(&fixed_record_init_state());

    assert!(checker.is_flat_state_primary());
    assert!(
        checker.compiled_bfs_step.is_none(),
        "multi-slot flat-primary promotion must drop stale logical-width step"
    );
    assert!(
        checker.compiled_bfs_level.is_none(),
        "multi-slot flat-primary promotion must drop stale logical-width fused level"
    );
    #[cfg(feature = "llvm2")]
    assert!(
        checker.llvm2_build_stats.is_none(),
        "LLVM2 build stats must be cleared with stale layout-sensitive artifacts"
    );
}

#[test]
fn test_compiled_bfs_activation_rejects_stale_flat_width() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryRecordRejectsStaleCompiledWidth ----
VARIABLE rec
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    checker.infer_flat_state_layout(&fixed_record_init_state());
    assert!(checker.is_flat_state_primary());
    let flat_slots = checker
        .flat_bfs_adapter
        .as_ref()
        .expect("flat adapter should be installed")
        .num_slots();
    assert_ne!(flat_slots, checker.test_vars().len());

    checker.compiled_bfs_step = Some(Box::new(TestCompiledBfsStep {
        state_len: checker.test_vars().len(),
    }));
    assert!(
        !checker.should_use_compiled_bfs(),
        "stale logical-width compiled step must not activate on a flat frontier"
    );

    checker.compiled_bfs_step = Some(Box::new(TestCompiledBfsStep {
        state_len: flat_slots,
    }));
    assert!(
        checker.should_use_compiled_bfs(),
        "matching flat-slot compiled step remains eligible"
    );
}

#[test]
fn test_flat_state_primary_promotes_fixed_array_wavefront_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryArrayActivation ----
VARIABLE arr
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    let states = vec![
        fixed_array_init_state([1, 2, 3]),
        fixed_array_init_state([4, 5, 6]),
    ];

    checker.infer_flat_state_layout_from_wavefront(&states);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for fixed-array wavefront");
    assert!(
        layout.is_fully_flat(),
        "fixed integer-indexed arrays are complete flat layouts"
    );
    assert!(
        !layout.is_all_scalar(),
        "array layout must exercise the fully-flat non-scalar path"
    );
    assert!(
        checker.is_flat_state_primary(),
        "verified fully-flat arrays should become flat_state_primary"
    );
}

#[test]
fn test_flat_state_primary_rejects_recursive_sequence_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimarySequenceGuard ----
VARIABLE queue
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);

    checker.infer_flat_state_layout(&sequence_init_state());

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for sequence state");
    assert!(
        layout.is_fully_flat(),
        "fixed-capacity sequences still use a complete slot layout for fitting states"
    );
    assert!(
        !layout.supports_flat_primary(),
        "sequence capacity inferred from one state must not activate flat-primary BFS"
    );
    assert!(
        !checker.is_flat_state_primary(),
        "recursive sequence layouts must stay on ArrayState-primary BFS"
    );
}

#[test]
fn test_flat_state_primary_rejects_observed_recursive_network_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryObservedNetworkGuard ----
VARIABLE network
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    let init = ArrayState::from_values(vec![observed_network_value()]);

    checker.infer_flat_state_layout(&init);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for observed network");
    assert!(layout.is_fully_flat());
    assert!(
        !layout.supports_flat_primary(),
        "observed recursive sequence capacity must not be primary-safe"
    );
    assert!(
        !checker.is_flat_state_primary(),
        "observed-only recursive network must stay ArrayState-primary"
    );
}

#[test]
fn test_bounded_network_proof_marks_matching_path_capacity_only() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryBoundedNetworkProof ----
EXTENDS Naturals, Sequences
VARIABLES log, network
Proc == {1, 2}
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    let log_value = Value::Seq(Arc::new(SeqValue::from_vec(vec![Value::SmallInt(1)])));
    let init = ArrayState::from_values(vec![log_value, observed_network_value()]);

    checker.infer_flat_state_layout(&init);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for proven network");
    assert!(
        !layout.supports_flat_primary(),
        "non-matching observed log sequence must still block primary-safe layout"
    );
    assert!(!checker.is_flat_state_primary());

    match &layout.var_layout(1).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence { bound, max_len, .. } => {
                    assert_eq!(*max_len, 3);
                    assert_eq!(
                        *bound,
                        SequenceBoundEvidence::ProvenInvariant {
                            invariant: Arc::from("BoundedNetwork")
                        }
                    );
                }
                other => panic!("expected network channel sequence layout, got {other:?}"),
            },
            other => panic!("expected nested network function layout, got {other:?}"),
        },
        other => panic!("expected recursive network layout, got {other:?}"),
    }

    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::Sequence { bound, .. },
        } => assert_eq!(*bound, SequenceBoundEvidence::Observed),
        other => panic!("expected recursive log sequence layout, got {other:?}"),
    }

    let network_only_module = parse_module(
        r#"
---- MODULE FlatPrimaryBoundedNetworkOnlyProof ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {1, 2}
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut network_only_checker = ModelChecker::new(&network_only_module, &config);
    network_only_checker
        .infer_flat_state_layout(&ArrayState::from_values(vec![observed_network_value()]));
    assert!(
        !network_only_checker
            .flat_state_layout()
            .expect("layout should be inferred for network-only state")
            .supports_flat_primary(),
        "a length proof alone must not make observed element shape primary-safe"
    );
    assert!(
        !network_only_checker.is_flat_state_primary(),
        "proven length without proven element shape must stay ArrayState-primary"
    );
}

#[test]
fn test_typeok_and_bounded_network_make_empty_mcl_channels_primary_safe() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryMclTypeOkBoundedNetwork ----
EXTENDS Naturals, Sequences
VARIABLES network
Proc == {1, 2}
Message == {
    [type |-> "req", clock |-> 1],
    [type |-> "ack", clock |-> 0],
    [type |-> "rel", clock |-> 0]
}
TypeOK == network \in [Proc -> [Proc -> Seq(Message)]]
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    precompute_constant_operators(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![empty_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for MCL network");
    assert!(
        layout.supports_flat_primary(),
        "TypeOK proves channel element shape and BoundedNetwork proves capacity"
    );
    assert!(
        checker.is_flat_state_primary(),
        "empty MCL channels with TypeOK+BoundedNetwork should qualify for flat_state_primary"
    );

    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence {
                    bound,
                    max_len,
                    element_layout,
                } => {
                    assert_eq!(*max_len, 3);
                    assert_eq!(
                        *bound,
                        SequenceBoundEvidence::ProvenInvariantWithElementLayout {
                            invariant: Arc::from("BoundedNetwork"),
                            element_invariant: Arc::from("TypeOK"),
                        }
                    );
                    match element_layout.as_ref() {
                        FlatValueLayout::Record {
                            field_names,
                            field_layouts,
                        } => {
                            assert!(field_names.contains(&Arc::from("type")));
                            assert!(field_names.contains(&Arc::from("clock")));
                            assert!(
                                field_layouts.contains(&FlatValueLayout::Scalar(SlotType::String))
                            );
                            assert!(field_layouts.contains(&FlatValueLayout::Scalar(SlotType::Int)));
                        }
                        other => panic!("expected proven message record layout, got {other:?}"),
                    }
                }
                other => panic!("expected network channel sequence layout, got {other:?}"),
            },
            other => panic!("expected nested network function layout, got {other:?}"),
        },
        other => panic!("expected recursive network layout, got {other:?}"),
    }
}

#[test]
fn test_typeok_real_mcl_message_operator_proves_empty_channel_element_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryRealMclMessageTypeOk ----
EXTENDS Naturals, Sequences
VARIABLES network
Proc == {1, 2}
Clock == Nat \ {0}
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]
Message == {AckMessage, RelMessage} \cup {ReqMessage(c) : c \in Clock}
TypeOK == network \in [Proc -> [Proc -> Seq(Message)]]
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    precompute_constant_operators(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![empty_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for real MCL-shaped network");
    assert!(
        layout.supports_flat_primary(),
        "operator-defined Message should prove empty channel element layout"
    );
    assert!(
        checker.is_flat_state_primary(),
        "real MCL-shaped TypeOK+BoundedNetwork should activate flat_state_primary"
    );

    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence {
                    bound,
                    element_layout,
                    ..
                } => {
                    assert_eq!(
                        *bound,
                        SequenceBoundEvidence::ProvenInvariantWithElementLayout {
                            invariant: Arc::from("BoundedNetwork"),
                            element_invariant: Arc::from("TypeOK"),
                        }
                    );
                    match element_layout.as_ref() {
                        FlatValueLayout::Record {
                            field_names,
                            field_layouts,
                        } => {
                            assert!(field_names.contains(&Arc::from("type")));
                            assert!(field_names.contains(&Arc::from("clock")));
                            assert!(
                                field_layouts.contains(&FlatValueLayout::Scalar(SlotType::String))
                            );
                            assert!(field_layouts.contains(&FlatValueLayout::Scalar(SlotType::Int)));
                        }
                        other => panic!("expected Message record layout, got {other:?}"),
                    }
                }
                other => panic!("expected network channel sequence layout, got {other:?}"),
            },
            other => panic!("expected nested network function layout, got {other:?}"),
        },
        other => panic!("expected recursive network layout, got {other:?}"),
    }
}

#[test]
fn test_typeok_mcl_range_alias_proc_proves_empty_channel_element_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryMclRangeAliasProc ----
EXTENDS Naturals, Sequences
VARIABLES network
Proc == 1..2
Clock == 1..7
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]
Message == {AckMessage, RelMessage} \cup {ReqMessage(c) : c \in Clock}
TypeOK == network \in [Proc -> [Proc -> Seq(Message)]]
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    precompute_constant_operators(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![empty_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for range-alias MCL network");
    assert!(
        layout.supports_flat_primary(),
        "range aliases like Proc == 1..N must prove the same recursive layout as set aliases"
    );
    assert!(
        checker.is_flat_state_primary(),
        "range-alias MCL TypeOK+BoundedNetwork should activate flat_state_primary"
    );
}

#[test]
fn test_typeok_mcl_cfg_nat_replacement_proves_empty_channel_element_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryMclCfgNatReplacement ----
EXTENDS Naturals, Sequences
CONSTANTS N, Zero, MaxNat, MaxChannel
VARIABLES network
ZeroOverride == 0
MaxChannelOverride == 3
NatOverride == Zero..MaxNat
Proc == 1..N
Clock == Nat \ {Zero}
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]
Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}
TypeOK == network \in [Proc -> [Proc -> Seq(Message)]]
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= MaxChannel
====
"#,
    );
    let mut config = Config::default();
    config.add_constant("N".to_string(), ConstantValue::Value("2".to_string()));
    config.add_constant("MaxNat".to_string(), ConstantValue::Value("7".to_string()));
    config.add_constant(
        "Zero".to_string(),
        ConstantValue::Replacement("ZeroOverride".to_string()),
    );
    config.add_constant(
        "MaxChannel".to_string(),
        ConstantValue::Replacement("MaxChannelOverride".to_string()),
    );
    config.add_constant(
        "Nat".to_string(),
        ConstantValue::Replacement("NatOverride".to_string()),
    );
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    bind_constants_from_config(&mut checker.ctx, &config).expect("config constants bind");
    precompute_constant_operators(&mut checker.ctx);
    promote_env_constants_to_precomputed(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![empty_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for cfg-replaced MCL network");
    assert!(
        layout.supports_flat_primary(),
        "cfg replacement Nat <- NatOverride must still prove MCL sequence capacity and element layout"
    );
    assert!(
        checker.is_flat_state_primary(),
        "MCL-shaped TypeOK+BoundedNetwork with cfg Nat replacement should activate flat_state_primary"
    );
}

#[test]
fn test_typeok_mcl_multi_hop_cfg_replacements_prove_empty_channel_element_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryMclMultiHopCfgReplacement ----
EXTENDS Naturals, Sequences
CONSTANTS N, Zero, MaxNat, MaxChannel
VARIABLES network
ZeroOverride == 0
MaxChannelOverride == 3
NatOverride == Zero..MaxNat
Proc == {1}
ProcOverride == 1..N
Clock == Nat \ {Zero}
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> Zero]
RelMessage == [type |-> "rel", clock |-> Zero]
Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}
TypeOK == network \in [Proc \ {1} -> [Proc -> Seq(Message)]]
MCLTypeOK == network \in [Proc -> [Proc -> Seq(Message)]]
BoundedNetwork == Len(network[1][1]) <= 1
MCBoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= MaxChannel
====
"#,
    );
    let mut config = Config::default();
    config.add_constant("N".to_string(), ConstantValue::Value("2".to_string()));
    config.add_constant("MaxNat".to_string(), ConstantValue::Value("7".to_string()));
    config.add_constant(
        "Zero".to_string(),
        ConstantValue::Replacement("ZeroAlias".to_string()),
    );
    config.add_constant(
        "ZeroAlias".to_string(),
        ConstantValue::Replacement("ZeroOverride".to_string()),
    );
    config.add_constant(
        "MaxChannel".to_string(),
        ConstantValue::Replacement("MaxChannelAlias".to_string()),
    );
    config.add_constant(
        "MaxChannelAlias".to_string(),
        ConstantValue::Replacement("MaxChannelOverride".to_string()),
    );
    config.add_constant(
        "Nat".to_string(),
        ConstantValue::Replacement("NatAlias".to_string()),
    );
    config.add_constant(
        "NatAlias".to_string(),
        ConstantValue::Replacement("NatOverride".to_string()),
    );
    config.add_constant(
        "Proc".to_string(),
        ConstantValue::Replacement("ProcAlias".to_string()),
    );
    config.add_constant(
        "ProcAlias".to_string(),
        ConstantValue::Replacement("ProcOverride".to_string()),
    );
    config.add_constant(
        "TypeOK".to_string(),
        ConstantValue::Replacement("TypeOKAlias".to_string()),
    );
    config.add_constant(
        "TypeOKAlias".to_string(),
        ConstantValue::Replacement("MCLTypeOK".to_string()),
    );
    config.add_constant(
        "BoundedNetwork".to_string(),
        ConstantValue::Replacement("BoundedNetworkAlias".to_string()),
    );
    config.add_constant(
        "BoundedNetworkAlias".to_string(),
        ConstantValue::Replacement("MCBoundedNetwork".to_string()),
    );
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    bind_constants_from_config(&mut checker.ctx, &config).expect("config constants bind");
    precompute_constant_operators(&mut checker.ctx);
    promote_env_constants_to_precomputed(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![empty_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for multi-hop cfg-replaced MCL network");
    assert!(
        layout.supports_flat_primary(),
        "multi-hop cfg replacements must prove MCL sequence capacity and element layout"
    );
    assert!(
        checker.is_flat_state_primary(),
        "MCL-shaped TypeOK+BoundedNetwork with multi-hop cfg replacements should activate flat_state_primary"
    );
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence {
                    bound,
                    max_len,
                    element_layout,
                } => {
                    assert_eq!(*max_len, 3);
                    assert_eq!(
                        *bound,
                        SequenceBoundEvidence::ProvenInvariantWithElementLayout {
                            invariant: Arc::from("BoundedNetwork"),
                            element_invariant: Arc::from("TypeOK"),
                        }
                    );
                    assert_message_record_layout(element_layout, "multi-hop cfg replacements");
                }
                other => panic!("expected network channel sequence layout, got {other:?}"),
            },
            other => panic!("expected nested network function layout, got {other:?}"),
        },
        other => panic!("expected recursive network layout, got {other:?}"),
    }
}

#[test]
fn test_replacement_cycle_does_not_fall_back_to_original_proof_domain() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryReplacementCycleProofDomain ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {1, 2}
Message == {
    [type |-> "req", clock |-> 1],
    [type |-> "ack", clock |-> 0],
    [type |-> "rel", clock |-> 0]
}
TypeOK == network \in [Proc -> [Proc -> Seq(Message)]]
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.add_constant(
        "Proc".to_string(),
        ConstantValue::Replacement("ProcAlias".to_string()),
    );
    config.add_constant(
        "ProcAlias".to_string(),
        ConstantValue::Replacement("Proc".to_string()),
    );
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    bind_constants_from_config(&mut checker.ctx, &config).expect("config constants bind");
    precompute_constant_operators(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![observed_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred with replacement cycle rejected");
    assert_network_channel_bound_observed(layout, "replacement-cycle proof domain");
    assert!(
        !checker.is_flat_state_primary(),
        "cyclic replacement provenance must not activate flat_state_primary"
    );
}

#[test]
fn test_full_mcl_sequence_init_typeok_proves_flat_primary_safe() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryFullMclSequenceTypeOk ----
EXTENDS Naturals, Sequences
CONSTANTS N, Zero, MaxNat, MaxChannel
VARIABLES clock, req, ack, network, crit
ZeroOverride == 0
MaxChannelOverride == 3
NatOverride == Zero..MaxNat
Proc == 1..N
Clock == Nat \ {Zero}
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]
Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}
TypeOK ==
  /\ clock \in [Proc -> Clock]
  /\ req \in [Proc -> [Proc -> Nat]]
  /\ ack \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit \in SUBSET Proc
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= MaxChannel
====
"#,
    );
    let mut config = Config::default();
    config.add_constant("N".to_string(), ConstantValue::Value("3".to_string()));
    config.add_constant("MaxNat".to_string(), ConstantValue::Value("7".to_string()));
    config.add_constant(
        "Zero".to_string(),
        ConstantValue::Replacement("ZeroOverride".to_string()),
    );
    config.add_constant(
        "MaxChannel".to_string(),
        ConstantValue::Replacement("MaxChannelOverride".to_string()),
    );
    config.add_constant(
        "Nat".to_string(),
        ConstantValue::Replacement("NatOverride".to_string()),
    );
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    bind_constants_from_config(&mut checker.ctx, &config).expect("config constants bind");
    precompute_constant_operators(&mut checker.ctx);
    promote_env_constants_to_precomputed(&mut checker.ctx);
    let init = full_mcl_sequence_init_state(&checker);

    checker.infer_flat_state_layout(&init);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for full MCL sequence-shaped init");
    assert_eq!(layout.total_slots(), 89);
    assert!(layout.is_fully_flat());
    assert!(
        layout.supports_flat_primary(),
        "full MCL TypeOK plus BoundedNetwork should make every recursive sequence primary-safe: {:?}",
        layout.var_layout(
            checker
                .ctx
                .var_registry()
                .get("network")
                .expect("network var")
                .as_usize()
        )
        .unwrap()
        .kind
    );
    assert!(
        checker.is_flat_state_primary(),
        "real sequence-shaped MCL init should activate flat_state_primary"
    );
    let mut adapter = checker
        .flat_bfs_adapter()
        .expect("flat_state_primary should install a FlatBfsAdapter");
    let flat_init = adapter
        .try_array_to_flat_lossless(&init)
        .expect("full MCL init must flatten losslessly for flat-primary BFS");
    let mut frontier = FlatBfsFrontier::with_capacity(Arc::clone(adapter.layout()), 1);
    let fp = flat_init.fingerprint_compiled();
    frontier.push((
        NoTraceQueueEntry::Flat {
            flat: flat_init,
            fp,
        },
        0,
        0,
    ));
    assert_eq!(frontier.total_pushed(), 1);
    assert_eq!(frontier.flat_pushed(), 1);
    assert_eq!(frontier.remaining_flat_count(), 1);
    assert!(
        !frontier.has_fallback_entries(),
        "full MCL init must enter the flat frontier arena, not the fallback queue"
    );

    let clock_idx = checker
        .ctx
        .var_registry()
        .get("clock")
        .expect("clock var")
        .as_usize();
    let req_idx = checker
        .ctx
        .var_registry()
        .get("req")
        .expect("req var")
        .as_usize();
    let ack_idx = checker
        .ctx
        .var_registry()
        .get("ack")
        .expect("ack var")
        .as_usize();
    let crit_idx = checker
        .ctx
        .var_registry()
        .get("crit")
        .expect("crit var")
        .as_usize();
    let network_idx = checker
        .ctx
        .var_registry()
        .get("network")
        .expect("network var")
        .as_usize();
    let clock_layout = layout.var_layout(clock_idx).expect("clock layout");
    assert_eq!(clock_layout.slot_count, 4);
    match &clock_layout.kind {
        VarLayoutKind::Recursive {
            layout:
                FlatValueLayout::Sequence {
                    bound,
                    max_len,
                    element_layout,
                },
        } => {
            assert_eq!(*max_len, 3);
            assert_eq!(
                *bound,
                SequenceBoundEvidence::FixedDomainTypeLayout {
                    invariant: Arc::from("TypeOK")
                }
            );
            assert_eq!(
                element_layout.as_ref(),
                &FlatValueLayout::Scalar(SlotType::Int)
            );
        }
        other => panic!("expected recursive clock sequence layout, got {other:?}"),
    }
    let req_layout = layout.var_layout(req_idx).expect("req layout");
    assert_eq!(req_layout.slot_count, 13);
    let VarLayoutKind::Recursive { layout: req } = &req_layout.kind else {
        panic!("expected recursive req layout, got {:?}", req_layout.kind);
    };
    let FlatValueLayout::Sequence {
        bound: req_bound,
        max_len: req_len,
        element_layout: req_row_layout,
    } = req
    else {
        panic!("expected req as sequence layout, got {req:?}");
    };
    assert_eq!(
        *req_bound,
        SequenceBoundEvidence::FixedDomainTypeLayout {
            invariant: Arc::from("TypeOK")
        }
    );
    assert_eq!(*req_len, 3);
    let FlatValueLayout::Sequence {
        bound: req_row_bound,
        max_len: req_row_len,
        element_layout: req_cell_layout,
    } = req_row_layout.as_ref()
    else {
        panic!("expected req rows as sequence layout, got {req_row_layout:?}");
    };
    assert_eq!(
        *req_row_bound,
        SequenceBoundEvidence::FixedDomainTypeLayout {
            invariant: Arc::from("TypeOK")
        }
    );
    assert_eq!(*req_row_len, 3);
    assert_eq!(
        req_cell_layout.as_ref(),
        &FlatValueLayout::Scalar(SlotType::Int)
    );
    match &layout.var_layout(ack_idx).unwrap().kind {
        VarLayoutKind::Recursive {
            layout:
                FlatValueLayout::Sequence {
                    bound,
                    max_len,
                    element_layout,
                },
        } => {
            assert_eq!(*max_len, 3);
            assert_eq!(
                *bound,
                SequenceBoundEvidence::FixedDomainTypeLayout {
                    invariant: Arc::from("TypeOK")
                }
            );
            match element_layout.as_ref() {
                FlatValueLayout::SetBitmask { universe } => assert_eq!(universe.len(), 3),
                other => panic!("expected ack sequence values as SetBitmask, got {other:?}"),
            }
        }
        other => panic!("expected recursive ack sequence layout, got {other:?}"),
    }
    let network_layout = layout.var_layout(network_idx).expect("network layout");
    assert_eq!(network_layout.slot_count, 67);
    let VarLayoutKind::Recursive { layout: network } = &network_layout.kind else {
        panic!(
            "expected recursive network layout, got {:?}",
            network_layout.kind
        );
    };
    let FlatValueLayout::Sequence {
        bound: network_bound,
        max_len: network_len,
        element_layout: network_row_layout,
    } = network
    else {
        panic!("expected network as sequence layout, got {network:?}");
    };
    assert_eq!(
        *network_bound,
        SequenceBoundEvidence::FixedDomainTypeLayout {
            invariant: Arc::from("TypeOK")
        }
    );
    assert_eq!(*network_len, 3);
    let FlatValueLayout::Sequence {
        bound: row_bound,
        max_len: row_len,
        element_layout: channel_layout,
    } = network_row_layout.as_ref()
    else {
        panic!("expected network rows as sequence layout, got {network_row_layout:?}");
    };
    assert_eq!(
        *row_bound,
        SequenceBoundEvidence::FixedDomainTypeLayout {
            invariant: Arc::from("TypeOK")
        }
    );
    assert_eq!(*row_len, 3);
    let FlatValueLayout::Sequence {
        bound: channel_bound,
        max_len: channel_len,
        element_layout: message_layout,
    } = channel_layout.as_ref()
    else {
        panic!("expected network channels as sequence layout, got {channel_layout:?}");
    };
    assert_eq!(
        *channel_bound,
        SequenceBoundEvidence::ProvenInvariantWithElementLayout {
            invariant: Arc::from("BoundedNetwork"),
            element_invariant: Arc::from("TypeOK"),
        }
    );
    assert_eq!(*channel_len, 3);
    let FlatValueLayout::Record {
        field_names,
        field_layouts,
    } = message_layout.as_ref()
    else {
        panic!("expected message element record layout, got {message_layout:?}");
    };
    assert_eq!(field_names.len(), 2);
    let clock_pos = field_names
        .iter()
        .position(|name| name.as_ref() == "clock")
        .expect("message clock field");
    let type_pos = field_names
        .iter()
        .position(|name| name.as_ref() == "type")
        .expect("message type field");
    assert_eq!(
        field_layouts[clock_pos],
        FlatValueLayout::Scalar(SlotType::Int)
    );
    assert_eq!(
        field_layouts[type_pos],
        FlatValueLayout::Scalar(SlotType::String)
    );
    match &layout.var_layout(crit_idx).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::SetBitmask { universe },
        } => assert_eq!(universe.len(), 3),
        other => panic!("expected recursive crit bitmask, got {other:?}"),
    }
}

#[test]
fn test_malformed_network_bound_does_not_mark_sequence_proven() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryMalformedNetworkProof ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {1, 2}
\* This is only one concrete channel, not a universally quantified path.
BadNetworkBound == Len(network[1][1]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("BadNetworkBound".to_string());
    let mut checker = ModelChecker::new(&module, &config);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![observed_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for malformed bound");
    assert!(
        !layout.supports_flat_primary(),
        "non-universal channel bound must not prove all network[p][q] capacities"
    );
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence { bound, max_len, .. } => {
                    assert_eq!(*bound, SequenceBoundEvidence::Observed);
                    assert_eq!(*max_len, 1);
                }
                other => panic!("expected network channel sequence layout, got {other:?}"),
            },
            other => panic!("expected nested network function layout, got {other:?}"),
        },
        other => panic!("expected recursive network layout, got {other:?}"),
    }
}

#[test]
fn test_subset_domain_network_bound_does_not_mark_sequence_proven() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimarySubsetDomainNetworkProof ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {1, 2}
\* This ranges over SUBSET Proc, so it must not prove every homogeneous network row.
BadSubsetDomainBound == \A s \in SUBSET Proc, q \in Proc : Len(network[s][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("BadSubsetDomainBound".to_string());
    let mut checker = ModelChecker::new(&module, &config);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![observed_network_value()]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for subset-domain bound");
    assert!(
        !layout.supports_flat_primary(),
        "SUBSET-domain proof must not make the recursive sequence primary-safe"
    );
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence { bound, max_len, .. } => {
                    assert_eq!(*bound, SequenceBoundEvidence::Observed);
                    assert_eq!(*max_len, 1);
                }
                other => panic!("expected network channel sequence layout, got {other:?}"),
            },
            other => panic!("expected nested network function layout, got {other:?}"),
        },
        other => panic!("expected recursive network layout, got {other:?}"),
    }
}

#[test]
fn test_invalid_capacity_domains_do_not_mark_sequence_proven() {
    let cases = [
        (
            "FlatPrimaryPartialLiteralDomainProof",
            r#"BadBound == \A p \in {1}, q \in Proc : Len(network[p][q]) <= 3"#,
            "partial literal domain",
        ),
        (
            "FlatPrimaryProperSubsetAliasDomainProof",
            r#"SomeProc == {1}
BadBound == \A p \in SomeProc, q \in Proc : Len(network[p][q]) <= 3"#,
            "proper-subset alias domain",
        ),
        (
            "FlatPrimarySetMinusUnknownAliasDomainProof",
            r#"SomeProc == Proc \ Unknown
BadBound == \A p \in SomeProc, q \in Proc : Len(network[p][q]) <= 3"#,
            "set-minus alias with unresolved RHS",
        ),
        (
            "FlatPrimaryLiteralDomainProof",
            r#"BadBound == \A p \in {1, 2}, q \in Proc : Len(network[p][q]) <= 3"#,
            "literal domain",
        ),
        (
            "FlatPrimaryRangeDomainProof",
            r#"BadBound == \A p \in 1..2, q \in Proc : Len(network[p][q]) <= 3"#,
            "range domain",
        ),
        (
            "FlatPrimaryUnknownDomainProof",
            r#"BadBound == \A p \in Unknown, q \in Proc : Len(network[p][q]) <= 3"#,
            "arbitrary identifier domain",
        ),
        (
            "FlatPrimaryProperSubsetDomainProof",
            r#"BadBound == \A p \in Proc \ {1}, q \in Proc : Len(network[p][q]) <= 3"#,
            "proper-subset domain",
        ),
        (
            "FlatPrimaryDiagonalDomainProof",
            r#"BadBound == \A p \in Proc : Len(network[p][p]) <= 3"#,
            "diagonal-only domain",
        ),
        (
            "FlatPrimaryShadowedProcDomainProof",
            r#"BadBound == \A Proc \in {1, 2} : \A p, q \in Proc : Len(network[p][q]) <= 3"#,
            "shadowed domain operator",
        ),
        (
            "FlatPrimaryShadowedNetworkDomainProof",
            r#"BadBound == \A network \in Proc, p \in Proc, q \in Proc : Len(network[p][q]) <= 3"#,
            "bound variable shadows state variable",
        ),
        (
            "FlatPrimaryNestedShadowedDomainProof",
            r#"BadBound == \A p \in Proc : \A p \in SUBSET Proc, q \in Proc : Len(network[p][q]) <= 3"#,
            "nested shadowed bound variable",
        ),
    ];

    for (module_name, bad_bound, message) in cases {
        let source = format!(
            r#"
---- MODULE {module_name} ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {{1, 2}}
{bad_bound}
====
"#
        );
        let module = parse_module(&source);
        let mut config = Config::default();
        config.invariants.push("BadBound".to_string());
        let mut checker = ModelChecker::new(&module, &config);

        checker.infer_flat_state_layout(&ArrayState::from_values(vec![observed_network_value()]));

        let layout = checker
            .flat_state_layout()
            .expect("layout should be inferred for invalid capacity proof");
        assert_network_channel_bound_observed(layout, message);
    }
}

#[test]
fn test_state_variable_capacity_domain_does_not_mark_sequence_proven() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryStateVarDomainProof ----
EXTENDS Naturals, Sequences
VARIABLES network, active
Proc == {1, 2}
BadBound == \A p \in active, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("BadBound".to_string());
    let mut checker = ModelChecker::new(&module, &config);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![
        Value::SmallInt(1),
        observed_network_value(),
    ]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for state-domain capacity proof");
    assert_network_channel_bound_observed_at(layout, 1, "state-variable domain");
}

#[test]
fn test_typeok_direct_domains_prove_replacement_aware_mcl_element_layout() {
    let cases = [
        (
            "FlatPrimaryLiteralTypeDomainProof",
            r#"MCTypeOK == network \in [{1, 2} -> [{1, 2} -> Seq(Message)]]"#,
            "literal TypeOK domains",
        ),
        (
            "FlatPrimaryRangeTypeDomainProof",
            r#"MCTypeOK == network \in [1..2 -> [1..2 -> Seq(Message)]]"#,
            "range TypeOK domains",
        ),
    ];

    for (module_name, replacement_type_ok, message) in cases {
        let source = format!(
            r#"
---- MODULE {module_name} ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {{1, 2}}
Message == {{
    [type |-> "req", clock |-> 1],
    [type |-> "ack", clock |-> 0],
    [type |-> "rel", clock |-> 0]
}}
TypeOK == network \in [Proc \ {{1}} -> [Proc -> Seq(Message)]]
{replacement_type_ok}
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#
        );
        let module = parse_module(&source);
        let mut config = Config::default();
        config.add_constant(
            "TypeOK".to_string(),
            ConstantValue::Replacement("MCTypeOK".to_string()),
        );
        config.invariants.push("TypeOK".to_string());
        config.invariants.push("BoundedNetwork".to_string());
        let mut checker = ModelChecker::new(&module, &config);
        bind_constants_from_config(&mut checker.ctx, &config).expect("config constants bind");
        precompute_constant_operators(&mut checker.ctx);

        checker.infer_flat_state_layout(&ArrayState::from_values(vec![empty_network_value()]));

        let layout = checker
            .flat_state_layout()
            .expect("layout should be inferred for direct-domain TypeOK proof");
        assert!(
            layout.supports_flat_primary(),
            "{message}: replacement-routed direct domains should prove sequence element layout"
        );
        assert!(
            checker.is_flat_state_primary(),
            "{message}: direct-domain TypeOK plus BoundedNetwork should activate flat_state_primary"
        );
        match &layout.var_layout(0).unwrap().kind {
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction { value_layout, .. },
            } => match value_layout.as_ref() {
                FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                    FlatValueLayout::Sequence {
                        bound,
                        max_len,
                        element_layout,
                    } => {
                        assert_eq!(*max_len, 3, "{message}");
                        assert_eq!(
                            *bound,
                            SequenceBoundEvidence::ProvenInvariantWithElementLayout {
                                invariant: Arc::from("BoundedNetwork"),
                                element_invariant: Arc::from("TypeOK"),
                            },
                            "{message}"
                        );
                        assert_message_record_layout(element_layout, message);
                    }
                    other => {
                        panic!("{message}: expected network channel sequence layout, got {other:?}")
                    }
                },
                other => {
                    panic!("{message}: expected nested network function layout, got {other:?}")
                }
            },
            other => panic!("{message}: expected recursive network layout, got {other:?}"),
        }
    }
}

#[test]
fn test_invalid_typeok_domains_do_not_prove_mcl_element_layout() {
    let cases = [
        (
            "FlatPrimaryUnknownTypeDomainProof",
            r#"TypeOK == network \in [Unknown -> [Proc -> Seq(Message)]]"#,
            "arbitrary identifier TypeOK domain",
        ),
        (
            "FlatPrimaryStateVarTypeDomainProof",
            r#"TypeOK == network \in [active -> [Proc -> Seq(Message)]]"#,
            "state-variable TypeOK domain",
        ),
        (
            "FlatPrimaryProperSubsetAliasTypeDomainProof",
            r#"SomeProc == {1}
TypeOK == network \in [SomeProc -> [Proc -> Seq(Message)]]"#,
            "proper-subset alias TypeOK domain",
        ),
        (
            "FlatPrimarySetMinusUnknownAliasTypeDomainProof",
            r#"SomeProc == Proc \ Unknown
TypeOK == network \in [SomeProc -> [Proc -> Seq(Message)]]"#,
            "set-minus alias TypeOK domain with unresolved RHS",
        ),
        (
            "FlatPrimaryProperSubsetTypeDomainProof",
            r#"TypeOK == network \in [Proc \ {1} -> [Proc -> Seq(Message)]]"#,
            "proper-subset TypeOK domain",
        ),
    ];

    for (module_name, type_ok, message) in cases {
        let source = format!(
            r#"
---- MODULE {module_name} ----
EXTENDS Naturals, Sequences
VARIABLES network, active
Proc == {{1, 2}}
Message == {{
    [type |-> "req", clock |-> 1],
    [type |-> "ack", clock |-> 0],
    [type |-> "rel", clock |-> 0]
}}
{type_ok}
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#
        );
        let module = parse_module(&source);
        let mut config = Config::default();
        config.invariants.push("TypeOK".to_string());
        config.invariants.push("BoundedNetwork".to_string());
        let mut checker = ModelChecker::new(&module, &config);
        precompute_constant_operators(&mut checker.ctx);

        checker.infer_flat_state_layout(&ArrayState::from_values(vec![
            Value::SmallInt(1),
            observed_network_value(),
        ]));

        let layout = checker
            .flat_state_layout()
            .expect("layout should be inferred for invalid TypeOK proof");
        assert!(
            !layout.supports_flat_primary(),
            "{message}: invalid TypeOK domain must not prove sequence element layout"
        );
        assert!(
            !checker.is_flat_state_primary(),
            "{message}: invalid TypeOK domain must not activate flat_state_primary"
        );
        assert_network_channel_capacity_only_at(layout, 1, message);
    }
}

#[test]
fn test_quantified_element_only_typeok_does_not_prove_parent_sequence_domains() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryQuantifiedElementOnlyTypeOK ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {1, 2}
Message == {
    [type |-> "req", clock |-> 1],
    [type |-> "ack", clock |-> 0],
    [type |-> "rel", clock |-> 0]
}
TypeOK == \A p, q \in Proc : network[p][q] \in Seq(Message)
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("TypeOK".to_string());
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    precompute_constant_operators(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![
        empty_sequence_network_value(),
    ]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for element-only TypeOK");
    assert_sequence_network_parent_bounds_observed(layout, "element-only quantified TypeOK");
    assert!(
        !checker.is_flat_state_primary(),
        "element-only quantified TypeOK must not activate flat_state_primary"
    );
}

#[test]
fn test_replacement_routed_fixed_domain_typeok_promotes_sequence_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryReplacementFixedDomainSequence ----
EXTENDS Naturals, Sequences
CONSTANT Proc
VARIABLE clock
MCProc == {1, 2, 3}
TypeOK == clock \in [Proc -> Nat]
====
"#,
    );
    let mut config = Config::default();
    config.add_constant(
        "Proc".to_string(),
        ConstantValue::Replacement("MCProc".to_string()),
    );
    config.invariants.push("TypeOK".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    bind_constants_from_config(&mut checker.ctx, &config).expect("config constants bind");
    precompute_constant_operators(&mut checker.ctx);
    promote_env_constants_to_precomputed(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![Value::Seq(Arc::new(
        SeqValue::from_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]),
    ))]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for replacement-routed fixed-domain TypeOK");
    assert_fixed_int_sequence_layout(layout, 3, "replacement-routed fixed-domain TypeOK");
    assert!(
        checker.is_flat_state_primary(),
        "replacement-routed fixed-domain sequence layout should activate flat_state_primary"
    );
}

#[test]
fn test_empty_fixed_domain_typeok_does_not_promote_sequence_layout() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryEmptyFixedDomainSequence ----
EXTENDS Naturals, Sequences
VARIABLE clock
Empty == {}
TypeOK == clock \in [Empty -> Nat]
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("TypeOK".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    precompute_constant_operators(&mut checker.ctx);

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![Value::Seq(Arc::new(
        SeqValue::from_vec(Vec::new()),
    ))]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for empty fixed-domain TypeOK");
    assert!(
        !layout.supports_flat_primary(),
        "empty fixed-domain TypeOK must not make a sequence primary-safe"
    );
    assert!(
        !checker.is_flat_state_primary(),
        "empty fixed-domain TypeOK must not activate flat_state_primary"
    );
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::Sequence { bound, .. },
        } => assert_eq!(
            *bound,
            SequenceBoundEvidence::Observed,
            "empty fixed-domain evidence should be rejected"
        ),
        other => panic!("expected recursive sequence layout, got {other:?}"),
    }
}

#[test]
fn test_fixed_domain_typeok_range_must_prove_observed_element_layout() {
    let cases = [
        (
            "FlatPrimaryUnknownFixedDomainRange",
            r#"TypeOK == clock \in [Proc -> Unknown]"#,
            "unknown fixed-domain range",
        ),
        (
            "FlatPrimaryMismatchedBooleanFixedDomainRange",
            r#"TypeOK == clock \in [Proc -> BOOLEAN]"#,
            "mismatched BOOLEAN fixed-domain range",
        ),
    ];

    for (module_name, type_ok, message) in cases {
        let source = format!(
            r#"
---- MODULE {module_name} ----
EXTENDS Naturals, Sequences
VARIABLE clock
Proc == {{1, 2}}
{type_ok}
====
"#
        );
        let module = parse_module(&source);
        let mut config = Config::default();
        config.invariants.push("TypeOK".to_string());
        let mut checker = ModelChecker::new(&module, &config);
        precompute_constant_operators(&mut checker.ctx);

        checker.infer_flat_state_layout(&ArrayState::from_values(vec![Value::Seq(Arc::new(
            SeqValue::from_vec(vec![Value::SmallInt(1), Value::SmallInt(1)]),
        ))]));

        let layout = checker
            .flat_state_layout()
            .expect("layout should be inferred for fixed-domain range mismatch");
        assert_single_sequence_bound_observed(layout, message);
        assert!(
            !checker.is_flat_state_primary(),
            "{message}: fixed-domain range mismatch must not activate flat_state_primary"
        );
    }
}

#[test]
fn test_broad_fixed_domain_typeok_range_proves_sequence_primary_safe() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryBroadFixedDomainRange ----
EXTENDS Naturals, Sequences
VARIABLE clock
TypeOK == clock \in [1..64 -> Nat]
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("TypeOK".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    let values = (1..=64).map(|_| Value::SmallInt(1)).collect();

    checker.infer_flat_state_layout(&ArrayState::from_values(vec![Value::Seq(Arc::new(
        SeqValue::from_vec(values),
    ))]));

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred for broad fixed-domain TypeOK");
    assert!(
        layout.supports_flat_primary(),
        "broad fixed-domain TypeOK with scalar range should remain primary-safe"
    );
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout:
                FlatValueLayout::Sequence {
                    bound,
                    max_len,
                    element_layout,
                },
        } => {
            assert_eq!(*max_len, 64);
            assert_eq!(
                *bound,
                SequenceBoundEvidence::FixedDomainTypeLayout {
                    invariant: Arc::from("TypeOK")
                }
            );
            assert_eq!(
                element_layout.as_ref(),
                &FlatValueLayout::Scalar(SlotType::Int)
            );
        }
        other => panic!("expected broad recursive sequence layout, got {other:?}"),
    }
    assert!(
        checker.is_flat_state_primary(),
        "broad fixed-domain TypeOK should activate flat_state_primary"
    );
}

#[test]
fn test_empty_network_wavefront_channels_inherit_proven_bound_but_not_primary_safe() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryEmptyBoundedNetworkProof ----
EXTENDS Naturals, Sequences
VARIABLE network
Proc == {1, 2}
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3
====
"#,
    );
    let mut config = Config::default();
    config.invariants.push("BoundedNetwork".to_string());
    let mut checker = ModelChecker::new(&module, &config);
    let states = vec![
        ArrayState::from_values(vec![empty_network_value()]),
        ArrayState::from_values(vec![observed_network_value()]),
    ];

    checker.infer_flat_state_layout_from_wavefront(&states);

    let layout = checker
        .flat_state_layout()
        .expect("layout should be inferred from network wavefront");
    assert!(
        !layout.supports_flat_primary(),
        "empty channels can inherit proven capacity, but not primary safety for observed element shape"
    );
    assert!(!checker.is_flat_state_primary());
    match &layout.var_layout(0).unwrap().kind {
        VarLayoutKind::Recursive {
            layout: FlatValueLayout::IntFunction { value_layout, .. },
        } => match value_layout.as_ref() {
            FlatValueLayout::IntFunction { value_layout, .. } => match value_layout.as_ref() {
                FlatValueLayout::Sequence { bound, max_len, .. } => {
                    assert_eq!(*max_len, 3);
                    assert_eq!(
                        *bound,
                        SequenceBoundEvidence::ProvenInvariant {
                            invariant: Arc::from("BoundedNetwork")
                        }
                    );
                }
                other => panic!("expected network channel sequence layout, got {other:?}"),
            },
            other => panic!("expected nested network function layout, got {other:?}"),
        },
        other => panic!("expected recursive network layout, got {other:?}"),
    }
}

#[test]
fn test_flat_state_primary_rejects_fixed_layout_when_full_state_storage_active() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryFullStateGuard ----
VARIABLE rec
====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);

    checker.infer_flat_state_layout(&fixed_record_init_state());

    assert!(
        !checker.is_flat_state_primary(),
        "full-state storage must keep BFS out of the flat primary fingerprint domain"
    );
}

#[test]
fn test_flat_state_primary_rejects_fixed_layout_with_view_or_symmetry() {
    let module = parse_module(
        r#"
---- MODULE FlatPrimaryViewSymmetryGuard ----
VARIABLE rec
====
"#,
    );
    let config = Config::default();

    let mut view_checker = ModelChecker::new(&module, &config);
    view_checker.compiled.cached_view_name = Some("View".to_string());
    view_checker.infer_flat_state_layout(&fixed_record_init_state());
    assert!(
        !view_checker.is_flat_state_primary(),
        "VIEW runs must stay out of flat_state_primary"
    );

    let mut symmetry_checker = ModelChecker::new(&module, &config);
    symmetry_checker
        .symmetry
        .perms
        .push(FuncValue::from_sorted_entries(Vec::<(Value, Value)>::new()));
    symmetry_checker.infer_flat_state_layout(&fixed_record_init_state());
    assert!(
        !symmetry_checker.is_flat_state_primary(),
        "SYMMETRY runs must stay out of flat_state_primary"
    );
}

/// #3125 regression: a zero-arg wrapper (`JsonInv`) that transitively references
/// a state-level operator (`Inv`) must NOT be precomputed. The old shallow gate
/// missed this because it only checked for direct `Expr::StateVar` nodes.
#[test]
fn test_precompute_skips_transitive_state_wrapper() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    // Inv == x = 0  (state-level: references state variable x)
    let inv_body = Expr::Eq(
        Box::new(Spanned::dummy(Expr::StateVar(
            "x".to_string(),
            0,
            intern_name("x"),
        ))),
        Box::new(Spanned::dummy(Expr::Int(0.into()))),
    );
    ctx.define_op("Inv".to_string(), make_op("Inv", inv_body));

    // JsonInv == Inv  (wrapper — body is just Ident("Inv"))
    let json_inv_body = Expr::Ident("Inv".to_string(), intern_name("Inv"));
    ctx.define_op("JsonInv".to_string(), make_op("JsonInv", json_inv_body));

    precompute_constant_operators(&mut ctx);

    let name_id = intern_name("JsonInv");
    assert!(
        ctx.shared().precomputed_constants.get(&name_id).is_none(),
        "JsonInv transitively references state var x — must NOT be precomputed"
    );

    let inv_id = intern_name("Inv");
    assert!(
        ctx.shared().precomputed_constants.get(&inv_id).is_none(),
        "Inv directly references state var x — must NOT be precomputed"
    );
}

/// Genuine constant operators (no state dependency at any level) must still
/// be precomputed for O(1) lookup during BFS.
#[test]
fn test_precompute_keeps_true_constants() {
    let mut ctx = EvalCtx::new();

    // N == 3  (constant: pure integer literal)
    let n_body = Expr::Int(3.into());
    ctx.define_op("N".to_string(), make_op("N", n_body));

    precompute_constant_operators(&mut ctx);

    let name_id = intern_name("N");
    assert!(
        ctx.shared().precomputed_constants.get(&name_id).is_some(),
        "N is a pure constant — must be precomputed"
    );
}

/// A constant wrapper over a constant operator should still be precomputed.
#[test]
fn test_precompute_keeps_transitive_constant_wrapper() {
    let mut ctx = EvalCtx::new();

    // Base == 42
    let base_body = Expr::Int(42.into());
    ctx.define_op("Base".to_string(), make_op("Base", base_body));

    // Wrapper == Base  (transitively constant)
    let wrapper_body = Expr::Ident("Base".to_string(), intern_name("Base"));
    ctx.define_op("Wrapper".to_string(), make_op("Wrapper", wrapper_body));

    precompute_constant_operators(&mut ctx);

    let base_id = intern_name("Base");
    assert!(
        ctx.shared().precomputed_constants.get(&base_id).is_some(),
        "Base is constant — must be precomputed"
    );

    let wrapper_id = intern_name("Wrapper");
    assert!(
        ctx.shared()
            .precomputed_constants
            .get(&wrapper_id)
            .is_some(),
        "Wrapper transitively references only constants — must be precomputed"
    );
}

#[test]
fn test_compile_action_bytecode_prunes_unsafe_and_unrewriteable_actions() {
    let module = parse_module(
        r#"
---- MODULE PrepareActionBytecodePrune ----
EXTENDS Naturals

VARIABLES x, y

Good ==
    /\ x' = x + 1
    /\ y' = y

UnsafeCrossPrime ==
    /\ y' = y + 1
    /\ x' = y'

ValidatorOverlapForward ==
    /\ UNCHANGED x
    /\ x' = x + 1
    /\ y' = y

ValidatorOverlapBackward ==
    /\ x' = x + 1
    /\ UNCHANGED x
    /\ y' = y

NoRewriteGuard ==
    /\ x < 10
    /\ y < 10

====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    seed_split_action_meta(
        &mut checker,
        &[
            "Good",
            "UnsafeCrossPrime",
            "ValidatorOverlapForward",
            "ValidatorOverlapBackward",
            "NoRewriteGuard",
        ],
    );

    checker.compile_action_bytecode();

    let compiled = checker
        .action_bytecode
        .as_ref()
        .expect("Good should remain in action_bytecode after pruning invalid actions");

    assert!(
        compiled.op_indices.contains_key("Good"),
        "safe actions should remain available for next-state JIT compilation",
    );
    assert!(
        !compiled.op_indices.contains_key("UnsafeCrossPrime"),
        "unsafe actions must be pruned from action_bytecode",
    );
    assert!(
        !compiled.op_indices.contains_key("NoRewriteGuard"),
        "actions with no rewrite must be pruned from action_bytecode",
    );
    assert!(
        !compiled.op_indices.contains_key("ValidatorOverlapForward"),
        "validator-rejected actions must be pruned from action_bytecode",
    );
    assert!(
        !compiled.op_indices.contains_key("ValidatorOverlapBackward"),
        "validator-rejected actions must be pruned from action_bytecode",
    );
    assert_eq!(
        compiled.failed.len(),
        4,
        "unsafe, validator-rejected, and no-rewrite actions should be surfaced as failures",
    );

    assert_failed_message_contains(
        compiled,
        "UnsafeCrossPrime",
        "unsafe next-state transform: prime-tainted RHS",
    );
    assert_failed_message_contains(
        compiled,
        "ValidatorOverlapForward",
        "unsafe next-state transform: primed var 0 is both written and UNCHANGED",
    );
    assert_failed_message_contains(
        compiled,
        "ValidatorOverlapBackward",
        "unsafe next-state transform: primed var 0 is both written and UNCHANGED",
    );
    assert_failed_message_contains(
        compiled,
        "NoRewriteGuard",
        "no safe next-state rewrite found",
    );
}

#[test]
fn test_compile_action_bytecode_prunes_transitive_prime_helpers() {
    let module = parse_module(
        r#"
---- MODULE PrepareActionBytecodeTransitiveCallees ----
EXTENDS Naturals

VARIABLES x, y

SafeValue ==
    x + 1

PrimeValue ==
    x'

PrimeModeCheck ==
    UNCHANGED (x + 1)

SafeWrapped ==
    /\ x' = SafeValue
    /\ y' = y

HiddenPrimeWrapped ==
    /\ x' = PrimeValue
    /\ y' = y

HiddenPrimeModeWrapped ==
    /\ x' = x + 1
    /\ y' = y
    /\ PrimeModeCheck

====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    seed_split_action_meta(
        &mut checker,
        &[
            "SafeWrapped",
            "HiddenPrimeWrapped",
            "HiddenPrimeModeWrapped",
        ],
    );

    checker.compile_action_bytecode();

    let compiled = checker
        .action_bytecode
        .as_ref()
        .expect("SafeWrapped should remain in action_bytecode after transitive pruning");

    assert!(
        compiled.op_indices.contains_key("SafeWrapped"),
        "actions that only reach pure helpers should remain eligible",
    );
    assert!(
        !compiled.op_indices.contains_key("HiddenPrimeWrapped"),
        "actions reaching helper callees with LoadPrime must be pruned",
    );
    assert!(
        !compiled.op_indices.contains_key("HiddenPrimeModeWrapped"),
        "actions reaching helper callees with SetPrimeMode must be pruned",
    );
    assert_eq!(
        compiled.failed.len(),
        2,
        "only the transitive helper violations should surface as failures",
    );

    assert_failed_message_contains(
        compiled,
        "HiddenPrimeWrapped",
        "unsafe next-state transform: reachable callee",
    );
    assert_failed_message_contains(compiled, "HiddenPrimeWrapped", "contains LoadPrime");
    assert_failed_message_contains(
        compiled,
        "HiddenPrimeModeWrapped",
        "unsafe next-state transform: reachable callee",
    );
    assert_failed_message_contains(compiled, "HiddenPrimeModeWrapped", "contains SetPrimeMode");
}

#[test]
fn test_compile_action_bytecode_prunes_multi_hop_prime_helpers() {
    let module = parse_module(
        r#"
---- MODULE PrepareActionBytecodeMultiHopCallees ----
EXTENDS Naturals

VARIABLES x, y

SafeLeaf ==
    x + 1

SafeMid ==
    SafeLeaf

PrimeLeaf ==
    x'

PrimeMid ==
    PrimeLeaf

PrimeModeLeaf ==
    UNCHANGED (x + 1)

PrimeModeMid ==
    PrimeModeLeaf

SafeWrapped ==
    /\ x' = SafeMid
    /\ y' = y

HiddenPrimeWrapped ==
    /\ x' = PrimeMid
    /\ y' = y

HiddenPrimeModeWrapped ==
    /\ x' = x + 1
    /\ y' = y
    /\ PrimeModeMid

====
"#,
    );
    let config = Config::default();
    let mut checker = ModelChecker::new(&module, &config);
    seed_split_action_meta(
        &mut checker,
        &[
            "SafeWrapped",
            "HiddenPrimeWrapped",
            "HiddenPrimeModeWrapped",
        ],
    );

    checker.compile_action_bytecode();

    let compiled = checker
        .action_bytecode
        .as_ref()
        .expect("SafeWrapped should remain in action_bytecode after multi-hop pruning");

    assert!(
        compiled.op_indices.contains_key("SafeWrapped"),
        "actions that only reach pure helper chains should remain eligible",
    );
    assert!(
        !compiled.op_indices.contains_key("HiddenPrimeWrapped"),
        "actions reaching multi-hop helper chains with LoadPrime must be pruned",
    );
    assert!(
        !compiled.op_indices.contains_key("HiddenPrimeModeWrapped"),
        "actions reaching multi-hop helper chains with SetPrimeMode must be pruned",
    );
    assert_eq!(
        compiled.failed.len(),
        2,
        "only the multi-hop helper violations should surface as failures",
    );

    assert_failed_message_contains(
        compiled,
        "HiddenPrimeWrapped",
        "unsafe next-state transform: reachable callee",
    );
    assert_failed_message_contains(compiled, "HiddenPrimeWrapped", "contains LoadPrime");
    assert_failed_message_contains(
        compiled,
        "HiddenPrimeModeWrapped",
        "unsafe next-state transform: reachable callee",
    );
    assert_failed_message_contains(compiled, "HiddenPrimeModeWrapped", "contains SetPrimeMode");
}
