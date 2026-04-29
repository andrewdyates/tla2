// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Data types for the refinement checking command.

use std::collections::BTreeMap;
use std::path::PathBuf;

use serde::Serialize;
use tla_core::ast::OperatorDef;

// ---------------------------------------------------------------------------
// Spec metadata
// ---------------------------------------------------------------------------

/// Extracted metadata from a TLA+ module: variables, operators, Init/Next.
#[derive(Debug, Clone)]
pub(super) struct SpecInfo {
    /// The module name (from the MODULE header).
    pub(super) module_name: String,
    /// Path to the source file.
    pub(super) file_path: PathBuf,
    /// Declared state variables (VARIABLES section).
    pub(super) variables: Vec<String>,
    /// All operator definitions keyed by name.
    pub(super) operators: BTreeMap<String, OperatorDef>,
    /// The `Init` operator definition, if found.
    pub(super) init_def: Option<OperatorDef>,
    /// The `Next` operator definition, if found.
    pub(super) next_def: Option<OperatorDef>,
}

// ---------------------------------------------------------------------------
// Refinement result types
// ---------------------------------------------------------------------------

/// Overall result of the refinement check.
#[derive(Debug, Clone, Serialize)]
pub(super) struct RefineResult {
    /// Whether the refinement check passed (no violations).
    pub(super) passed: bool,
    /// All violations found during the check.
    pub(super) violations: Vec<RefinementViolation>,
    /// Number of implementation states explored.
    pub(super) states_explored: usize,
    /// Number of implementation transitions explored.
    pub(super) transitions_explored: usize,
}

/// A single refinement violation.
#[derive(Debug, Clone, Serialize)]
pub(super) struct RefinementViolation {
    /// The kind of violation.
    pub(super) kind: ViolationKind,
    /// Human-readable description.
    pub(super) description: String,
    /// The implementation state where the violation occurred (if applicable).
    pub(super) impl_state: Option<BTreeMap<String, String>>,
    /// The mapped abstract state (if computed).
    pub(super) mapped_abstract_state: Option<BTreeMap<String, String>>,
    /// Trace of implementation states leading to the violation.
    pub(super) trace: Vec<TraceStep>,
    /// The step index in the trace where the violation occurred.
    pub(super) step_index: Option<usize>,
}

/// Classification of refinement violations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(super) enum ViolationKind {
    /// Abstract variables not covered by the refinement mapping.
    UnmappedVariables,
    /// An initial implementation state maps to an invalid abstract initial state.
    InitRefinement,
    /// An implementation transition does not correspond to any valid abstract
    /// transition (including stuttering).
    TransitionRefinement,
    /// The mapped abstract state violates an abstract invariant.
    InvariantViolation,
    /// A structural issue prevents checking (e.g., missing Init/Next).
    StructuralError,
    /// The refinement mapping itself is inconsistent or unparseable.
    MappingError,
}

/// A single step in a counterexample trace.
#[derive(Debug, Clone, Serialize)]
pub(super) struct TraceStep {
    /// Step index (0 = initial state).
    pub(super) index: usize,
    /// Variable assignments at this step.
    pub(super) state: BTreeMap<String, String>,
    /// The mapped abstract variable assignments (if computed).
    pub(super) abstract_state: Option<BTreeMap<String, String>>,
    /// Whether this step is a stuttering step (no abstract change).
    pub(super) is_stuttering: bool,
}

/// An abstract transition for comparison.
#[derive(Debug, Clone)]
pub(super) struct AbstractTransition {
    /// The pre-state of the abstract spec.
    pub(super) pre_state: BTreeMap<String, String>,
    /// The post-state of the abstract spec.
    pub(super) post_state: BTreeMap<String, String>,
}

/// Statistics collected during the refinement check.
#[derive(Debug, Clone, Serialize)]
pub(super) struct RefineStatistics {
    /// Number of implementation states explored.
    pub(super) impl_states_explored: usize,
    /// Number of implementation transitions explored.
    pub(super) impl_transitions_explored: usize,
    /// Number of violations found.
    pub(super) violations_found: usize,
    /// Wall-clock time in seconds.
    pub(super) elapsed_secs: f64,
    /// Number of refinement mapping entries.
    pub(super) mapping_entries: usize,
    /// Abstract variables not covered by the mapping.
    pub(super) unmapped_variables: Vec<String>,
}
