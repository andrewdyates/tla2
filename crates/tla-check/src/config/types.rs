// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core configuration types: Config, TerminalSpec, ConstantValue, ConfigError.

use std::collections::HashMap;
use std::fmt;

use super::init_mode::InitMode;

/// Execution strategy for temporal liveness checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LivenessExecutionMode {
    /// Existing path: reuse the BFS-cached system graph during post-BFS liveness.
    #[default]
    Full,
    /// Regenerate system successors lazily during product exploration.
    OnTheFly,
}

impl LivenessExecutionMode {
    #[must_use]
    pub fn uses_on_the_fly(self) -> bool {
        matches!(self, Self::OnTheFly)
    }
}

/// A parsed TLC configuration
#[derive(Debug, Clone)]
pub struct Config {
    /// Initial state predicate name
    pub init: Option<String>,
    /// Next-state relation name
    pub next: Option<String>,
    /// Invariants to check (safety properties)
    pub invariants: Vec<String>,
    /// Trace invariants (Apalache-style): operators that take `Seq(Record)`.
    ///
    /// Each operator is called at every BFS state with the trace (as a sequence
    /// of state records) leading to that state. If it returns FALSE, a violation
    /// is reported. Part of #3752.
    pub trace_invariants: Vec<String>,
    /// Temporal properties to check
    pub properties: Vec<String>,
    /// Constant assignments (name -> expression string)
    pub constants: HashMap<String, ConstantValue>,
    /// Constant assignment order as encountered while parsing the config file.
    ///
    /// TLC's ModelValue ordering uses first-seen semantics (UniqueString token order).
    /// For config-defined model values, we approximate this by binding constants in
    /// config-file order rather than `HashMap` iteration order.
    pub constants_order: Vec<String>,
    /// Module-scoped overrides: module_name -> (lhs -> rhs)
    ///
    /// Parsed from TLC syntax: `CONSTANT Lhs <- [Mod] Rhs` (also accepts no-space: `[Mod]Rhs`).
    ///
    /// These apply only within the referenced module scope, matching TLC's
    /// `ModelConfig.modOverrides` behavior.
    pub module_overrides: HashMap<String, HashMap<String, String>>,
    /// Module-scoped assignments: module_name -> (lhs -> value_string)
    ///
    /// Parsed from TLC syntax: `CONSTANT Lhs = [Mod] Value` (also accepts no-space: `[Mod]Value`).
    ///
    /// TLC applies these to operator definitions' bodies within the specified module.
    pub module_assignments: HashMap<String, HashMap<String, String>>,
    /// Symmetry set name
    pub symmetry: Option<String>,
    /// State constraints
    pub constraints: Vec<String>,
    /// Action constraints
    pub action_constraints: Vec<String>,
    /// Specification (replaces INIT/NEXT with a temporal formula)
    pub specification: Option<String>,
    /// Whether to check for deadlock (default: true)
    pub check_deadlock: bool,
    /// Whether CHECK_DEADLOCK was explicitly set in the config file.
    ///
    /// This records config provenance only. TLA2 follows TLC here: PROPERTY /
    /// SPECIFICATION shape does not implicitly disable deadlock checking.
    /// Callers should combine this with `check_deadlock` and CLI flags when they
    /// need to explain or preserve deadlock-selection precedence.
    pub check_deadlock_explicit: bool,
    /// VIEW expression for fingerprinting (optional state abstraction)
    ///
    /// When set, the fingerprint of a state is computed by evaluating this
    /// expression rather than using all state variables. This can dramatically
    /// reduce state space when some variables don't affect correctness.
    pub view: Option<String>,
    /// Terminal states specification (states that should not be considered deadlocks)
    ///
    /// When set, states matching these conditions are considered intentional
    /// termination points, not deadlocks. This is useful for specs like SAT
    /// solvers where reaching "SAT" or "UNSAT" is a successful termination.
    pub terminal: Option<TerminalSpec>,
    /// Postcondition operator (called after simulation/generation completes)
    ///
    /// Used in simulation mode to verify aggregate statistics. For example,
    /// SimKnuthYao uses POSTCONDITION to run a ChiSquare test on generated traces.
    /// Ignored during normal model checking.
    pub postcondition: Option<String>,
    /// Alias operator for error trace output formatting.
    ///
    /// When set, TLC (and TLA2) evaluates this operator for each state in
    /// counterexample traces. If the result is a record, its fields replace
    /// the raw state variables in the trace output.
    ///
    /// Part of #3012.
    pub alias: Option<String>,
    /// Mode for initial state enumeration.
    ///
    /// Controls whether to use brute-force enumeration or z4-based SMT solving.
    /// Environment variables TLA2_USE_Z4 and TLA2_FORCE_Z4 can override this.
    /// Default: Auto (use z4 if analysis recommends it).
    pub init_mode: InitMode,
    /// Enable Partial Order Reduction (POR).
    ///
    /// When enabled, the checker computes a static independence matrix from
    /// action variable-access patterns and uses ample-set selection to reduce
    /// the number of explored successors. Supported in both sequential and
    /// parallel modes. Each parallel worker computes its own ample set
    /// independently using the shared read-only independence matrix.
    /// Default: false.
    /// Part of #541, #3706.
    pub por_enabled: bool,
    /// Override auto-POR behavior.
    ///
    /// When `Some(false)`, auto-POR is disabled regardless of the
    /// `TLA2_AUTO_POR` env var. When `None` (default), auto-POR follows the
    /// env var (enabled by default). This field exists primarily for tests
    /// that need a deterministic "no POR" baseline without relying on env
    /// var state.
    ///
    /// Part of #3993.
    pub auto_por: Option<bool>,
    /// Cross-check fully JIT-evaluated invariants against the interpreter.
    ///
    /// When enabled, the checker runs the interpreter alongside the JIT fast
    /// path, reports mismatches, and uses the interpreter result as canonical.
    /// Default: false.
    pub jit_verify: bool,
    /// Liveness execution strategy.
    ///
    /// This is a runtime/CLI selection, not a TLC config-file directive.
    /// Default: `Full`.
    pub liveness_execution: LivenessExecutionMode,
    /// Whether to use FlatState as the native BFS representation.
    ///
    /// When `None` (default), flat BFS is auto-detected: enabled when all
    /// state variables are scalar (i64-representable: Int, Bool, ModelValue)
    /// and the roundtrip verification passes. Set to `Some(true)` to force
    /// enable (equivalent to `TLA2_FLAT_BFS=1`) or `Some(false)` to force
    /// disable (equivalent to `TLA2_NO_FLAT_BFS=1`).
    ///
    /// Part of #4126: Auto-detect flat BFS for scalar specs.
    pub use_flat_state: Option<bool>,
    /// Whether to use the compiled BFS level loop (fused JIT path).
    ///
    /// When `None` (default), compiled BFS is auto-detected: enabled when
    /// all actions and invariants are JIT-compiled, the state layout is
    /// fully flat (all scalar), and the fused level function compiles
    /// successfully. Set to `Some(true)` to force enable (equivalent to
    /// `TLA2_COMPILED_BFS=1`) or `Some(false)` to force disable
    /// (equivalent to `TLA2_NO_COMPILED_BFS=1`).
    ///
    /// The fused level processes entire BFS frontiers in a single native
    /// function call, eliminating per-parent Rust-to-JIT boundary crossings.
    ///
    /// Part of #4171: End-to-end compiled BFS wiring.
    pub use_compiled_bfs: Option<bool>,
}

/// Specification for terminal states (states that are intentionally final)
///
/// Terminal states are states where the spec should not proceed further,
/// but which should NOT be reported as deadlocks.
#[derive(Debug, Clone)]
pub enum TerminalSpec {
    /// Terminal states defined by variable predicates: `TERMINAL state = "SAT"`
    /// Each entry is (variable_name, expected_value_string)
    Predicates(Vec<(String, String)>),
    /// Terminal states defined by a TLA+ operator: `TERMINAL IsTerminal`
    Operator(String),
}

impl Default for Config {
    fn default() -> Self {
        Self {
            init: None,
            next: None,
            invariants: Vec::new(),
            trace_invariants: Vec::new(),
            properties: Vec::new(),
            constants: HashMap::new(),
            constants_order: Vec::new(),
            module_overrides: HashMap::new(),
            module_assignments: HashMap::new(),
            symmetry: None,
            constraints: Vec::new(),
            action_constraints: Vec::new(),
            specification: None,
            check_deadlock: true, // TLC default is to check for deadlock
            check_deadlock_explicit: false, // Not explicitly set until parsed from config
            view: None,
            terminal: None,
            postcondition: None,
            alias: None,
            init_mode: InitMode::default(),
            por_enabled: false,
            auto_por: None,
            jit_verify: false,
            liveness_execution: LivenessExecutionMode::Full,
            use_flat_state: None,
            use_compiled_bfs: None,
        }
    }
}

/// A constant value in the configuration
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ConstantValue {
    /// Direct value assignment: CONSTANT N = 3
    Value(String),
    /// Model value: CONSTANT Procs <- [ model value ]
    ModelValue,
    /// Set of model values: CONSTANT Procs <- {p1, p2, p3}
    ModelValueSet(Vec<String>),
    /// Replacement operator: CONSTANT Op <- OtherOp
    Replacement(String),
}

impl fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstantValue::Value(v) => write!(f, "{}", v),
            ConstantValue::ModelValue => write!(f, "[ model value ]"),
            ConstantValue::ModelValueSet(vs) => {
                write!(f, "{{{}}}", vs.join(", "))
            }
            ConstantValue::Replacement(r) => write!(f, "<- {}", r),
        }
    }
}

/// Issue found during config field-relationship validation.
///
/// Returned by [`Config::validate()`]. All current issues are hard errors that
/// prevent model checking.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum ConfigValidationIssue {
    /// SPECIFICATION and INIT/NEXT are mutually exclusive directives.
    ///
    /// TLC rejects this combination in `ModelConfig.java`.
    #[error("SPECIFICATION and INIT/NEXT are mutually exclusive — use one or the other")]
    SpecificationWithInitNext,
}

impl ConfigValidationIssue {
    /// Returns `true` for issues that should block model checking.
    #[must_use]
    pub fn is_error(&self) -> bool {
        match self {
            ConfigValidationIssue::SpecificationWithInitNext => true,
        }
    }
}

/// Configuration parse error
///
/// Display format does NOT include "line N:" prefix — callers add their own
/// `"path:line: "` prefix for compiler-style diagnostics.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ConfigError {
    /// INIT directive without a predicate name.
    #[error("INIT requires a predicate name")]
    MissingInit { line: usize },
    /// NEXT directive without a relation name.
    #[error("NEXT requires a relation name")]
    MissingNext { line: usize },
    /// Invalid syntax for a recognized directive (CONSTANT, TERMINAL, etc.).
    #[error("Invalid {directive} syntax: {text}")]
    InvalidSyntax {
        line: usize,
        directive: &'static str,
        text: String,
    },
    /// Unrecognized config directive.
    #[error("Unknown directive: {text}")]
    UnknownDirective { line: usize, text: String },
}

impl ConfigError {
    /// Source line number (1-indexed) where the error occurred.
    pub fn line(&self) -> usize {
        match self {
            ConfigError::MissingInit { line }
            | ConfigError::MissingNext { line }
            | ConfigError::InvalidSyntax { line, .. }
            | ConfigError::UnknownDirective { line, .. } => *line,
        }
    }
}

impl Config {
    /// Create a new empty configuration
    pub fn new() -> Self {
        Self::default()
    }

    /// Helper to insert a constant while maintaining insertion order.
    pub(super) fn insert_constant(&mut self, name: String, value: ConstantValue) {
        if !self.constants.contains_key(&name) {
            self.constants_order.push(name.clone());
        }
        self.constants.insert(name, value);
    }

    /// Add a constant assignment, maintaining insertion order.
    ///
    /// Public API for CLI and programmatic config construction.
    /// Part of #3779.
    pub fn add_constant(&mut self, name: String, value: ConstantValue) {
        self.insert_constant(name, value);
    }
}
