// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CLI argument schema: command definitions, output format types, and gating enums.

use std::path::PathBuf;

use clap::{Parser, Subcommand, ValueEnum};
use clap_complete::Shell;

/// Template for the `init` command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum InitTemplate {
    /// Simple spec with Init, Next, TypeOK (default).
    #[default]
    Basic,
    /// Multi-process spec with VARIABLE pc, messages, EXTENDS Sequences.
    Distributed,
    /// Mutual exclusion protocol template.
    Mutex,
    /// Cache coherence protocol template.
    Cache,
}

/// Output format for diagnose command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DiagnoseOutputFormat {
    /// Human-readable summary table (default)
    #[default]
    Human,
    /// Structured JSON output compatible with metrics/spec_coverage.json
    Json,
}

/// Differential oracle mode for `tla2 diagnose` (#4252 Stream 6).
///
/// The tree-walking interpreter is the permanent correctness oracle for every
/// compiled backend (LLVM2 today, tMIR/others later). `compare` runs both and
/// records divergences to `metrics/oracle_parity.json`. `fail-closed` also
/// exits non-zero on any divergence, making it the CI gate mode.
#[derive(Clone, Copy, Debug, Default, ValueEnum, PartialEq, Eq)]
pub(crate) enum DiagnoseOracleMode {
    /// No oracle run — interpreter only (default).
    #[default]
    Off,
    /// Run both interpreter and LLVM2, record divergences, do NOT fail the build.
    Compare,
    /// Run both and exit non-zero on any divergence (CI gate).
    #[value(name = "fail-closed")]
    FailClosed,
}

/// Which evaluation backend `tla2 check` should use (#4252 Stream 6).
///
/// `interpreter` is the default and the permanent correctness oracle.
/// `llvm2` is the native-compiled AOT path gated behind the `llvm2` feature;
/// when unavailable or not yet wired, selecting `llvm2` emits a JSON
/// `backend_unavailable` sentinel and exits with code 3 so the oracle harness
/// can classify the run as infra-gap rather than divergence.
#[derive(Clone, Copy, Debug, Default, ValueEnum, PartialEq, Eq)]
pub(crate) enum CheckBackend {
    /// Tree-walking interpreter (the oracle). Default.
    #[default]
    Interpreter,
    /// LLVM2-compiled path. Currently a stub — emits backend_unavailable.
    Llvm2,
}

/// Output format for bench command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum BenchOutputFormat {
    /// Human-readable table output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
    /// GitHub-Flavored Markdown table (for pasting into issues)
    Markdown,
}

/// Output format for profile command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ProfileOutputFormat {
    /// Human-readable profiling report with bars (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for diff command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DiffOutputFormat {
    /// Human-readable colored diff output (default)
    #[default]
    Human,
    /// Structured JSON output for tooling
    Json,
}

/// Input format for convert command
#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum ConvertFrom {
    /// TLA+ source file
    Tla,
    /// JSON AST
    Json,
    /// JSON trace output from `tla2 check --output json`
    Trace,
}

/// Output format for convert command
#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum ConvertTo {
    /// Structured JSON AST
    Json,
    /// TLA+ source
    Tla,
    /// GitHub-Flavored Markdown documentation
    Markdown,
    /// Aligned table of trace states
    Table,
}

/// Output format for repair command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum RepairOutputFormat {
    /// Human-readable repair suggestions (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Solver engine for the AIGER subcommand.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AigerEngine {
    /// SAT-based portfolio: IC3/PDR + BMC + k-induction (default, faster for most benchmarks).
    #[default]
    Sat,
    /// CHC-based: translates to CHC and uses z4-chc adaptive portfolio solver.
    Chc,
    /// BMC only: bounded model checking (finds bugs, cannot prove safety).
    Bmc,
    /// k-induction only: can prove safety for k-inductive properties.
    Kind,
    /// Strengthened k-induction: k-induction with auxiliary invariant discovery.
    /// Extends standard k-induction with single-literal invariant discovery,
    /// BMC-based confirmation, and counterexample-guided strengthening.
    KindStrengthened,
    /// IC3/PDR only: full invariant-based safety checking.
    Ic3,
}

/// Portfolio mode for the SAT engine.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AigerPortfolio {
    /// Default: conservative IC3 + BMC + k-induction (3 threads).
    #[default]
    Default,
    /// Full IC3 portfolio: 8 IC3 configs + BMC + k-induction (10 threads).
    Full,
    /// Competition: 13 IC3 configs + 3 BMC + k-induction (17 threads).
    Competition,
    /// Adaptive preset rotation: when a worker returns Unknown, restart it
    /// with the next preset and a rotated random seed (rIC3 PolyNexus port,
    /// #4309). Target: recover from stuck IC3 runs on hard benchmarks.
    Adaptive,
}

/// Output format for deps command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DepsOutputFormat {
    /// Indented text tree showing the dependency hierarchy (default)
    #[default]
    Tree,
    /// Graphviz DOT format for graph visualization
    Dot,
    /// Structured JSON output for tooling integration
    Json,
}

/// Output format for doc command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DocOutputFormat {
    /// GitHub-Flavored Markdown (default)
    #[default]
    Markdown,
    /// Self-contained HTML with CSS styling and navigation sidebar
    Html,
    /// Structured JSON output for tooling
    Json,
}

/// Output format for graph command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum GraphOutputFormat {
    /// Graphviz DOT format (default)
    #[default]
    Dot,
    /// Mermaid.js flowchart syntax for GitHub markdown rendering
    Mermaid,
    /// Structured JSON adjacency list for programmatic consumption
    Json,
}

/// Output format for snapshot command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SnapshotOutputFormat {
    /// Human-readable colored summary table (default)
    #[default]
    Human,
    /// Structured JSON regression report
    Json,
}

/// Output format for bisect command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum BisectOutputFormat {
    /// Human-readable progress and result output (default)
    #[default]
    Human,
    /// Structured JSON bisect report
    Json,
}

/// Output format for merge command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum MergeOutputFormat {
    /// Human-readable merged TLA+ source with optional conflict markers (default)
    #[default]
    Human,
    /// Structured JSON merge report
    Json,
}

/// Output format for thread-check command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ThreadCheckOutputFormat {
    /// Human-readable terminal output (default)
    #[default]
    Human,
    /// Structured JSON output (ConcurrentCheckResult)
    Json,
}

/// Output format for validate command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ValidateOutputFormat {
    /// Human-readable colored terminal output (default)
    #[default]
    Human,
    /// Structured JSON validation report
    Json,
}

/// Output format for coverage command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum CoverageOutputFormat {
    /// Human-readable table with ASCII bar chart (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for `tla2 trace view` command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TraceViewOutputFormat {
    /// Human-readable colored output with change markers (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
    /// Aligned columns table
    Table,
}

/// Output format for stats command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum StatsOutputFormat {
    /// Human-readable table output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// What kind of TLA+ entity to search for.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SearchKind {
    /// Find operator definitions matching a name pattern.
    #[default]
    Operator,
    /// Find variable declarations matching a pattern.
    Variable,
    /// Find constant declarations matching a pattern.
    Constant,
    /// Find expressions matching a text pattern in operator bodies.
    Expr,
    /// Find Next disjuncts (actions) matching a pattern.
    Action,
}

/// Output format for search command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SearchOutputFormat {
    /// Grep-like colored terminal output (default).
    #[default]
    Human,
    /// Structured JSON output.
    Json,
}

/// Output format for lint command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum LintOutputFormat {
    /// Human-readable colored terminal output (default)
    #[default]
    Human,
    /// Structured JSON output for IDE integration
    Json,
}

/// Minimum severity level for lint output
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum LintSeverityArg {
    /// Show warnings and above (default)
    #[default]
    Warning,
    /// Show all diagnostics including informational messages
    Info,
}

/// Output format for typecheck command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TypecheckOutputFormat {
    /// Human-readable text output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for explain command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ExplainOutputFormat {
    /// Human-readable step-by-step explanation (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for summary command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SummaryOutputFormat {
    /// Human-readable colored table (default)
    #[default]
    Human,
    /// Structured JSON array of results
    Json,
    /// CSV format for spreadsheets
    Csv,
}

/// Sort order for summary command
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SummarySortBy {
    /// Sort by spec name alphabetically (default)
    #[default]
    Name,
    /// Sort by wall-clock time (slowest first)
    Time,
    /// Sort by state count (most states first)
    States,
    /// Sort by status (errors first, then timeouts, then passes)
    Status,
}

/// Protocol template kind for `tla2 template`.
#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum TemplateKind {
    /// Peterson's mutual exclusion
    Mutex,
    /// Simple consensus with proposals and votes
    Consensus,
    /// MSI-like cache coherence protocol
    Cache,
    /// Bounded FIFO queue with producer/consumer
    Queue,
    /// Leader election in a ring
    Leader,
    /// Token passing ring protocol
    TokenRing,
}

/// Deadlock analysis mode for `tla2 deadlock`.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DeadlockMode {
    /// Static analysis only (fast, no model checking)
    #[default]
    Quick,
    /// Full model checking for deadlock states
    Full,
}

/// Output format for deadlock command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DeadlockOutputFormat {
    /// Human-readable output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for abstract command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AbstractOutputFormat {
    /// Human-readable structured text (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
    /// Mermaid state diagram
    Mermaid,
}

/// Detail level for abstract command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AbstractDetail {
    /// Just action names
    Brief,
    /// Actions + affected variables (default)
    #[default]
    Normal,
    /// Everything including expressions
    Full,
}

/// Output format for witness command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum WitnessOutputFormat {
    /// Human-readable step-by-step trace (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for compare command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum CompareOutputFormat {
    /// Diff-like colored output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for scope command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ScopeOutputFormat {
    /// Human-readable tree output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
    /// Graphviz DOT graph
    Dot,
}

/// Strategy for the constrain command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ConstrainStrategy {
    /// Suggest smallest constants that exercise all actions (default)
    #[default]
    Minimize,
    /// Generate incrementally larger configs (N=1, N=2, ...)
    Incremental,
    /// Detect and add SYMMETRY declarations
    Symmetric,
}

/// Output format for audit command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AuditOutputFormat {
    /// Human-readable scorecard (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Import source format for `tla2 import`.
#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum ImportFormat {
    /// JSON state machine description
    JsonStateMachine,
    /// Promela (SPIN) model
    Promela,
    /// Alloy specification
    Alloy,
}

/// Output format for symmetry command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SymmetryOutputFormat {
    /// Human-readable output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for partition command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum PartitionOutputFormat {
    /// Human-readable output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for sim-report command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SimReportOutputFormat {
    /// Human-readable table output (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for trace-gen command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TraceGenOutputFormat {
    /// Human-readable trace listing (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
    /// Informal Trace Format (Apalache-compatible)
    Itf,
}

/// Trace generation mode.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TraceGenMode {
    /// Find a trace reaching a state where a target predicate holds
    #[default]
    Target,
    /// Find a minimal set of traces covering every Next disjunct
    Coverage,
    /// Generate diverse random traces for testing
    Random,
}

/// Output format for inv-gen command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum InvGenOutputFormat {
    /// Human-readable summary with explanations (default)
    #[default]
    Human,
    /// Machine-readable JSON array of candidate invariants
    Json,
    /// TLA+ operator definitions ready to paste into a spec
    Tla,
}

/// Output format for action-graph command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ActionGraphOutputFormat {
    /// Human-readable summary (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
    /// GraphViz DOT format for visualization
    Dot,
}

/// Output format for refine command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum RefineOutputFormat {
    /// Human-readable summary (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for model-diff command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ModelDiffOutputFormat {
    /// Human-readable colored diff (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for state-filter command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum StateFilterOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for unfold command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum UnfoldOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for project command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ProjectOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for bound command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum BoundOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for slice command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SliceOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for reach command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ReachOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for compose command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ComposeOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for census command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum CensusOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for equiv command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum EquivOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for induct command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum InductOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for lasso command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum LassoOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for assume-guarantee command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AssumeGuaranteeOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for predicate-abs command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum PredicateAbsOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for sandbox command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SandboxOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for timeline command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TimelineOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for metric command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum MetricOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for scaffold command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ScaffoldOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for stutter command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum StutterOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for quorum command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum QuorumOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for fingerprint command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum FingerprintOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for normalize command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum NormalizeOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for countex command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum CountexOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for heatmap command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum HeatmapOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for protocol command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ProtocolOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for hierarchy command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum HierarchyOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for crossref command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum CrossrefOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for invariantgen command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum InvariantgenOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for drift command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DriftOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for safety command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SafetyOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for liveness-check command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum LivenesscheckOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for translate command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TranslateOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for tableau command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TableauOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for alphabet command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AlphabetOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for weight command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum WeightOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for absorb command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AbsorbOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for cluster command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ClusterOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for rename command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum RenameOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for reachset command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ReachsetOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for guard command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum GuardOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for symmetry-detect command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SymmetrydetectOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for deadlock-free command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DeadlockfreeOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for action-count command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ActioncountOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for const-check command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ConstcheckOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for spec-info command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SpecinfoOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for var-track command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum VartrackOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for cfg-gen command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum CfggenOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for dep-graph command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum DepgraphOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
    /// DOT graph format
    Dot,
}

/// Output format for init-count command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum InitcountOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for branch-factor command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum BranchfactorOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for state-graph command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum StategraphOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for predicate command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum PredicateOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for module-info command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ModuleinfoOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for op-arity command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum OparityOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for unused-var command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum UnusedvarOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for expr-count command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ExprcountOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for spec-size command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SpecsizeOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for const-list command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ConstlistOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for var-list command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum VarlistOutputFormat {
    /// Human-readable table (default)
    #[default]
    Human,
    /// Structured JSON output
    Json,
}

/// Output format for unused-const command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum UnusedconstOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for ast-depth command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum AstdepthOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for op-list command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum OplistOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for extends command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ExtendsOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for set-ops command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum SetopsOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for quant-count command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum QuantcountOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for prime-count command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum PrimecountOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for if-count command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum IfcountOutputFormat {
    #[default]
    Human,
    Json,
}

/// Output format for let-count command.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum LetcountOutputFormat {
    #[default]
    Human,
    Json,
}

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ChoosecountOutputFormat { #[default] Human, Json }

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum CasecountOutputFormat { #[default] Human, Json }

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum RecordopsOutputFormat { #[default] Human, Json }

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TemporalopsOutputFormat { #[default] Human, Json }
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum UnchangedOutputFormat { #[default] Human, Json }
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum EnabledOutputFormat { #[default] Human, Json }

/// Output format for model checking results
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum OutputFormat {
    /// Human-readable text output (default)
    #[default]
    Human,
    /// Structured JSON output for AI agents and automation
    Json,
    /// Streaming JSONL format (one JSON object per line)
    #[value(name = "jsonl", alias = "json-lines")]
    Jsonl,
    /// TLC "-tool" tagged output for Eclipse Toolbox compatibility
    #[value(name = "tlc-tool", alias = "tool")]
    TlcTool,
    /// Informal Trace Format (ITF) JSON for Apalache/TLA+ tooling interoperability
    ///
    /// Emits the full check result as an ITF JSON document to stdout.
    /// On error (invariant/property/liveness violation, deadlock), the counterexample
    /// trace is encoded in ITF format. On success, a minimal ITF document with an
    /// empty states array is emitted.
    Itf,
}

/// Format for counterexample traces
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TraceFormat {
    /// Human-readable text format (default)
    #[default]
    Text,
    /// GraphViz DOT format for visualization
    Dot,
    /// Informal Trace Format (ITF) JSON for Apalache/TLA+ tooling interoperability
    Itf,
}

/// Speculative type specialization mode for JIT Tier 2 recompilation.
///
/// Controls whether the JIT type profiler observes runtime types of state
/// variables during BFS warmup and builds a specialization plan for Tier 2
/// recompilation.
///
/// Part of #3989: JIT V2 Phase 6 speculative type specialization.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum TypeSpecializeArg {
    /// Enable type specialization when JIT is active and profiling detects
    /// monomorphic state variables (default).
    #[default]
    Auto,
    /// Always enable type specialization profiling (even without --jit).
    On,
    /// Disable type specialization entirely.
    Off,
}

/// Post-BFS liveness execution strategy.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum LivenessModeArg {
    /// Reuse the BFS-cached successor graph during post-BFS liveness.
    #[default]
    Full,
    /// Regenerate system successors lazily during product exploration.
    #[value(name = "on-the-fly", alias = "on_the_fly")]
    OnTheFly,
}

/// Maximum allowed soundness mode for this run (automation gate).
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub enum SoundnessGate {
    /// Require TLC-equivalent (claimed) semantics.
    #[default]
    Sound,
    /// Allow experimental engine paths.
    Experimental,
    /// Allow heuristic / incomplete engine paths.
    Heuristic,
}

/// Named verification strategy for multi-phase pipeline mode.
///
/// Part of #3723.
#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum StrategyArg {
    /// Fast feedback: RandomWalk + BMC (no exhaustive BFS).
    Quick,
    /// TLC-equivalent: RandomWalk + exhaustive BFS + liveness.
    Full,
    /// Adaptive: walk -> BMC -> k-induction -> PDR -> BFS with early exit.
    Auto,
}

/// Exploration mode for the `explore` subcommand.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ExploreModeArg {
    /// Interactive terminal REPL (default).
    #[default]
    Repl,
    /// HTTP JSON API server.
    Http,
}

/// Exploration engine for the `explore` subcommand.
///
/// Controls whether the server uses concrete-state enumeration or
/// symbolic SMT-based exploration. Part of #3751: Apalache Gap 3.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub(crate) enum ExploreEngineArg {
    /// Concrete-state exploration (default).
    #[default]
    Concrete,
    /// Symbolic SMT-based exploration (requires z4 feature).
    Symbolic,
}

#[derive(Debug, Parser)]
#[command(name = "tla", version, about = "TLA2 CLI")]
pub(crate) struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Debug, Subcommand)]
pub(crate) enum Command {
    /// Create a new TLA+ specification project from a template.
    ///
    /// Generates a `.tla` module file and a `.cfg` configuration file
    /// with boilerplate for the chosen template (basic, distributed,
    /// mutex, or cache).
    Init {
        /// Specification name (becomes the TLA+ module name and file prefix).
        name: String,
        /// Template to use for scaffolding.
        #[arg(short, long, value_enum, default_value = "basic")]
        template: InitTemplate,
        /// Output directory (default: current directory).
        #[arg(short, long, default_value = ".")]
        dir: PathBuf,
        /// Overwrite existing files.
        #[arg(long)]
        force: bool,
    },
    /// Parse a TLA+ source file and report syntax errors.
    Parse { file: PathBuf },
    /// Parse + lower a TLA+ source file and dump the lowered AST (Debug).
    Ast {
        file: PathBuf,
        /// Dump the lowered TIR instead of the lowered AST.
        #[arg(long, hide = true)]
        tir: bool,
    },
    /// Format a TLA+ source file with consistent style.
    ///
    /// By default, prints the formatted output to stdout.
    /// Use `--write` to modify the file in place, `--check` to verify
    /// formatting, or `--diff` to preview changes as a unified diff.
    Fmt {
        /// TLA+ source file(s) to format. Use `-` for stdin.
        files: Vec<PathBuf>,
        /// Write formatted output back to the source file(s) in place.
        #[arg(short, long, conflicts_with = "diff")]
        write: bool,
        /// Number of spaces per indentation level (default: 2).
        #[arg(long, default_value = "2")]
        indent: usize,
        /// Target maximum line width before expressions break to multiple lines.
        #[arg(long, default_value = "80")]
        width: usize,
        /// Check formatting without modifying files. Exit with code 1 if unformatted.
        #[arg(long, conflicts_with_all = ["write", "diff"])]
        check: bool,
        /// Show unified diff of what would change (implies no writes).
        #[arg(long, conflicts_with_all = ["write", "check"])]
        diff: bool,
    },
    /// Model check a TLA+ specification.
    Check {
        /// TLA+ source file to check.
        ///
        /// Supports `.tla` (TLA+ source) and `.qnt.json` (Quint IR) files.
        /// For `.qnt.json` files, the `--quint` flag is automatically inferred.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Compile the TLA+ spec to native Rust code, build, and run
        /// instead of interpreting.
        ///
        /// When set, tla2 generates Rust source from the spec via TIR codegen,
        /// writes a temporary Cargo project, builds with `cargo build --release`,
        /// and runs the compiled binary. The compiled binary performs BFS model
        /// checking and reports results in the same format as the interpreter.
        ///
        /// This can be significantly faster than interpretation for large state
        /// spaces since the generated code runs as optimized native machine code.
        ///
        /// Requires: Rust toolchain (cargo/rustc) installed and accessible.
        #[arg(long)]
        compiled: bool,
        /// Parse the input as Quint JSON IR instead of TLA+ source.
        ///
        /// Automatically enabled when the file extension is `.qnt.json`.
        /// Use this flag to force Quint parsing for files with other extensions.
        ///
        /// Part of #3754: Quint integration (Apalache Gap 6).
        #[arg(long)]
        quint: bool,
        /// Run N random walks before exhaustive BFS for fast shallow bug detection.
        ///
        /// Each walk starts from a random initial state and fires random transitions
        /// up to 10,000 steps. Zero memory overhead (no state set). If a violation is
        /// found, the trace is reported immediately and BFS is skipped.
        ///
        /// Part of #3720.
        #[arg(long, default_value = "0")]
        random_walks: usize,
        /// Maximum depth (steps) per random walk.
        ///
        /// Controls how many transitions each random walk explores before
        /// terminating. Higher values explore deeper state spaces but take longer.
        ///
        /// Part of #3720.
        #[arg(long, default_value = "10000")]
        walk_depth: usize,
        /// Compatibility alias that routes `tla2 check` through simulation mode.
        ///
        /// Use `tla2 simulate` for simulation-specific controls such as
        /// `--num-traces`, `--max-trace-length`, `--seed`, and `--no-invariants`.
        #[arg(long)]
        simulate: bool,
        /// Number of worker threads.
        /// 0 = auto (adaptive selection based on spec characteristics).
        /// 1 = sequential (no parallelism overhead).
        /// N = parallel with N workers.
        #[arg(short, long, default_value = "0")]
        workers: usize,
        /// Disable deadlock checking.
        #[arg(long)]
        no_deadlock: bool,
        /// Maximum number of states to explore (0 = unlimited).
        #[arg(long, default_value = "0")]
        max_states: usize,
        /// Maximum BFS depth to explore (0 = unlimited).
        #[arg(long, default_value = "0")]
        max_depth: usize,
        /// Memory limit in megabytes (0 = unlimited).
        ///
        /// When RSS reaches 80% of this limit, a checkpoint is saved (if configured).
        /// When RSS reaches 95%, exploration stops gracefully with a LimitReached result.
        /// Part of #2751: TLC MemCheck-style memory monitoring.
        #[arg(long, default_value = "0")]
        memory_limit: usize,
        /// Disk usage limit in megabytes for state storage (0 = unlimited).
        ///
        /// When disk-backed storage approaches this limit, exploration stops
        /// gracefully with a LimitReached result. This prevents filling disk
        /// volumes with .fp fingerprint files and state dumps.
        /// Part of #3282: TLC disk-exhaustion prevention.
        #[arg(long, default_value = "0")]
        disk_limit: usize,
        /// Gate: maximum allowed soundness mode (default: `sound`).
        ///
        /// This gate is about engine parity/experimental status. It does not encode
        /// boundedness; use `--require-exhaustive` to gate on configured bounds.
        #[arg(long, value_enum, default_value = "sound")]
        soundness: SoundnessGate,
        /// Gate: require exhaustive exploration (rejects configured bounds).
        ///
        /// Fails fast if `--max-states` or `--max-depth` are non-zero.
        #[arg(long)]
        require_exhaustive: bool,
        /// Enable Bounded Model Checking (BMC) mode with given depth bound.
        ///
        /// BMC encodes k-step transition sequences as SAT formulas for quick bug
        /// finding. If a violation exists within k steps, BMC finds it directly.
        /// Use 0 to disable (default). Typical values: 10-100.
        ///
        /// Note: BMC is experimental and only supports a subset of TLA+ specs.
        /// Works best with specs using Bool/Int variables and simple arithmetic.
        #[arg(long, default_value = "0", conflicts_with_all = [
            "workers",
            "por", "coverage", "no_deadlock", "max_states", "max_depth",
            "memory_limit", "disk_limit", "require_exhaustive",
            "no_trace", "store_states", "initial_capacity",
            "mmap_fingerprints", "disk_fingerprints", "mmap_dir",
            "trace_file", "mmap_trace_locations",
            "checkpoint", "checkpoint_interval", "resume",
            "continue_on_error", "difftrace",
            "profile_enum", "profile_enum_detail", "profile_eval", "liveness_mode",
        ])]
        bmc: usize,
        /// Use incremental solving for BMC: reuse solver state across depths.
        ///
        /// When enabled, BMC keeps one solver instance across all unrolling depths,
        /// using push/pop scoping to retract per-depth safety queries while retaining
        /// learned clauses from Init + accumulated transition assertions. This avoids
        /// re-encoding all transitions from scratch at each depth.
        ///
        /// Requires `--bmc` > 0. Part of #3724.
        #[arg(long, requires = "bmc")]
        bmc_incremental: bool,
        /// Enable PDR (Property-Directed Reachability) symbolic safety checking.
        ///
        /// PDR uses IC3/PDR algorithm with CHC (Constrained Horn Clauses) to prove
        /// safety properties symbolically. Unlike explicit-state model checking,
        /// PDR can prove safety for infinite-state systems.
        ///
        /// Note: PDR requires the z4 feature and only supports a subset of TLA+ specs
        /// (Bool/Int variables, arithmetic, comparisons). Part of #642.
        #[cfg(feature = "z4")]
        #[arg(long, conflicts_with_all = [
            "workers", "bmc",
            // Explicit-state features unsupported by the symbolic PDR engine.
            // Part of #3576: fail closed instead of silently dropping flags.
            "por", "coverage", "no_deadlock", "max_states", "max_depth",
            "memory_limit", "disk_limit", "require_exhaustive",
            "no_trace", "store_states", "initial_capacity",
            "mmap_fingerprints", "disk_fingerprints", "mmap_dir",
            "trace_file", "mmap_trace_locations",
            "checkpoint", "checkpoint_interval", "resume",
            "continue_on_error", "difftrace",
            "profile_enum", "profile_enum_detail", "profile_eval", "liveness_mode",
        ])]
        pdr: bool,
        /// Enable k-induction symbolic safety proving.
        ///
        /// K-induction extends BMC by attempting to prove safety properties hold
        /// for ALL reachable states, not just bounded depth. First runs BMC as
        /// a base case, then checks an inductive step. If the inductive step
        /// succeeds (UNSAT), the property is proved for all reachable states.
        ///
        /// Note: requires the z4 feature and only supports a subset of TLA+ specs
        /// (Bool/Int variables, arithmetic, comparisons). Part of #3722.
        #[cfg(feature = "z4")]
        #[arg(long, conflicts_with_all = [
            "workers", "bmc", "pdr",
            "por", "coverage", "no_deadlock", "max_states", "max_depth",
            "memory_limit", "disk_limit", "require_exhaustive",
            "no_trace", "store_states", "initial_capacity",
            "mmap_fingerprints", "disk_fingerprints", "mmap_dir",
            "trace_file", "mmap_trace_locations",
            "checkpoint", "checkpoint_interval", "resume",
            "continue_on_error", "difftrace",
            "profile_enum", "profile_enum_detail", "profile_eval", "liveness_mode",
        ])]
        kinduction: bool,
        /// Maximum induction depth for k-induction (default: 20).
        ///
        /// The algorithm tries increasing depths k=1..N until the inductive step
        /// succeeds (property proved) or the maximum is reached (inconclusive).
        /// Higher values increase the chance of proving the property but take longer.
        #[cfg(feature = "z4")]
        #[arg(long, default_value = "20", requires = "kinduction")]
        kinduction_max_k: usize,
        /// Use incremental solving for k-induction's inductive step.
        ///
        /// Keeps a single solver instance across all depth iterations, retaining
        /// learned clauses via push/pop scoping. Can significantly speed up the
        /// inductive step for specs where each depth builds on the previous one.
        #[cfg(feature = "z4")]
        #[arg(long, requires = "kinduction")]
        kinduction_incremental: bool,
        /// Enable multi-phase verification pipeline.
        ///
        /// Runs cheap verification phases first (random walk, BMC) to resolve
        /// easy properties, then expensive phases (PDR, BFS) only on remaining
        /// hard properties. The default pipeline is:
        /// walk(5s) -> BMC(30s) -> PDR(60s) -> BFS(300s).
        ///
        /// BMC and PDR phases require the z4 feature; they are silently skipped
        /// if z4 is not available. Part of #3723.
        #[arg(long, conflicts_with = "strategy")]
        pipeline: bool,
        /// Named verification strategy for multi-phase pipeline mode.
        ///
        /// Selects a pre-configured pipeline of verification phases:
        ///   quick  — RandomWalk(2s) + BMC(10s). Fast feedback, no BFS.
        ///   full   — RandomWalk(5s) + exhaustive BFS(600s). TLC-equivalent.
        ///   auto   — walk -> BMC -> k-induction -> PDR -> BFS (adaptive).
        ///
        /// Implies `--pipeline`. Conflicts with `--bmc`, `--pdr`, `--kinduction`,
        /// `--fused`, and `--pipeline` (which uses the default auto strategy).
        ///
        /// Part of #3723.
        #[arg(long, value_enum, conflicts_with_all = [
            "pipeline", "bmc",
        ])]
        strategy: Option<StrategyArg>,
        /// Force pure BFS model checking (disable CDEMC/fused default).
        ///
        /// When the z4 feature is enabled, the checker defaults to cooperative
        /// fused BFS+symbolic verification (CDEMC). Use `--bfs-only` to disable
        /// symbolic lanes and run pure explicit-state BFS, matching TLC behavior.
        ///
        /// Part of #3953.
        #[arg(long, conflicts_with_all = ["pipeline", "bmc", "portfolio", "strategy"])]
        bfs_only: bool,
        /// Enable cooperative fused BFS+symbolic verification (now the default).
        ///
        /// This is now the default when the z4 feature is enabled. The flag is
        /// retained for backward compatibility but is no longer required.
        /// Use `--bfs-only` to opt out.
        ///
        /// Part of #3770, #3953.
        #[cfg(feature = "z4")]
        #[arg(long, conflicts_with_all = ["pipeline", "bmc", "pdr", "kinduction", "portfolio"], hide = true)]
        fused: bool,
        /// Enable portfolio racing: run BFS + symbolic strategies in parallel.
        ///
        /// Spawns multiple verification lanes simultaneously and terminates when
        /// the first one reaches a definitive result. BFS always runs; symbolic
        /// lanes (PDR, BMC, k-induction) require the z4 feature.
        ///
        /// Use `--portfolio-strategies` to select which strategies to race.
        /// Default: bfs + all available symbolic strategies.
        ///
        /// Part of #3717.
        #[arg(long, conflicts_with_all = [
            "pipeline", "bmc", "strategy",
            "workers",
        ])]
        portfolio: bool,
        /// Comma-separated list of portfolio strategies to race.
        ///
        /// Available strategies: bfs, random (always available);
        /// bmc, pdr, kinduction (require z4 feature).
        /// Default when omitted: all available strategies.
        ///
        /// Examples:
        ///   --portfolio --portfolio-strategies bfs,random
        ///   --portfolio --portfolio-strategies bfs,bmc,pdr
        ///
        /// Part of #3717.
        #[arg(long, requires = "portfolio", value_delimiter = ',')]
        portfolio_strategies: Vec<String>,
        /// Enable Partial Order Reduction (POR) for state-space reduction.
        ///
        /// POR computes ample sets of independent actions to reduce the number
        /// of states explored while preserving safety properties. Works with
        /// both sequential and parallel BFS engines.
        #[arg(long)]
        por: bool,
        /// Show state space size estimate during model checking.
        ///
        /// Tracks states discovered per BFS level and fits growth models
        /// (exponential, logistic, linear) to predict total reachable states.
        #[arg(long)]
        estimate: bool,
        /// Run estimation-only mode: explore first N BFS levels, then stop.
        ///
        /// Implies `--estimate`.
        #[arg(long, value_name = "LEVELS")]
        estimate_only: Option<usize>,
        /// Show per-action coverage statistics.
        ///
        /// Note: Coverage collection is only supported in sequential mode today.
        /// Use `--workers 1` or `--workers 0` (auto, which will force sequential).
        #[arg(long)]
        coverage: bool,
        /// Enable coverage-guided exploration.
        ///
        /// Uses a hybrid BFS + priority frontier that directs exploration toward
        /// states exercising rare or uncovered actions. Forces sequential mode.
        #[arg(long)]
        coverage_guided: bool,
        /// Mix ratio for coverage-guided exploration (default: 8).
        ///
        /// Controls how often to dequeue from the priority queue:
        /// - 1 = always prefer coverage-guided (aggressive)
        /// - 8 = every 8th pop is coverage-guided (balanced, default)
        /// - 0 = never use priority queue (pure BFS with coverage reporting)
        #[arg(long, default_value = "8", requires = "coverage_guided")]
        coverage_mix_ratio: usize,
        /// Enable enumeration profiling (coarse timing breakdown).
        ///
        /// Prints a high-level time breakdown showing: Successor gen, Fingerprinting,
        /// Dedup check, Invariant check, and Other. Equivalent to TLA2_PROFILE_ENUM=1.
        #[arg(long)]
        profile_enum: bool,
        /// Enable detailed enumeration profiling.
        ///
        /// Prints detailed breakdowns inside the enumerator: domain/guard/assignment
        /// time, EXISTS loop details, etc. Equivalent to TLA2_PROFILE_ENUM_DETAIL=1.
        #[arg(long)]
        profile_enum_detail: bool,
        /// Enable eval() call count profiling.
        ///
        /// Prints eval call count summary at the end of checking. Useful for
        /// identifying expensive sub-expression evaluation. Equivalent to TLA2_PROFILE_EVAL=1.
        #[arg(long)]
        profile_eval: bool,
        /// Liveness execution strategy.
        ///
        /// `full` reuses the BFS-cached successor graph. `on-the-fly` skips
        /// that graph and regenerates successors lazily during liveness
        /// product exploration to reduce memory usage.
        #[arg(long = "liveness-mode", value_enum, default_value = "full")]
        liveness_mode: LivenessModeArg,
        /// Strict liveness: panic on missing states instead of skipping.
        ///
        /// By default, the parallel liveness checker gracefully skips states
        /// that are missing from the post-BFS state cache (with a warning).
        /// Use --strict-liveness to panic on any missing state, which is
        /// useful for debugging nondeterministic liveness crashes.
        /// Equivalent to setting TLA2_STRICT_LIVENESS=1.
        #[arg(long)]
        strict_liveness: bool,
        /// Enable JIT compilation of invariant and action operators.
        ///
        /// Deprecated and slated for removal in Wave 7e of #4251. The Cranelift
        /// JIT path is being deleted in favor of LLVM2 AOT. Set `TLA2_JIT=1` in
        /// the environment if you need to enable the legacy runtime path during
        /// migration.
        ///
        /// Part of #4251 Wave 12 7e finalizer: CLI surface removal.
        #[arg(long, hide = true)]
        jit: bool,
        /// Cross-check JIT invariant results against the interpreter.
        ///
        /// Deprecated alongside `--jit`. Will be removed with the Cranelift
        /// path in Wave 7e of #4251.
        #[arg(long, hide = true)]
        jit_verify: bool,
        /// Show per-action tier compilation summary at end of run.
        ///
        /// Prints a table showing each action's compilation tier, evaluation
        /// count, branching factor, and JIT dispatch counters (hits, fallbacks,
        /// not_compiled, errors). Useful for diagnosing JIT coverage.
        ///
        /// Part of #3932.
        #[arg(long)]
        show_tiers: bool,
        /// Control speculative type specialization for JIT Tier 2.
        ///
        /// When `auto` (default), type profiling is enabled when --jit is
        /// active. The profiler samples runtime types of state variables
        /// during BFS warmup (~1000 states). If variables are monomorphic
        /// (always Int or Bool), a specialization plan guides Tier 2
        /// recompilation to skip type checks in compiled code.
        ///
        /// `on` forces profiling even without --jit (useful for diagnostics).
        /// `off` disables profiling entirely.
        ///
        /// Part of #3989: JIT V2 Phase 6 speculative type specialization.
        #[arg(long, value_enum, default_value = "auto")]
        type_specialize: TypeSpecializeArg,
        /// Maximum memory efficiency: disable all trace reconstruction.
        ///
        /// By default, TLA2 stores only fingerprints with a temp trace file for
        /// counterexample reconstruction (42x less memory than full states).
        /// Use --no-trace to also disable the trace file, which maximizes memory
        /// savings but may leave safety counterexample traces unavailable.
        ///
        /// Temporal checking still runs when the checker can replay from cached
        /// graph data, and the checker may still enable full-state storage when
        /// required for soundness-critical cases.
        #[arg(long)]
        no_trace: bool,
        /// Store full states in memory (legacy mode, 42x more memory).
        ///
        /// By default, TLA2 stores only fingerprints with disk-based trace
        /// reconstruction. Use --store-states to keep full states in memory,
        /// which provides faster trace reconstruction but uses ~42x more memory.
        /// This was the default behavior before v0.6.
        ///
        /// Conflicts with --no-trace.
        #[arg(long, conflicts_with = "no_trace")]
        store_states: bool,
        /// Pre-allocate in-memory fingerprint storage capacity.
        ///
        /// Part of #188, #229: Pre-allocating capacity reduces hash set resizing
        /// during model checking, which can cause performance degradation at scale.
        /// Specify the expected number of states (e.g., "6000000" for 6M states).
        ///
        /// If not set, the hash set grows dynamically with O(n) resize events.
        /// For large specs, this can add 20+ resize events that each rehash all
        /// fingerprints. Pre-allocation avoids this overhead entirely.
        #[arg(long, value_name = "CAPACITY", conflicts_with_all = ["mmap_fingerprints", "disk_fingerprints"])]
        initial_capacity: Option<usize>,
        /// Use memory-mapped fingerprint storage with given capacity.
        ///
        /// This enables exploring state spaces larger than available RAM by using
        /// memory-mapped storage that can page to disk. The capacity specifies the
        /// maximum number of fingerprints to store (e.g., "1000000" for 1M states).
        ///
        /// Incompatible with --store-states. If not set, uses in-memory hash set.
        #[arg(long, value_name = "CAPACITY", conflicts_with = "store_states")]
        mmap_fingerprints: Option<usize>,
        /// Enable huge page hints for mmap fingerprint storage.
        ///
        /// When used with --mmap-fingerprints, requests the OS to back the
        /// memory-mapped storage with huge pages (2MB) for reduced TLB pressure.
        ///
        /// Part of #3856.
        #[arg(long)]
        huge_pages: bool,
        /// Use disk-backed fingerprint storage with automatic eviction.
        ///
        /// This enables exploring billion-state specs by automatically evicting
        /// fingerprints from memory to disk when the primary storage fills up.
        /// The capacity specifies the in-memory primary storage size before eviction.
        ///
        /// Requires --mmap-dir. Incompatible with --store-states and --mmap-fingerprints.
        #[arg(long, value_name = "CAPACITY", conflicts_with_all = ["mmap_fingerprints", "store_states"])]
        disk_fingerprints: Option<usize>,
        /// Directory for memory-mapped or disk-backed fingerprint storage.
        ///
        /// If specified with --mmap-fingerprints, creates a file-backed mapping
        /// in this directory, allowing the OS to page fingerprints to disk.
        /// If not specified, uses anonymous memory mapping (in-memory, but with
        /// mmap semantics for potentially better OS memory management).
        ///
        /// Required for --disk-fingerprints. The evicted fingerprints are stored
        /// as sorted files in this directory.
        #[arg(long, value_name = "DIR")]
        mmap_dir: Option<PathBuf>,
        /// Path to explicit disk-based trace file for counterexample reconstruction.
        ///
        /// By default, TLA2 creates a temporary trace file automatically. Use this
        /// to specify a persistent location. The file stores (predecessor, fingerprint)
        /// pairs for trace reconstruction. Useful for debugging or keeping traces.
        ///
        /// Incompatible with --store-states. If file already exists, it will be overwritten.
        #[arg(long, value_name = "FILE", conflicts_with = "store_states")]
        trace_file: Option<PathBuf>,
        /// Use memory-mapped storage for trace file location mapping.
        ///
        /// When using --trace-file, this option enables memory-mapped storage
        /// for the fingerprint-to-offset mapping. Specify the capacity (maximum
        /// number of states). This reduces memory usage for large state spaces.
        ///
        /// Requires --trace-file. Uses the same directory as --mmap-dir if specified.
        #[arg(long, value_name = "CAPACITY")]
        mmap_trace_locations: Option<usize>,
        /// Fingerprint collision detection mode (none/sampling/sampling:N/full).
        #[arg(long, default_value = "none", value_name = "MODE")]
        collision_check: String,
        /// Directory for saving checkpoints during model checking.
        ///
        /// When specified, the model checker will periodically save checkpoint
        /// files to this directory. Checkpoints allow resuming interrupted model
        /// checking runs. The checkpoint interval can be set with --checkpoint-interval.
        #[arg(long, value_name = "DIR")]
        checkpoint: Option<PathBuf>,
        /// Checkpoint interval in seconds (default: 300).
        ///
        /// How often to save checkpoints during model checking. Only used when
        /// --checkpoint is specified.
        #[arg(long, default_value = "300")]
        checkpoint_interval: u64,
        /// Resume model checking from a checkpoint directory.
        ///
        /// Loads the checkpoint from the specified directory and continues
        /// model checking from where it left off.
        #[arg(long, value_name = "DIR")]
        resume: Option<PathBuf>,
        /// Output format: human (default), json, jsonl, or tlc-tool.
        ///
        /// Use `json` for structured output suitable for AI agents and automated tooling.
        /// Use `jsonl` (alias: `json-lines`) for streaming output with one JSON object per line.
        /// Use `tlc-tool` (alias: `tool`) for Eclipse Toolbox-compatible tagged output.
        #[arg(long, value_enum, default_value = "human")]
        output: OutputFormat,
        /// Emit TLC "-tool" tagged output (Eclipse Toolbox-compatible).
        ///
        /// Equivalent to `--output tlc-tool`.
        #[arg(long, conflicts_with = "output")]
        tool: bool,
        /// Format for counterexample traces: text (default), dot, or itf.
        ///
        /// Use `dot` to output traces in GraphViz DOT format for visualization.
        /// The DOT output can be rendered using: dot -Tpng trace.dot -o trace.png
        ///
        /// Use `itf` for Informal Trace Format (ITF) JSON output compatible with
        /// Apalache and other TLA+ ecosystem tooling.
        #[arg(long, value_enum, default_value = "text")]
        trace_format: TraceFormat,
        /// Show only changed variables in counterexample traces (TLC -difftrace).
        ///
        /// When enabled, each state after the first shows only variables whose
        /// values differ from the previous state. The initial state always shows
        /// all variables. Matches TLC's `-difftrace` behavior.
        ///
        /// Part of #2470: TLC trace format parity, Step 5.
        #[arg(long)]
        difftrace: bool,
        /// Annotate counterexample traces with human-readable explanations.
        #[arg(long)]
        explain_trace: bool,
        /// Continue exploring after finding an invariant or property violation.
        ///
        /// By default, model checking stops at the first violation. With this flag,
        /// exploration continues until the full state space is exhausted (or limits
        /// are reached), then reports the first violation found with final stats.
        ///
        /// This is useful for:
        /// - Getting stable state counts for error specs (comparable with TLC -continue)
        /// - Finding all reachable states even when some violate invariants
        ///
        /// Violating states are still counted as "seen" but not expanded further.
        #[arg(long)]
        continue_on_error: bool,
        /// Allow incomplete results when fingerprint storage overflows.
        ///
        /// By default, mmap fingerprint overflow is a fatal error because dropped
        /// states make verification unsound. Use this only when you intentionally
        /// want partial exploration and accept incomplete results.
        #[arg(long)]
        allow_incomplete: bool,
        /// Bypass the local check cache (always re-run).
        #[arg(long)]
        force: bool,
        /// Override the Init operator (replaces INIT from .cfg).
        ///
        /// When used with --next, allows running without a .cfg file entirely.
        /// If both --init/--next and a .cfg are provided, CLI flags take precedence.
        /// Part of #3759.
        #[arg(long, value_name = "OPERATOR")]
        init: Option<String>,
        /// Override the Next operator (replaces NEXT from .cfg).
        ///
        /// When used with --init, allows running without a .cfg file entirely.
        /// If both --init/--next and a .cfg are provided, CLI flags take precedence.
        /// Part of #3759.
        #[arg(long, value_name = "OPERATOR")]
        next: Option<String>,
        /// Override invariants to check (replaces INVARIANT from .cfg).
        ///
        /// Can be specified multiple times: --inv TypeOK --inv Safety.
        /// If both --inv and a .cfg are provided, CLI flags take precedence.
        /// Part of #3759.
        #[arg(long = "inv", value_name = "INVARIANT")]
        invariants: Vec<String>,
        /// Override temporal properties to check (replaces PROPERTY from .cfg).
        ///
        /// Can be specified multiple times: --prop Liveness --prop Fairness.
        /// If both --prop and a .cfg are provided, CLI flags take precedence.
        /// Part of #3779.
        #[arg(long = "prop", value_name = "PROPERTY")]
        properties: Vec<String>,
        /// Override constant assignments (replaces CONSTANT from .cfg).
        ///
        /// Format: NAME=VALUE where VALUE is a TLA+ expression.
        /// Can be specified multiple times: --const N=3 --const "Procs={p1,p2}".
        /// If both --const and a .cfg are provided, CLI flags take precedence.
        /// Part of #3779.
        #[arg(long = "const", value_name = "NAME=VALUE")]
        constants: Vec<String>,
        /// Skip .cfg file entirely; use only CLI flags and convention defaults.
        ///
        /// When set, the model checker does not look for or read a .cfg file.
        /// Combine with --init/--next/--inv for fully config-free checking.
        /// Without --init/--next, convention names "Init" and "Next" are used.
        /// Part of #3779.
        #[arg(long, conflicts_with = "config")]
        no_config: bool,
        /// Disable TIR preprocessing (NNF normalization, keramelization,
        /// constant folding).
        ///
        /// By default, the model checker applies a preprocessing pipeline to
        /// TIR expressions after lowering: negation normal form (NNF),
        /// conjunction/disjunction flattening (keramelization), and boolean
        /// constant folding. This improves evaluation performance by
        /// normalizing expression trees.
        ///
        /// Use --no-preprocess to skip the pipeline (for debugging or
        /// comparison). Equivalent to setting TLA2_NO_PREPROCESS=1.
        #[arg(long)]
        no_preprocess: bool,
        /// Enable partial evaluation of CONSTANT bindings into TIR operator
        /// bodies before the preprocessing pipeline runs.
        ///
        /// When enabled, the model checker substitutes each reference to a
        /// module-level `CONSTANT` (from the .cfg file) with its concrete
        /// `Value` in the lowered TIR. The existing const_prop pipeline then
        /// cascades through the baked literals (arithmetic folds, IF
        /// simplification, dead-branch elimination, etc.).
        ///
        /// This is the first "structural supremacy" pillar: specialization per
        /// concrete spec configuration is something TLC / the JVM HotSpot JIT
        /// cannot perform by construction, because the JVM does not know the
        /// CONSTANT assignment is frozen after spec load.
        ///
        /// See `designs/2026-04-18-supremacy-pillar-partial-eval.md`. Part of
        /// #4251 Stream 5. Equivalent to setting `TLA2_PARTIAL_EVAL=1`.
        #[arg(long)]
        partial_eval: bool,
        /// Allow IOExec and related operators to execute shell commands.
        ///
        /// By default, the IOExec, IOEnvExec, IOExecTemplate, and
        /// IOEnvExecTemplate operators are disabled for security. A malicious
        /// TLA+ spec could use these operators to run arbitrary commands on
        /// the host system. Pass --allow-io to explicitly opt in to IO
        /// command execution when you trust the spec being checked.
        ///
        /// Part of #3965: Security gate for IOExec command execution.
        #[arg(long)]
        allow_io: bool,
        /// Check trace invariants over the execution history (Apalache-style).
        ///
        /// A trace invariant is an operator that takes a `Seq(Record)` argument
        /// representing the execution trace up to the current state. Each record
        /// in the sequence has fields matching the spec's state variables.
        ///
        /// The operator is called at each BFS state with the trace leading to
        /// that state. If it returns FALSE, a violation is reported with the
        /// full trace as the counterexample.
        ///
        /// Can be specified multiple times: --trace-inv TraceInv1 --trace-inv TraceInv2.
        ///
        /// Part of #3752: Apalache Gap 4 — trace invariant checking.
        #[arg(long = "trace-inv", alias = "trace-invariant", value_name = "OPERATOR")]
        trace_invariants: Vec<String>,
        /// Check that an operator is an inductive invariant (Apalache-style).
        ///
        /// Runs a two-phase check:
        /// 1. Initiation: `Init => IndInv` (initial states satisfy the invariant)
        /// 2. Consecution: `IndInv /\ Next => IndInv'` (transitions preserve the invariant)
        ///
        /// Equivalent to `--kinduction --kinduction-max-k 1 --inv <INVARIANT>`
        /// (1-induction), but reports which phase fails for clearer diagnostics.
        ///
        /// Requires the z4 feature. Part of #3756.
        #[cfg(feature = "z4")]
        #[arg(long, value_name = "INVARIANT")]
        inductive_check: Option<String>,
        /// Enable symbolic simulation mode (Apalache-style).
        ///
        /// Uses z4 SMT solving to explore random execution paths symbolically.
        /// Unlike BMC (which checks all paths up to depth k), symbolic simulation
        /// follows one path per run, extracting concrete witnesses at each step.
        /// Multiple runs with different solver choices explore different paths.
        ///
        /// Requires the z4 feature. Part of #3757.
        #[cfg(feature = "z4")]
        #[arg(long, conflicts_with_all = [
            "workers", "bmc", "pdr", "kinduction", "fused", "pipeline",
            "por", "coverage", "no_deadlock", "max_states", "max_depth",
            "memory_limit", "disk_limit", "require_exhaustive",
            "no_trace", "store_states", "initial_capacity",
            "mmap_fingerprints", "disk_fingerprints", "mmap_dir",
            "trace_file", "mmap_trace_locations",
            "checkpoint", "checkpoint_interval", "resume",
            "continue_on_error", "difftrace",
            "profile_enum", "profile_enum_detail", "profile_eval", "liveness_mode",
            "inductive_check",
        ])]
        symbolic_sim: bool,
        /// Number of simulation runs for `--symbolic-sim` (default: 100).
        ///
        /// Each run explores an independent random execution path.
        /// More runs increase the probability of finding violations.
        #[cfg(feature = "z4")]
        #[arg(long, default_value = "100", requires = "symbolic_sim")]
        sim_runs: usize,
        /// Maximum depth (steps) per simulation run for `--symbolic-sim` (default: 10).
        ///
        /// Controls how many Next transitions each run explores.
        /// Higher values explore deeper state spaces but take longer per run.
        #[cfg(feature = "z4")]
        #[arg(long, default_value = "10", requires = "symbolic_sim")]
        sim_length: usize,
        /// Enable incremental model checking with a cache directory.
        ///
        /// On the first run, saves a verification cache. On subsequent runs,
        /// computes an AST-level diff and only re-explores affected states.
        #[arg(long, value_name = "DIR")]
        incremental: Option<PathBuf>,
        /// Enable distributed multi-machine model checking.
        ///
        /// Partitions the fingerprint space across multiple machines connected
        /// via TCP. Each node owns a slice of the state space and exchanges
        /// cross-partition states over the network. Uses Dijkstra's token-based
        /// algorithm for distributed termination detection.
        ///
        /// Requires `--nodes` to specify the cluster addresses.
        ///
        /// Part of Pillar 6 Phase 2: Multi-machine distributed BFS.
        #[arg(long, requires = "nodes")]
        distributed: bool,
        /// Comma-separated list of node addresses for distributed checking.
        ///
        /// Format: `host1:port1,host2:port2,...`
        /// The node's own address is identified by `--node-id`.
        ///
        /// Example: `--distributed --nodes 10.0.0.1:9000,10.0.0.2:9000,10.0.0.3:9000 --node-id 0`
        #[arg(long, requires = "distributed", value_delimiter = ',')]
        nodes: Vec<String>,
        /// This node's ID in the distributed cluster (0-indexed).
        ///
        /// Must be in the range `[0, len(nodes))`. Node 0 acts as the
        /// coordinator for progress reporting and termination initiation.
        #[arg(long, default_value = "0", requires = "distributed")]
        node_id: u32,
        /// Evaluation backend: `interpreter` (default, the oracle) or `llvm2`
        /// (AOT-compiled native path). `llvm2` is a stub that emits a
        /// `backend_unavailable` JSON result and exits with code 3 until the
        /// compiled path is wired in (#4252 Stream 6).
        #[arg(long, value_enum, default_value = "interpreter")]
        backend: CheckBackend,
    },
    /// Trace-related tooling (parsing, validation, visualization).
    Trace {
        #[command(subcommand)]
        command: crate::trace_cmd::TraceCommand,
    },
    /// Run a Petri-net MCC examination against a PNML model.
    Petri {
        /// Model directory or a direct path to `model.pnml`.
        model: PathBuf,
        /// MCC examination name.
        #[arg(long)]
        examination: String,
        #[command(flatten)]
        args: tla_petri::cli::PetriRunArgs,
    },
    /// Emit a JSON formula-simplification report for one MCC property examination.
    ///
    /// Loads the model, parses the property XML for the given examination,
    /// simplifies each formula against the net's structure, and prints a
    /// JSON report showing which formulas were simplified, resolved, or
    /// left unchanged.
    #[command(name = "petri-simplify")]
    PetriSimplify {
        /// Model directory containing `model.pnml` and examination XML files.
        model_dir: PathBuf,
        /// Property examination name (e.g. ReachabilityFireability, CTLFireability).
        #[arg(long)]
        examination: String,
    },
    /// Run MCC-style Petri model checking.
    ///
    /// Supports the same `BK_INPUT`, `BK_EXAMINATION`, and `BK_TIME_CONFINEMENT`
    /// environment variables as the legacy `pnml-tools` entrypoint.
    Mcc {
        /// Model directory or a direct path to `model.pnml`.
        ///
        /// If omitted, uses `BK_INPUT` or the current directory.
        model_dir: Option<PathBuf>,
        /// MCC examination name.
        ///
        /// If omitted, uses `BK_EXAMINATION`.
        #[arg(long)]
        examination: Option<String>,
        #[command(flatten)]
        args: tla_petri::cli::PetriRunArgs,
    },
    /// Property-based testing of a TLA+ specification.
    ///
    /// Runs N random walks through the state space, checking invariants
    /// along each trace. Reports results in a test-framework style with
    /// per-invariant pass/fail and trace statistics.
    ///
    /// Unlike exhaustive model checking (`check`), `test` uses random
    /// exploration for fast feedback during development. Any bug found
    /// is real, but absence of bugs is not a proof of correctness.
    ///
    /// Exit code 0 on all-pass, 1 on any failure. Use `--seed` for
    /// deterministic replay of failures.
    Test {
        /// TLA+ source file to test.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of random walks (test runs) to execute.
        #[arg(short, long, default_value = "100")]
        runs: usize,
        /// Maximum depth (steps) per random walk.
        #[arg(short, long, default_value = "10000")]
        depth: usize,
        /// Random seed for reproducibility (0 = random seed).
        #[arg(short, long, default_value = "0")]
        seed: u64,
        /// Number of worker threads for parallel trace generation.
        /// 0 = auto (use available cores), 1 = sequential (default).
        #[arg(short, long, default_value = "1")]
        workers: usize,
        /// Disable deadlock checking.
        #[arg(long)]
        no_deadlock: bool,
    },
    /// Simulate a TLA+ specification (random trace exploration).
    ///
    /// Unlike exhaustive model checking, simulation generates random traces
    /// through the state space. This is useful for:
    /// - Quick exploration of large state spaces
    /// - Finding bugs that require deep traces
    /// - Probabilistic coverage when exhaustive checking is infeasible
    Simulate {
        /// TLA+ source file to simulate.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of random traces to generate.
        #[arg(short, long, default_value = "1000")]
        num_traces: usize,
        /// Maximum length of each trace (steps from initial state).
        #[arg(short = 'l', long, default_value = "100")]
        max_trace_length: usize,
        /// Random seed for reproducibility (0 = random seed).
        #[arg(long, default_value = "0")]
        seed: u64,
        /// Disable invariant checking during simulation.
        #[arg(long)]
        no_invariants: bool,
    },
    /// Start the Language Server Protocol server.
    Lsp,
    /// Start a JSON-RPC server for interactive state exploration.
    ///
    /// Loads a TLA+ spec and exposes it via a TCP JSON-RPC 2.0 interface for
    /// step-by-step model exploration. Supports: `init()`, `step(state_id)`,
    /// `eval(state_id, expr)`, `check_invariant(state_id, inv)`.
    ///
    /// Part of #3751: Apalache Gap 3 — interactive symbolic exploration API.
    Server {
        /// TLA+ source file to load.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// TCP port to listen on (default: 8765).
        #[arg(short, long, default_value = "8765")]
        port: u16,
    },
    /// Interactively explore a TLA+ specification's state space.
    ///
    /// Default mode is an interactive terminal REPL with commands:
    ///   init, step, pick, eval, inv, back, forward, trace, actions, help, quit
    ///
    /// With `--mode http`, starts an HTTP JSON API server instead:
    ///   POST /explore/init          — compute initial states
    ///   POST /explore/eval          — evaluate expression in a state
    ///   POST /explore/successors    — compute successor states
    ///   POST /explore/random-trace  — generate a random execution trace
    ///
    /// Part of #3795: Interactive symbolic exploration API.
    Explore {
        /// TLA+ source file to load.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// HTTP port for `--mode http` (default: 8080).
        #[arg(short, long, default_value = "8080")]
        port: u16,
        /// Exploration mode: 'repl' (default) or 'http'.
        #[arg(short, long, default_value = "repl")]
        mode: ExploreModeArg,
        /// Exploration engine: 'concrete' (default) or 'symbolic'.
        ///
        /// 'concrete' uses explicit-state enumeration (always available).
        /// 'symbolic' uses SMT-based exploration via z4 (requires z4 feature).
        /// You can also switch engines at runtime via the REPL 'symbolic'/'concrete'
        /// commands or the POST /explore/mode HTTP endpoint.
        ///
        /// Part of #3751: Apalache Gap 3 — interactive symbolic exploration.
        #[arg(short, long, default_value = "concrete")]
        engine: ExploreEngineArg,
        /// Maximum symbolic exploration depth (default: 20).
        ///
        /// Limits how many symbolic transition steps can be taken before
        /// the solver rejects further exploration. Only meaningful when
        /// `--engine symbolic` is used or when switching to symbolic mode
        /// at runtime.
        ///
        /// Part of #3751: Apalache Gap 3 — interactive symbolic exploration.
        #[arg(long, default_value = "20")]
        max_symbolic_depth: usize,
        /// Disable automatic invariant checking at each step (REPL mode only).
        #[arg(long)]
        no_invariants: bool,
    },
    /// Prove theorems in a TLA+ specification (requires Z3).
    #[cfg(feature = "prove")]
    Prove {
        /// TLA+ source file to prove.
        file: PathBuf,
        /// Timeout per obligation in seconds.
        #[arg(short, long, default_value = "60")]
        timeout: u64,
        /// Only check specific theorem(s) by name (comma-separated).
        #[arg(long)]
        theorem: Option<String>,
    },
    /// Run diagnostic coverage analysis against the TLC baseline.
    ///
    /// Tests the current binary against known TLC results from spec_baseline.json.
    /// The binary tests itself via std::env::current_exe(), so the binary being
    /// measured is always the binary doing the measuring.
    Diagnose(DiagnoseArgs),
    /// Benchmark TLA+ specs with timing and baseline comparison.
    ///
    /// Runs each spec through `tla2 check` with precise timing, reports throughput
    /// (states/sec), wall time, and optionally compares against TLC baselines or
    /// previously-saved benchmark data.
    Bench {
        /// Spec file(s) or directory to benchmark.
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Config file (.cfg) for single-spec benchmarks.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of iterations per spec for statistical accuracy.
        #[arg(long, default_value = "1")]
        iterations: usize,
        /// Number of worker threads (0 = auto).
        #[arg(short, long, default_value = "0")]
        workers: usize,
        /// Path to spec_baseline.json for TLC comparison.
        #[arg(long)]
        baseline: Option<PathBuf>,
        /// Save results as new benchmark baseline JSON file.
        #[arg(long)]
        save_baseline: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: BenchOutputFormat,
    },
    /// Summarize model checking results for one or more specs in a compact table.
    ///
    /// Runs `tla2 check` on each spec and produces a one-line-per-spec summary
    /// showing status, state count, time, depth, and invariant names.
    /// Useful for batch checking directories of specs.
    ///
    /// Output formats: human (colored table), json (array), csv (spreadsheets).
    Summary {
        /// Spec file(s) or directory to check.
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Config file (.cfg) for single-spec runs.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of worker threads per check subprocess (0 = auto).
        #[arg(short, long, default_value = "0")]
        workers: usize,
        /// Output format: human (default), json, or csv.
        #[arg(long, value_enum, default_value = "human")]
        format: SummaryOutputFormat,
        /// Sort results by: name (default), time, states, or status.
        #[arg(long, value_enum, default_value = "name")]
        sort: SummarySortBy,
        /// Filter results by status: pass, error, timeout, or crash.
        #[arg(long)]
        status: Option<String>,
    },
    /// Minimize a TLA+ spec to a minimal reproducer of a property violation.
    ///
    /// Uses delta debugging to systematically remove operators, variables,
    /// constants, and expression sub-terms until a minimal spec that still
    /// exhibits the same failure is found.
    Minimize {
        /// TLA+ source file to minimize.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Maximum number of model-checker oracle calls before stopping.
        #[arg(long, default_value = "1000")]
        max_oracle_calls: usize,
        /// Disable fine-grained expression simplification.
        #[arg(long)]
        no_fine: bool,
        /// Write the minimized spec to a file instead of stdout.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
    },
    /// Lint a TLA+ specification for common issues.
    ///
    /// Parses the spec and runs static analysis checks including:
    /// unused operators, unused variables, shadowed names, missing Init/Next,
    /// stuttering detection, and naming convention warnings.
    Lint {
        /// TLA+ source file to lint.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: LintOutputFormat,
        /// Minimum severity to report: warning (default) or info.
        #[arg(long, value_enum, default_value = "warning")]
        severity: LintSeverityArg,
    },
    /// Search across TLA+ specifications for patterns.
    ///
    /// Parses TLA+ specs and searches for operator definitions, variable
    /// declarations, constant declarations, expression text, and Next-action
    /// disjuncts matching a pattern. Recursively walks directories for .tla files.
    ///
    /// The pattern is a glob: `*` matches zero or more characters, `?` matches
    /// exactly one character. A bare substring (no wildcards) matches anywhere
    /// (case-insensitive).
    Search {
        /// Pattern to search for (glob: * and ? supported; plain text = substring).
        pattern: String,
        /// Files or directories to search. Directories are walked recursively for .tla files.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
        /// What to search for: operator (default), variable, constant, expr, action.
        #[arg(short, long, value_enum, default_value = "operator")]
        kind: SearchKind,
        /// Output format: human (default, grep-like) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: SearchOutputFormat,
    },
    /// Generate documentation from a TLA+ specification.
    ///
    /// Parses the spec and extracts structural documentation including:
    /// module-level and operator-level comments, operator signatures,
    /// variable/constant declarations, EXTENDS/INSTANCE dependencies,
    /// and cross-reference graphs (calls/called-by).
    Doc {
        /// TLA+ source file to document.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: markdown (default), html, or json.
        #[arg(long, value_enum, default_value = "markdown")]
        format: DocOutputFormat,
        /// Output file. If not specified, writes to stdout.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
    },
    /// Type check a TLA+ specification.
    ///
    /// Parses the spec, runs TIR lowering (which includes type inference),
    /// and reports inferred types for each operator. Also parses Apalache-style
    /// `@type:` annotations from TLA+ comments and reports any mismatches.
    ///
    /// Part of #3750: Apalache Gap 2 — type checker CLI.
    Typecheck {
        /// TLA+ source file to type check.
        file: PathBuf,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        output: TypecheckOutputFormat,
        /// Show inferred types for all operators, variables, and constants.
        ///
        /// Without this flag, the command only reports type errors and
        /// annotation mismatches (exit 0 = no errors). With this flag,
        /// it additionally prints the full type map for every definition
        /// in the module.
        #[arg(long)]
        infer_types: bool,
    },
    /// Analyze dependency graph of a TLA+ specification.
    ///
    /// Parses the spec and produces dependency information including:
    /// module dependencies (EXTENDS/INSTANCE), operator call graph,
    /// variable usage, root reachability, dead code detection, and
    /// circular dependency detection.
    ///
    /// Output formats: tree (default indented text), dot (Graphviz),
    /// or json (structured data for tooling).
    Deps {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: tree (default), dot, or json.
        #[arg(long, value_enum, default_value = "tree")]
        format: DepsOutputFormat,
        /// Highlight unused/unreachable operators in the output.
        #[arg(long)]
        unused: bool,
        /// Show only module-level dependencies (skip operator-level analysis).
        #[arg(long)]
        modules_only: bool,
    },
    /// Watch a TLA+ specification and re-check on file changes.
    ///
    /// Monitors the spec file and any EXTENDS'd modules for changes.
    /// On each change, re-parses and re-checks the specification,
    /// displaying results in the terminal. Debounces rapid changes
    /// (100ms) to avoid redundant re-checks during editing.
    Watch {
        /// TLA+ source file to watch and check.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of worker threads (0 = auto, 1 = sequential).
        #[arg(short, long, default_value = "0")]
        workers: usize,
        /// Disable deadlock checking.
        #[arg(long)]
        no_deadlock: bool,
        /// Debounce interval in milliseconds.
        #[arg(long, default_value = "100")]
        debounce_ms: u64,
        /// Clear terminal before each re-check.
        #[arg(long)]
        clear: bool,
    },
    /// Generate Rust code from a TLA+ specification.
    Codegen {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg) providing CONSTANTS and INVARIANTS.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output file (default: stdout).
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Use TIR-based code generation (typed intermediate representation).
        ///
        /// The TIR path benefits from type information, resolved INSTANCE
        /// references, and operator inlining. Requires --config for constant
        /// values. Part of #3729.
        #[arg(long)]
        tir: bool,
        /// Generate a production-type adapter layer (runtime checkers).
        #[arg(long)]
        checker: bool,
        /// Mapping config (TOML) for generating `impl checker::To<Spec>State for <RustType>` blocks.
        #[arg(long, value_name = "FILE")]
        checker_map: Option<PathBuf>,
        /// Generate Kani verification harnesses.
        #[arg(long)]
        kani: bool,
        /// Generate proptest property-based tests.
        #[arg(long)]
        proptest: bool,
        /// Generate a complete runnable Cargo project (directory with Cargo.toml,
        /// src/lib.rs, src/main.rs) instead of just the generated module.
        ///
        /// When combined with --kani, also generates a zani/Kani verification
        /// harness file. The output directory is created at --output (required
        /// with --scaffold).
        #[arg(long)]
        scaffold: bool,
        /// Emit a source map JSON file alongside the generated Rust code.
        ///
        /// The source map records which TLA+ operators correspond to which
        /// line ranges in the generated Rust file, enabling counterexample
        /// traces to be annotated with generated source locations.
        /// Written to `<output>.source_map.json` when --output is provided.
        #[arg(long)]
        source_map: bool,
    },
    /// Export a TLA+ specification as VMT (Verification Modulo Theories) format.
    ///
    /// VMT is an SMT-LIB2 extension used by external model checkers such as
    /// nuXmv, ic3ia, and AVR. Part of #3755.
    Vmt {
        /// TLA+ source file to export.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
    },
    /// Explain a counterexample trace from a saved JSON output file.
    ///
    /// Reads a JSON output file produced by `tla2 check --output json` and generates
    /// a human-readable step-by-step explanation of the counterexample trace.
    Explain {
        /// Path to the JSON output file from `tla2 check --output json`.
        trace_file: PathBuf,
        /// Optional TLA+ spec file for invariant structure analysis.
        #[arg(long)]
        spec: Option<PathBuf>,
        /// Optional config file (.cfg) to locate the invariant name.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Specific invariant to analyze (overrides config file).
        #[arg(long)]
        invariant: Option<String>,
        /// Show only variable changes between consecutive steps.
        #[arg(long)]
        diff: bool,
        /// Show full state dump at each step.
        #[arg(long)]
        verbose: bool,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ExplainOutputFormat,
    },
    /// Analyze action coverage from a model checking JSON output file.
    ///
    /// Reads a JSON output file produced by `tla2 check --output json` and reports
    /// which actions (Next disjuncts) were exercised during model checking, how many
    /// states each generated, and what percentage of actions were explored.
    Coverage {
        /// Path to the JSON output file from `tla2 check --output json`.
        trace_file: PathBuf,
        /// Optional TLA+ spec file for cross-referencing Next disjuncts.
        #[arg(long)]
        spec: Option<PathBuf>,
        /// Optional config file (.cfg) to locate the Next operator name.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: CoverageOutputFormat,
    },
    /// Visualize the state transition graph from a counterexample trace.
    ///
    /// Reads a JSON output file produced by `tla2 check --output json` and
    /// generates a state transition graph where each state is a node and
    /// each transition is an edge labeled with the action name.
    Graph {
        /// Path to the JSON output file from `tla2 check --output json`.
        trace_file: PathBuf,
        /// Output format: dot (default), mermaid, or json.
        #[arg(long, value_enum, default_value = "dot")]
        format: GraphOutputFormat,
        /// Maximum number of states to render (0 = unlimited, default: 50).
        #[arg(long, default_value = "50")]
        max_states: usize,
        /// Highlight error/violating states in red (default: true).
        #[arg(long, default_value = "true", action = clap::ArgAction::Set)]
        highlight_error: bool,
        /// Group states by the action that created them.
        #[arg(long)]
        cluster_by_action: bool,
    },
    /// Check a BTOR2 hardware model checking benchmark.
    ///
    /// Parses a BTOR2 file, translates each `bad` property to a CHC safety
    /// query, and dispatches to the z4-chc portfolio solver (PDR/BMC/k-induction).
    /// Output follows HWMCC convention: `sat` / `unsat` / `unknown` on stdout.
    #[cfg(feature = "z4")]
    Btor2 {
        /// BTOR2 file to check.
        file: PathBuf,
        /// Verbose output: print parse stats, per-property results, and timing.
        #[arg(short, long)]
        verbose: bool,
        /// Write HWMCC-style witness to a file (only written if a counterexample exists).
        #[arg(long, value_name = "FILE")]
        witness: Option<PathBuf>,
        /// Solver time budget in seconds (default: 27s from AdaptiveConfig).
        #[arg(long, value_name = "SECONDS")]
        timeout: Option<u64>,
        /// Bit-blast narrow bitvectors to AIGER and use the IC3/PDR engine.
        /// Automatically enabled for eligible benchmarks with bitvectors <= max-bv-width.
        #[arg(long)]
        bitblast: bool,
        /// Maximum bitvector width for bit-blasting (default: 32).
        #[arg(long, value_name = "BITS", default_value = "32")]
        max_bv_width: u32,
    },
    /// Check an AIGER hardware model checking benchmark.
    ///
    /// Parses an AIGER file (.aag or .aig), translates each bad-state literal
    /// to a safety query, and dispatches to the selected solver engine.
    /// Output follows HWMCC convention: `sat` / `unsat` / `unknown` on stdout.
    #[cfg(feature = "z4")]
    Aiger {
        /// AIGER file to check (.aag or .aig).
        file: PathBuf,
        /// Verbose output: print parse stats, per-property results, and timing.
        #[arg(short, long)]
        verbose: bool,
        /// Write HWMCC-style witness to a file (only written if a counterexample exists).
        #[arg(long, value_name = "FILE")]
        witness: Option<PathBuf>,
        /// Solver time budget in seconds.
        #[arg(long, value_name = "SECONDS")]
        timeout: Option<u64>,
        /// Solver engine: 'chc' (z4-chc portfolio), 'sat' (BMC + k-induction portfolio).
        /// Default: 'sat'.
        #[arg(long, value_name = "ENGINE", default_value = "sat")]
        engine: AigerEngine,
        /// Portfolio mode for the SAT engine (ignored when engine=chc).
        /// 'default': IC3 + BMC + k-induction (3 threads).
        /// 'full': 6 IC3 variants + BMC + k-induction (8 threads).
        /// 'competition': 8 IC3 variants + BMC + k-induction (10 threads).
        #[arg(long, value_name = "MODE", default_value = "default")]
        portfolio: AigerPortfolio,
    },
    /// Suggest repairs for invariant violations found in counterexample traces.
    ///
    /// Reads a JSON output file produced by `tla2 check --output json`, analyzes
    /// the counterexample trace, and suggests potential fixes:
    /// - Which variables changed in the violating step
    /// - What values would satisfy the invariant
    /// - Which action (Next disjunct) was taken
    /// - Minimal state change to restore the invariant
    Repair {
        /// Path to the JSON output file from `tla2 check --output json`.
        trace_file: PathBuf,
        /// TLA+ spec file for deeper analysis.
        #[arg(long)]
        spec: Option<PathBuf>,
        /// Config file (.cfg) for invariant identification.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Specific invariant to repair.
        #[arg(long)]
        invariant: Option<String>,
        /// Maximum number of repair suggestions to generate.
        #[arg(long, default_value = "5")]
        max_suggestions: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: RepairOutputFormat,
    },
    /// Profile a model checking run with timing and resource instrumentation.
    ///
    /// Runs `tla2 check` with profiling flags and reports overall statistics,
    /// per-action breakdown, operator hotspots, and BFS level statistics.
    Profile {
        /// TLA+ source file to profile.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of worker threads (0 = auto).
        #[arg(short, long, default_value = "0")]
        workers: usize,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: ProfileOutputFormat,
        /// Show top N hottest operators/metrics (default: 20).
        #[arg(long, default_value = "20")]
        top: usize,
        /// Include memory timeline (RSS snapshots over time).
        #[arg(long)]
        memory: bool,
    },
    /// Compare two TLA+ specifications at the semantic (AST) level.
    ///
    /// Parses both specs and reports added, removed, and modified operators,
    /// variable/constant declaration changes, EXTENDS changes, and invariant
    /// changes (when .cfg files are provided).
    Diff {
        /// Old (baseline) TLA+ source file.
        old: PathBuf,
        /// New (updated) TLA+ source file.
        new: PathBuf,
        /// Old configuration file (.cfg).
        #[arg(long)]
        old_config: Option<PathBuf>,
        /// New configuration file (.cfg).
        #[arg(long)]
        new_config: Option<PathBuf>,
        /// Output format: human (default, colored) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: DiffOutputFormat,
        /// Skip variable, constant, extends, and invariant diff; show only operator changes.
        #[arg(long)]
        operators_only: bool,
    },
    /// Convert between TLA+ and related formats.
    ///
    /// Supported conversions: tla-to-json (AST), json-to-tla (pretty-print),
    /// tla-to-markdown (documentation), trace-to-table (counterexample table).
    Convert {
        /// Input file.
        input: PathBuf,
        /// Input format (auto-detected from extension if omitted).
        #[arg(long, value_enum)]
        from: Option<ConvertFrom>,
        /// Output format (required).
        #[arg(long, value_enum)]
        to: ConvertTo,
        /// Output file (stdout if omitted).
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
    },
    /// Show specification statistics and complexity metrics.
    ///
    /// Parses a TLA+ spec and reports structural metrics: line counts,
    /// declaration counts, operator complexity, nesting depths, primed
    /// variable usage, UNCHANGED usage, and state-space size hints.
    Stats {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: StatsOutputFormat,
    },
    /// Generate shell completion scripts.
    ///
    /// Prints a completion script for the specified shell to stdout.
    /// Redirect the output to the appropriate location for your shell.
    Completions {
        /// Shell to generate completions for.
        shell: Shell,
    },
    /// Inspect or clear the LLVM2 on-disk compilation cache.
    ///
    /// The cache lives at `~/.cache/tla2/compiled/` (override with
    /// `TLA2_CACHE_DIR`). Each cached artifact is a native dynamic library
    /// plus a JSON sidecar keyed by `sha256(tMIR || LLVM2-version ||
    /// opt-level || target-triple)`. See design doc §7.
    Cache {
        #[command(subcommand)]
        action: CacheAction,
    },
    /// Refactor a TLA+ specification with semantic-preserving transformations.
    ///
    /// Performs AST-guided source transformations: extracting expressions into
    /// named operators, renaming identifiers, inlining simple operators, and
    /// removing unused definitions.
    Refactor {
        #[command(subcommand)]
        action: RefactorAction,
    },
    /// Snapshot testing for regression detection.
    ///
    /// Records model-checking results (status, state counts, max depth) as
    /// snapshot files, then compares future runs against them to catch regressions.
    Snapshot {
        /// TLA+ source file(s) to snapshot.
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Config file (.cfg) for single-spec snapshots.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Directory to store/read snapshot files (default: .snapshots).
        #[arg(long, default_value = ".snapshots")]
        snapshot_dir: PathBuf,
        /// Update (record) snapshots instead of checking against them.
        #[arg(long)]
        update: bool,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: SnapshotOutputFormat,
    },
    /// Binary search over a CONSTANT integer value to find the minimal
    /// configuration that triggers an invariant violation or exceeds a
    /// state-count threshold.
    Bisect {
        /// TLA+ source file to check.
        file: PathBuf,
        /// Configuration file (.cfg) to use as a template.
        #[arg(short, long)]
        config: PathBuf,
        /// Name of the CONSTANT integer to bisect over.
        #[arg(long)]
        constant: String,
        /// Lower bound of the search range (inclusive).
        #[arg(long)]
        low: i64,
        /// Upper bound of the search range (inclusive).
        #[arg(long)]
        high: i64,
        /// Bisect for the minimal value where state count exceeds this threshold.
        /// If omitted, bisects for the minimal invariant violation.
        #[arg(long, value_name = "STATES")]
        state_count: Option<u64>,
        /// Per-check timeout in seconds (0 = no timeout).
        #[arg(long, default_value = "60")]
        timeout: u64,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: BisectOutputFormat,
    },
    /// Merge two TLA+ specifications at the AST level.
    ///
    /// Applies a "patch" spec onto a "base" spec by unioning declarations
    /// and detecting operator conflicts.
    Merge {
        /// Base TLA+ source file.
        base: PathBuf,
        /// Patch TLA+ source file to merge onto the base.
        patch: PathBuf,
        /// Output file. If not specified, prints to stdout.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        /// Force merge: use patch version for all conflicting operators.
        #[arg(long)]
        force: bool,
        /// Output format: human (default) or json (structured report).
        #[arg(long, value_enum, default_value = "human")]
        format: MergeOutputFormat,
    },
    /// Deep pre-flight validation of a TLA+ specification.
    ///
    /// Runs 12 semantic validation checks (V001-V012) that catch errors
    /// before model checking: undefined operators, undeclared variables,
    /// config/spec mismatches, missing EXTENDS, arity errors, etc.
    Validate {
        /// TLA+ source file to validate.
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: ValidateOutputFormat,
        /// Treat warnings as errors (exit code 1 on any warning).
        #[arg(long)]
        strict: bool,
    },
    /// Generate a protocol template TLA+ specification.
    ///
    /// Creates a complete, runnable TLA+ spec and matching .cfg file
    /// for common distributed systems patterns.
    Template {
        /// Protocol template to generate.
        kind: TemplateKind,
        /// Module name for the generated spec (default: template kind name).
        #[arg(long, default_value = "Spec")]
        name: String,
        /// Number of processes (default: 3).
        #[arg(long, default_value = "3")]
        processes: u32,
        /// Output directory for generated files (default: current directory).
        #[arg(long, default_value = ".")]
        output_dir: PathBuf,
        /// Print to stdout instead of writing files.
        #[arg(long)]
        stdout: bool,
    },
    /// Analyze a TLA+ spec for deadlock conditions.
    ///
    /// Quick mode performs static analysis; full mode runs model checking.
    Deadlock {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Analysis mode: quick (static) or full (model checking).
        #[arg(long, value_enum, default_value = "quick")]
        mode: DeadlockMode,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: DeadlockOutputFormat,
    },
    /// Generate an abstract view of a TLA+ specification.
    ///
    /// Extracts state variables, actions, invariants, and transitions
    /// into a high-level summary suitable for documentation and review.
    Abstract {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: human (default), json, or mermaid.
        #[arg(long, value_enum, default_value = "human")]
        format: AbstractOutputFormat,
        /// Detail level: brief, normal (default), or full.
        #[arg(long, value_enum, default_value = "normal")]
        detail: AbstractDetail,
    },
    /// Import a specification from another format into TLA+.
    ///
    /// Supports JSON state machines, basic Promela, and basic Alloy.
    Import {
        /// Input file to import.
        file: PathBuf,
        /// Source format.
        #[arg(long, value_enum)]
        from: ImportFormat,
        /// Output file. If not specified, prints to stdout.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
    },
    /// Generate witness traces — concrete paths demonstrating a property.
    ///
    /// Unlike `check` which finds violations, `witness` finds positive examples
    /// showing how a state satisfying the target predicate can be reached.
    Witness {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Operator name to find a witness for (e.g., "TypeOK").
        #[arg(long)]
        target: String,
        /// Maximum search depth (default: 20).
        #[arg(long, default_value = "20")]
        max_depth: usize,
        /// Number of witness traces to find (default: 1).
        #[arg(long, default_value = "1")]
        count: usize,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: WitnessOutputFormat,
    },
    /// Compare two TLA+ specs structurally.
    ///
    /// Shows semantic differences: added/removed/modified operators,
    /// variables, constants, EXTENDS, and INSTANCE declarations.
    Compare {
        /// Left (base) TLA+ file.
        left: PathBuf,
        /// Right (new) TLA+ file.
        right: PathBuf,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: CompareOutputFormat,
    },
    /// Inline INSTANCE modules into a self-contained TLA+ file.
    ///
    /// Resolves INSTANCE declarations by finding and inlining the
    /// referenced module's operators, variables, and constants.
    Inline {
        /// TLA+ source file.
        file: PathBuf,
        /// Output file. If not specified, prints to stdout.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        /// Keep comments from inlined modules.
        #[arg(long)]
        keep_comments: bool,
    },
    /// Scope and dependency graph analysis for a TLA+ specification.
    ///
    /// Parses a spec and produces a detailed scope analysis: operator
    /// call graph, variable reads/writes, constant usage, dead operators,
    /// and reachability from Init/Next/invariants.
    Scope {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Output format: human (default), json, or dot.
        #[arg(long, value_enum, default_value = "human")]
        format: ScopeOutputFormat,
    },
    /// Generate constrained TLC config files by analyzing a TLA+ spec.
    ///
    /// Three strategies: minimize (smallest useful constants), incremental
    /// (progressively larger configs), symmetric (add SYMMETRY declarations).
    Constrain {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg) to read/modify.
        #[arg(short, long)]
        config: PathBuf,
        /// Constraining strategy: minimize (default), incremental, or symmetric.
        #[arg(long, value_enum, default_value = "minimize")]
        strategy: ConstrainStrategy,
        /// Output directory for generated configs (incremental mode).
        #[arg(short, long, value_name = "DIR")]
        output: Option<PathBuf>,
    },
    /// Comprehensive project-level audit of a TLA+ specification directory.
    ///
    /// Scans a directory for .tla and .cfg files and runs structural checks:
    /// spec/config pairing, parse validation, naming conventions, complexity
    /// metrics, anti-pattern detection, and config completeness.
    Audit {
        /// Directory to audit (default: current directory).
        #[arg(default_value = ".")]
        dir: PathBuf,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: AuditOutputFormat,
    },
    /// Analyze symmetry properties of CONSTANT sets.
    ///
    /// Detects which model-value sets are used symmetrically (no ordering,
    /// no distinguished elements) and suggests SYMMETRY declarations to
    /// reduce the state space.
    Symmetry {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: SymmetryOutputFormat,
    },
    /// Analyze state space partitioning for parallel/distributed checking.
    ///
    /// Identifies natural partitioning boundaries by analyzing variable
    /// domains, action independence, and symmetry classes.
    Partition {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of partitions to suggest (default: 4).
        #[arg(long, default_value = "4")]
        partitions: usize,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: PartitionOutputFormat,
    },
    /// Run simulation traces and produce a statistical coverage report.
    ///
    /// Generates N random walks, collects action frequency distributions,
    /// variable value ranges, coverage estimates, and identifies "cold"
    /// actions that are rarely or never fired.
    #[command(name = "sim-report")]
    SimReport {
        /// TLA+ source file to simulate.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Number of simulation traces (default: 1000).
        #[arg(short, long, default_value = "1000")]
        num_traces: usize,
        /// Maximum depth per trace (default: 100).
        #[arg(short, long, default_value = "100")]
        max_depth: usize,
        /// Output format: human (default) or json.
        #[arg(long, value_enum, default_value = "human")]
        format: SimReportOutputFormat,
    },
    /// Generate targeted traces matching specific patterns.
    ///
    /// Unlike `check` (which finds violations) or `simulate` (which explores
    /// randomly), `trace-gen` generates traces matching specific patterns:
    /// target (reach a predicate), coverage (cover all actions), or random.
    #[command(name = "trace-gen")]
    TraceGen {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Trace generation mode.
        #[arg(long, value_enum, default_value = "target")]
        mode: TraceGenMode,
        /// Target predicate expression (required for target mode).
        #[arg(long)]
        target: Option<String>,
        /// Number of traces to generate (default: 10).
        #[arg(long, default_value = "10")]
        count: usize,
        /// Maximum trace depth (default: 100).
        #[arg(long, default_value = "100")]
        max_depth: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: TraceGenOutputFormat,
    },
    /// Generate candidate invariants from spec structure.
    ///
    /// Analyzes Init/Next to suggest type invariants, range preservation,
    /// monotonicity, conservation laws, and mutual exclusion patterns.
    #[command(name = "inv-gen")]
    InvGen {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Quick-check each candidate with a bounded model check.
        #[arg(long)]
        verify: bool,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: InvGenOutputFormat,
    },
    /// Analyze action dependencies and conflicts.
    ///
    /// Decomposes the Next relation into individual actions and builds a
    /// dependency graph showing enables/disables, conflicts, and independence
    /// relationships. Independent actions are POR ample-set candidates.
    #[command(name = "action-graph")]
    ActionGraph {
        /// TLA+ source file to analyze.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format: human (default), json, or dot.
        #[arg(long, value_enum, default_value = "human")]
        format: ActionGraphOutputFormat,
    },
    /// Refinement checking — verify one spec refines another.
    ///
    /// Checks simulation relation: every implementation behavior, when mapped
    /// through the refinement mapping, must be a valid abstract behavior.
    Refine {
        /// Implementation TLA+ file.
        #[arg(name = "impl-file")]
        impl_file: PathBuf,
        /// Abstract TLA+ file.
        #[arg(name = "abstract-file")]
        abstract_file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Refinement mapping file.
        #[arg(short, long)]
        mapping: Option<PathBuf>,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: RefineOutputFormat,
    },
    /// Compare two TLA+ specifications structurally.
    ///
    /// Shows what operators, variables, and invariants changed between spec
    /// versions, with impact analysis on verification obligations.
    #[command(name = "model-diff")]
    ModelDiff {
        /// Old TLA+ file.
        #[arg(name = "old-file")]
        old_file: PathBuf,
        /// New TLA+ file.
        #[arg(name = "new-file")]
        new_file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ModelDiffOutputFormat,
    },
    /// Filter and query states from a model checking run.
    ///
    /// Explores state space via bounded BFS and finds states matching
    /// user-specified filter predicates. Reports matching states with traces.
    #[command(name = "state-filter")]
    StateFilter {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Filter expression (TLA+ predicate evaluated against each state).
        #[arg(short, long)]
        filter: String,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Maximum matching states to report (default: 100).
        #[arg(long, default_value = "100")]
        max_results: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: StateFilterOutputFormat,
    },
    /// Analyze lasso-shaped counterexamples for liveness violations.
    ///
    /// Decomposes a liveness violation trace into a stem (finite prefix)
    /// and loop (repeating cycle), reporting the lasso structure.
    Lasso {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Temporal property to check (overrides .cfg).
        #[arg(short, long)]
        property: Option<String>,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: LassoOutputFormat,
    },
    /// Compositional assume-guarantee verification.
    ///
    /// Decomposes the specification into action groups and verifies each
    /// group independently, checking that assumptions between groups hold.
    #[command(name = "assume-guarantee")]
    AssumeGuarantee {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Maximum states to explore per group (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: AssumeGuaranteeOutputFormat,
    },
    /// Predicate abstraction analysis.
    ///
    /// Constructs an abstract model by tracking boolean predicates over
    /// the state, reporting abstraction metrics and compression ratio.
    #[command(name = "predicate-abs")]
    PredicateAbs {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Additional predicate expressions.
        #[arg(short, long)]
        predicate: Vec<String>,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: PredicateAbsOutputFormat,
    },
    /// State space census — explore states and report statistics.
    ///
    /// Reports variable count, total states, initial states, max depth,
    /// and exploration status.
    Census {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: CensusOutputFormat,
    },
    /// Equivalence checking between two TLA+ specifications.
    ///
    /// Runs model checking on both specs and compares state counts,
    /// depth, and initial states to determine if they produce identical
    /// state spaces.
    Equiv {
        /// First TLA+ source file.
        #[arg(name = "file-a")]
        file_a: PathBuf,
        /// Second TLA+ source file.
        #[arg(name = "file-b")]
        file_b: PathBuf,
        /// Configuration file for spec A (.cfg).
        #[arg(long)]
        config_a: Option<PathBuf>,
        /// Configuration file for spec B (.cfg).
        #[arg(long)]
        config_b: Option<PathBuf>,
        /// Maximum states to explore per spec (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: EquivOutputFormat,
    },
    /// Inductive invariant checking.
    ///
    /// Verifies whether a candidate invariant holds over all reachable
    /// states. Reports whether the invariant is maintained by Init and
    /// all transitions.
    Induct {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Name of the candidate invariant operator.
        #[arg(short, long)]
        invariant: String,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: InductOutputFormat,
    },
    /// Specification slicing — extract the relevant portion for a target.
    ///
    /// Computes the transitive dependency closure of a target operator,
    /// identifying which variables, operators, and constants are needed.
    Slice {
        /// TLA+ source file.
        file: PathBuf,
        /// Target operator name to slice for.
        #[arg(short, long)]
        target: String,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: SliceOutputFormat,
    },
    /// Reachability analysis for a target predicate.
    ///
    /// Checks whether the negation of a target predicate is reachable
    /// by adding it as an invariant and looking for violations.
    Reach {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Target predicate operator name.
        #[arg(short, long)]
        target: String,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ReachOutputFormat,
    },
    /// Parallel composition analysis of two TLA+ specs.
    ///
    /// Analyzes two specifications for composition compatibility,
    /// reports shared variables and interface analysis.
    Compose {
        /// First TLA+ source file.
        #[arg(name = "file-a")]
        file_a: PathBuf,
        /// Second TLA+ source file.
        #[arg(name = "file-b")]
        file_b: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ComposeOutputFormat,
    },
    /// Unfold operator definitions, showing expanded bodies.
    ///
    /// Displays the body of a target operator and its transitive
    /// dependencies up to a configurable depth.
    Unfold {
        /// TLA+ source file.
        file: PathBuf,
        /// Target operator name to unfold.
        #[arg(short, long)]
        target: String,
        /// Maximum unfolding depth (default: 5).
        #[arg(long, default_value = "5")]
        max_depth: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: UnfoldOutputFormat,
    },
    /// Project state space onto a variable subset.
    ///
    /// Explores the state space and reports statistics for a projection
    /// onto a user-specified subset of variables.
    Project {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Variables to project onto.
        #[arg(short, long, required = true)]
        variable: Vec<String>,
        /// Maximum states to explore (default: 100000).
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ProjectOutputFormat,
    },
    /// Estimate state space bounds from type information.
    ///
    /// Analyzes Init predicate structure and config to compute
    /// upper bounds on the state space size.
    Bound {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: BoundOutputFormat,
    },
    /// Run a specification in a sandboxed environment with resource limits.
    ///
    /// Checks a TLA+ spec with configurable state/depth/time limits
    /// and reports whether exploration stayed within bounds.
    Sandbox {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Maximum BFS depth.
        #[arg(long, default_value = "100")]
        max_depth: usize,
        /// Timeout in seconds.
        #[arg(long, default_value = "30")]
        timeout: u64,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: SandboxOutputFormat,
    },
    /// Analyze temporal behavior timeline of a specification.
    ///
    /// Extracts actions from the Next relation, identifies temporal
    /// properties, invariants, and fairness constraints.
    Timeline {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: TimelineOutputFormat,
    },
    /// Compute structural complexity metrics for a specification.
    ///
    /// Reports operator count, nesting depth, expression size,
    /// variable count, quantifiers, and prime expressions.
    Metric {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: MetricOutputFormat,
    },
    /// Generate a configuration file scaffold from a specification.
    ///
    /// Analyzes the spec to detect Init/Next, constants, invariant
    /// candidates, and produces a .cfg file.
    Scaffold {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ScaffoldOutputFormat,
    },
    /// Analyze stuttering and UNCHANGED patterns.
    ///
    /// Reports which variables each action primes, detects stuttering
    /// steps, and flags variables that are never modified.
    Stutter {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: StutterOutputFormat,
    },
    /// Detect quorum and majority patterns in distributed specs.
    ///
    /// Scans for Cardinality thresholds, SUBSET selections, voting
    /// variables, and quorum-related operators.
    Quorum {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: QuorumOutputFormat,
    },
    /// Compute state fingerprints for debugging and comparison.
    ///
    /// Runs model checking to a limit and reports an aggregate
    /// fingerprint of the state space for cross-implementation comparison.
    Fingerprint {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "10000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: FingerprintOutputFormat,
    },
    /// Normalize a specification to canonical form.
    ///
    /// Outputs the spec with sorted constants, variables, and operators
    /// in a canonical ordering for diffing and comparison.
    Normalize {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: NormalizeOutputFormat,
    },
    /// Analyze counterexamples from model checking.
    ///
    /// Runs model checking and classifies any violation found by type,
    /// trace length, and involved variables.
    Countex {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: CountexOutputFormat,
    },
    /// State space exploration heatmap.
    ///
    /// Shows per-action complexity contribution to the state space.
    Heatmap {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "10000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: HeatmapOutputFormat,
    },
    /// Detect distributed protocol patterns.
    ///
    /// Scans for message passing, leader election, consensus,
    /// mutual exclusion, and state machine patterns.
    Protocol {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ProtocolOutputFormat,
    },
    /// Display operator call hierarchy.
    ///
    /// Builds and visualizes the call graph between operators,
    /// showing roots, leaves, and dependency chains.
    Hierarchy {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: HierarchyOutputFormat,
    },
    /// Build a cross-reference index of definitions and usages.
    ///
    /// Shows where each operator, variable, and constant is defined
    /// and which operators reference it. Flags unused definitions.
    Crossref {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: CrossrefOutputFormat,
    },
    /// Generate invariant candidates from spec structure.
    ///
    /// Analyzes Init constraints, variable types, and naming patterns
    /// to suggest invariant formulas for model checking.
    Invariantgen {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: InvariantgenOutputFormat,
    },
    /// Detect specification drift between two versions.
    ///
    /// Compares two TLA+ files and reports added, removed, and
    /// modified operators, variables, and constants.
    Drift {
        /// First (baseline) TLA+ source file.
        file_a: PathBuf,
        /// Second (current) TLA+ source file.
        file_b: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: DriftOutputFormat,
    },
    /// Analyze safety properties and invariants.
    ///
    /// Reports configured invariants, classifies them by type,
    /// and suggests additional invariant candidates.
    Safety {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: SafetyOutputFormat,
    },
    /// Analyze liveness properties and fairness constraints.
    ///
    /// Reports temporal properties, classifies them (leads-to,
    /// recurrence, stability), and detects fairness.
    #[command(name = "liveness-check")]
    LivenessCheck {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: LivenesscheckOutputFormat,
    },
    /// Translate specification to pseudocode.
    ///
    /// Converts TLA+ operators into readable pseudocode with
    /// assignments, conditions, and loops.
    Translate {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: TranslateOutputFormat,
    },
    /// Display liveness tableau construction.
    ///
    /// Analyzes temporal properties and shows the tableau structure
    /// used for liveness checking, including SCC requirements.
    Tableau {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: TableauOutputFormat,
    },
    /// Extract the action alphabet from the Next relation.
    ///
    /// Lists all distinct actions with their parameter counts.
    Alphabet {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: AlphabetOutputFormat,
    },
    /// Compute action weights for guided search.
    ///
    /// Assigns weights based on structural complexity and variable
    /// coverage for use in heuristic-guided model checking.
    Weight {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: WeightOutputFormat,
    },
    /// Absorb constant values from config into the spec.
    ///
    /// Reads constant assignments and displays operators with
    /// constants replaced by their configured values.
    Absorb {
        /// TLA+ source file.
        file: PathBuf,
        /// Configuration file (.cfg).
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: AbsorbOutputFormat,
    },
    /// Cluster operators by variable affinity.
    ///
    /// Groups operators that reference the same variables,
    /// identifying natural functional clusters.
    Cluster {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ClusterOutputFormat,
    },
    /// Rename an identifier across the specification.
    ///
    /// Performs word-boundary-aware renaming of operators,
    /// variables, or constants.
    Rename {
        /// TLA+ source file.
        file: PathBuf,
        /// Current name of the identifier.
        #[arg(long)]
        from: String,
        /// New name for the identifier.
        #[arg(long)]
        to: String,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: RenameOutputFormat,
    },
    /// Reachable state set summary.
    ///
    /// Runs bounded model checking and reports summary statistics
    /// about the reachable state set.
    Reachset {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "1000000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ReachsetOutputFormat,
    },
    /// Extract enabling conditions (guards) from actions.
    ///
    /// Analyzes each action in the Next-state relation to identify
    /// the enabling condition (guard).
    Guard {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: GuardOutputFormat,
    },
    /// Detect potential symmetry in a specification.
    ///
    /// Analyzes constants, variables, and operators to identify
    /// potential symmetry sets for the SYMMETRY keyword.
    #[command(name = "symmetry-detect")]
    SymmetryDetect {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: SymmetrydetectOutputFormat,
    },
    /// Verify deadlock freedom with diagnostics.
    ///
    /// Runs model checking focused on deadlock detection and provides
    /// detailed analysis of deadlock states when found.
    #[command(name = "deadlock-free")]
    DeadlockFree {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "1000000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: DeadlockfreeOutputFormat,
    },
    /// Count transitions per action in the Next-state relation.
    ///
    /// Analyzes the structure of Next to identify and count
    /// individual action disjuncts.
    #[command(name = "action-count")]
    ActionCount {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ActioncountOutputFormat,
    },
    /// Validate constant assignments between spec and config.
    ///
    /// Checks that all CONSTANT declarations have assignments
    /// and no config assignments reference non-existent constants.
    #[command(name = "const-check")]
    ConstCheck {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ConstcheckOutputFormat,
    },
    /// Comprehensive specification information summary.
    ///
    /// Displays module name, EXTENDS, constants, variables, operators,
    /// and structural statistics.
    #[command(name = "spec-info")]
    SpecInfo {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: SpecinfoOutputFormat,
    },
    /// Track variable read/write usage across operators.
    ///
    /// For each variable, identifies which operators read (unprimed)
    /// and write (primed) it.
    #[command(name = "var-track")]
    VarTrack {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: VartrackOutputFormat,
    },
    /// Generate a .cfg configuration file from spec analysis.
    ///
    /// Produces Init/Next, constant declarations, and invariant
    /// candidates by analyzing the spec.
    #[command(name = "cfg-gen")]
    CfgGen {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: CfggenOutputFormat,
    },
    /// Operator dependency graph.
    ///
    /// Produces a dependency graph showing which operators
    /// call which other operators.
    #[command(name = "dep-graph")]
    DepGraph {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: DepgraphOutputFormat,
    },
    /// Count initial states.
    ///
    /// Enumerates initial states and reports the count without
    /// running full model checking.
    #[command(name = "init-count")]
    InitCount {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: InitcountOutputFormat,
    },
    /// Compute average branching factor of the state graph.
    ///
    /// Runs bounded model checking and reports the average number
    /// of successor states per state.
    #[command(name = "branch-factor")]
    BranchFactor {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "100000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: BranchfactorOutputFormat,
    },
    /// Export state graph summary.
    ///
    /// Runs bounded model checking and exports state graph statistics.
    #[command(name = "state-graph")]
    StateGraph {
        /// TLA+ source file.
        file: PathBuf,
        /// Path to a .cfg configuration file.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Maximum number of states to explore.
        #[arg(long, default_value = "10000")]
        max_states: usize,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: StategraphOutputFormat,
    },
    /// Extract and classify predicates.
    ///
    /// Identifies boolean-valued operators and classifies them
    /// as state predicates, action predicates, or temporal formulas.
    Predicate {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: PredicateOutputFormat,
    },
    /// Display module structure and metadata.
    ///
    /// Shows module name, EXTENDS list, and unit counts by type.
    #[command(name = "module-info")]
    ModuleInfo {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ModuleinfoOutputFormat,
    },
    /// List operators with their arities.
    ///
    /// Extracts all operator definitions and displays their names
    /// and parameter counts.
    #[command(name = "op-arity")]
    OpArity {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: OparityOutputFormat,
    },
    /// Detect unused variables.
    ///
    /// Identifies variables declared in VARIABLE that are never
    /// referenced in any operator body.
    #[command(name = "unused-var")]
    UnusedVar {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: UnusedvarOutputFormat,
    },
    /// Count expression nodes by type.
    ///
    /// Walks the AST and counts how many nodes of each expression
    /// type appear, providing a structural complexity profile.
    #[command(name = "expr-count")]
    ExprCount {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ExprcountOutputFormat,
    },
    /// Specification size metrics.
    ///
    /// Reports line counts, character counts, and structural
    /// size metrics.
    #[command(name = "spec-size")]
    SpecSize {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: SpecsizeOutputFormat,
    },
    /// List all CONSTANT declarations.
    ///
    /// Extracts and displays all CONSTANT declarations
    /// including their arity.
    #[command(name = "const-list")]
    ConstList {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ConstlistOutputFormat,
    },
    /// List all VARIABLE declarations.
    ///
    /// Extracts and displays all VARIABLE declarations.
    #[command(name = "var-list")]
    VarList {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: VarlistOutputFormat,
    },
    /// Detect unused constants.
    #[command(name = "unused-const")]
    UnusedConst {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: UnusedconstOutputFormat,
    },
    /// Compute maximum AST nesting depth per operator.
    #[command(name = "ast-depth")]
    AstDepth {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: AstdepthOutputFormat,
    },
    /// List all operator definitions.
    #[command(name = "op-list")]
    OpList {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: OplistOutputFormat,
    },
    /// List EXTENDS dependencies.
    Extends {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: ExtendsOutputFormat,
    },
    /// Count set operation usage.
    #[command(name = "set-ops")]
    SetOps {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: SetopsOutputFormat,
    },
    /// Count quantifier usage per operator.
    #[command(name = "quant-count")]
    QuantCount {
        /// TLA+ source file.
        file: PathBuf,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        format: QuantcountOutputFormat,
    },
    /// Count primed variable references per operator.
    #[command(name = "prime-count")]
    PrimeCount {
        file: PathBuf,
        #[arg(long, value_enum, default_value = "human")]
        format: PrimecountOutputFormat,
    },
    /// Count IF-THEN-ELSE expressions per operator.
    #[command(name = "if-count")]
    IfCount {
        file: PathBuf,
        #[arg(long, value_enum, default_value = "human")]
        format: IfcountOutputFormat,
    },
    /// Count LET-IN definitions per operator.
    #[command(name = "let-count")]
    LetCount {
        file: PathBuf,
        #[arg(long, value_enum, default_value = "human")]
        format: LetcountOutputFormat,
    },
    /// Count CHOOSE expressions.
    #[command(name = "choose-count")]
    ChooseCount { file: PathBuf, #[arg(long, value_enum, default_value = "human")] format: ChoosecountOutputFormat },
    /// Count CASE expressions.
    #[command(name = "case-count")]
    CaseCount { file: PathBuf, #[arg(long, value_enum, default_value = "human")] format: CasecountOutputFormat },
    /// Count record/function operations.
    #[command(name = "record-ops")]
    RecordOps { file: PathBuf, #[arg(long, value_enum, default_value = "human")] format: RecordopsOutputFormat },
    /// Count temporal operator usage.
    #[command(name = "temporal-ops")]
    TemporalOps { file: PathBuf, #[arg(long, value_enum, default_value = "human")] format: TemporalopsOutputFormat },
    /// Find UNCHANGED clauses and their variables.
    Unchanged { file: PathBuf, #[arg(long, value_enum, default_value = "human")] format: UnchangedOutputFormat },
    /// Find ENABLED expressions.
    Enabled { file: PathBuf, #[arg(long, value_enum, default_value = "human")] format: EnabledOutputFormat },
    /// Check a concurrent model (ConcurrentModel JSON from tRust).
    ///
    /// Reads a ConcurrentModel JSON file, generates a TLA+ module, runs the
    /// model checker, and reports verification results with source-mapped
    /// counterexamples.
    #[command(name = "thread-check")]
    ThreadCheck {
        /// Path to ConcurrentModel JSON file.
        file: PathBuf,
        /// Number of BFS worker threads (0 = auto).
        #[arg(long, default_value = "0")]
        workers: usize,
        /// Maximum states to explore (0 = unlimited).
        #[arg(long, default_value = "0")]
        max_states: usize,
        /// Maximum BFS depth (0 = unlimited).
        #[arg(long, default_value = "0")]
        max_depth: usize,
        /// Print generated TLA+ module to stdout.
        #[arg(long)]
        emit_tla: bool,
        /// Output format.
        #[arg(long, value_enum, default_value = "human")]
        output: ThreadCheckOutputFormat,
    },
}

/// Subcommands for `tla2 cache` — LLVM2 on-disk compilation cache.
///
/// The cache stores compiled tMIR modules at
/// `~/.cache/tla2/compiled/<digest>.{dylib,so,dll}` plus a JSON sidecar
/// describing the compilation context. See design doc §7.
#[derive(Debug, Subcommand)]
pub(crate) enum CacheAction {
    /// Remove all cached artifacts under `~/.cache/tla2/compiled/`.
    ///
    /// Prints a per-extension count of removed files. Safe to run while
    /// other `tla2` processes are not actively loading artifacts (each
    /// artifact is self-contained once loaded).
    Clear,
    /// List cached artifacts with their digests, opt levels, and sizes.
    ///
    /// Reads the JSON sidecars without touching the dynamic libraries,
    /// so it is cheap even for large caches.
    List,
    /// Print the cache root directory and exit. Respects `TLA2_CACHE_DIR`.
    Path,
}

/// Refactoring action subcommands for `tla2 refactor`.
#[derive(Debug, Subcommand)]
pub(crate) enum RefactorAction {
    /// Extract an expression into a new named operator.
    #[command(name = "extract-operator")]
    ExtractOperator {
        /// TLA+ source file to refactor.
        #[arg(long)]
        file: PathBuf,
        /// Expression text to extract (must appear verbatim in the source).
        #[arg(long)]
        expr: String,
        /// Name for the new operator.
        #[arg(long)]
        name: String,
        /// Write output to a file instead of showing a diff.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        /// Modify the file in place.
        #[arg(long, conflicts_with = "output")]
        in_place: bool,
        /// Skip the preview diff output.
        #[arg(long)]
        no_preview: bool,
    },
    /// Rename an operator, variable, or constant throughout the spec.
    Rename {
        /// TLA+ source file to refactor.
        #[arg(long)]
        file: PathBuf,
        /// Current name of the operator/variable/constant.
        #[arg(long)]
        from: String,
        /// New name to replace it with.
        #[arg(long)]
        to: String,
        /// Write output to a file instead of showing a diff.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        /// Modify the file in place.
        #[arg(long, conflicts_with = "output")]
        in_place: bool,
        /// Skip the preview diff output.
        #[arg(long)]
        no_preview: bool,
    },
    /// Inline a simple (zero-parameter) operator.
    Inline {
        /// TLA+ source file to refactor.
        #[arg(long)]
        file: PathBuf,
        /// Name of the operator to inline.
        #[arg(long)]
        name: String,
        /// Write output to a file instead of showing a diff.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        /// Modify the file in place.
        #[arg(long, conflicts_with = "output")]
        in_place: bool,
        /// Skip the preview diff output.
        #[arg(long)]
        no_preview: bool,
    },
    /// Remove all unused operators from the spec.
    Cleanup {
        /// TLA+ source file to refactor.
        #[arg(long)]
        file: PathBuf,
        /// Configuration file (.cfg). If not specified, looks for `<file>.cfg`.
        #[arg(short, long)]
        config: Option<PathBuf>,
        /// Write output to a file instead of showing a diff.
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        /// Modify the file in place.
        #[arg(long, conflicts_with = "output")]
        in_place: bool,
        /// Skip the preview diff output.
        #[arg(long)]
        no_preview: bool,
    },
}

#[derive(Debug, clap::Args)]
pub(crate) struct DiagnoseArgs {
    /// Path to spec_baseline.json.
    #[arg(long, default_value = "tests/tlc_comparison/spec_baseline.json")]
    pub baseline: PathBuf,
    /// Output format: human (default) or json.
    #[arg(long, value_enum, default_value = "human")]
    pub output: DiagnoseOutputFormat,
    /// Default timeout in seconds for specs without a baseline override.
    /// Per-spec `diagnose_timeout_seconds` in the baseline can extend beyond
    /// this value for slow specs. Default is 1800s (30 min).
    #[arg(long, default_value = "1800")]
    pub timeout: u64,
    /// Filter by category (small, medium, large, xlarge).
    #[arg(long)]
    pub category: Option<String>,
    /// Run only specific spec(s) by name. Can be repeated.
    #[arg(long, conflicts_with = "spec_list")]
    pub spec: Vec<String>,
    /// Read spec names from a file (one per line, # comments, blank lines skipped).
    #[arg(long, conflicts_with = "spec")]
    pub spec_list: Option<PathBuf>,
    /// Retry timed-out specs up to N times. Specs that pass on retry are
    /// classified as `flaky_timeout` instead of `timeout`.
    #[arg(long, default_value = "0")]
    pub retries: u32,
    /// Number of concurrent spec runs (minimum 1).
    #[arg(long, default_value = "1")]
    pub parallel: usize,
    /// Inner checker worker count for each `tla2 check` subprocess.
    /// Omit to preserve baseline parity mode (`--workers 1 --continue-on-error`).
    /// Use 0 for adaptive/auto, 1 for explicit sequential, or N > 1 for explicit parallel.
    #[arg(long, value_name = "N")]
    pub checker_workers: Option<usize>,
    /// Update tla2 fields in baseline after run.
    #[arg(long)]
    pub update_baseline: bool,
    /// Root directory for tlaplus-examples/specifications.
    #[arg(long)]
    pub examples_dir: Option<PathBuf>,
    /// Exit with code 1 if any spec has a state count mismatch.
    /// FlakyTimeout and Skip do NOT trigger failure.
    #[arg(long)]
    pub fail_on_mismatch: bool,
    /// Exit with code 1 if any spec does not pass.
    /// FlakyTimeout and Skip do NOT trigger failure.
    #[arg(long)]
    pub fail_on_non_pass: bool,
    /// Write metrics JSON to a file. If no path given, writes to metrics/spec_coverage.json.
    /// Can combine with --output human.
    #[arg(long, value_name = "PATH", num_args = 0..=1, default_missing_value = "metrics/spec_coverage.json")]
    pub output_metrics: Option<PathBuf>,
    /// Differential oracle harness mode (#4252 Stream 6).
    ///
    /// `off` (default): interpreter only. `compare`: run interpreter AND
    /// LLVM2 for each spec, record divergences to `metrics/oracle_parity.json`.
    /// `fail-closed`: like compare but also exit non-zero on any divergence.
    /// Can also be set via `TLA2_ORACLE={off|compare|fail-closed}`. The CLI
    /// flag takes precedence over the env var.
    #[arg(long, value_enum, value_name = "MODE")]
    pub oracle_mode: Option<DiagnoseOracleMode>,
    /// Output path for oracle parity report JSON. Defaults to
    /// `metrics/oracle_parity.json`. Only used when `--oracle-mode` is
    /// `compare` or `fail-closed`.
    #[arg(long, value_name = "PATH")]
    pub oracle_output: Option<PathBuf>,
}
