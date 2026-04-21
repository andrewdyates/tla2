// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Op interface registry — capability-based polymorphism for dialect ops.
//!
//! Ported from MLIR's `OpInterface` concept (see
//! [`designs/2026-04-18-mlir-ideas-to-llvm2.md`](../../../designs/2026-04-18-mlir-ideas-to-llvm2.md)
//! §"Idea 4: Op Interfaces"). Instead of passes enumerating op kinds
//! ("`VerifFingerprintBatch` is parallel, `VerifBfsStep` is not"), ops
//! declare capability interfaces. Passes query capabilities, not op kinds.
//!
//! This is the *minimum viable interface registry* — one trait per
//! capability, ops `impl` each trait they support, and a tiny `Capabilities`
//! snapshot that passes consume. We deliberately avoid a runtime
//! `dyn`-object registry (MLIR's TypeID lookup table) because Rust's coherence
//! rules make static `impl` checks free and type-safe.
//!
//! # Canonical capability predicate
//!
//! Per supremacy plan §5 (GPU auto-promotion): an op is GPU-eligible iff
//!
//! ```text
//! Pure  ∧  HasParallelism  ∧  DivergenceClass ≤ Low
//! ```
//!
//! Passes call [`is_gpu_eligible`] on a [`Capabilities`] snapshot; adding a
//! new op that implements these three interfaces becomes GPU-eligible
//! automatically — no `KernelExtract` allowlist edits required.
//!
//! # Anti-scope
//!
//! - Not a general MLIR-completeness port. We ship the three canonical
//!   capabilities referenced by the GPU/KernelExtract acceptance criterion.
//!   More interfaces (`IsReduction`, `MemoryRole`, `HasBoundedLoops`, …)
//!   follow the same template and can be added without API churn.
//! - No dynamic registration. Ops opt in via `impl` blocks at the op
//!   definition site. A pass that wants to query a brand-new capability
//!   adds the trait here and the `impl` on the op — two edits, fully
//!   checked by `rustc`.

/// Marker trait: op has no observable side effects.
///
/// A pure op can be duplicated, re-ordered, or eliminated if its result is
/// unused. Analogous to MLIR's `SideEffectFree` / `Pure`.
///
/// Ops that mutate shared state (seen-set insertion, frontier push,
/// counterexample trace emit) do **not** implement `Pure`.
pub trait Pure {}

/// Marker trait: op's semantics permit data-parallel execution.
///
/// An op with `HasParallelism` can be executed over many independent
/// elements concurrently (SIMD lane, GPU warp, thread pool task).
/// `VerifFingerprintBatch` is the canonical example: fingerprinting `count`
/// independent states is embarrassingly parallel.
///
/// Serial-only ops (scheduler records, control flow, BFS worker-loop
/// boundaries) do **not** implement `HasParallelism`.
pub trait HasParallelism {}

/// Divergence class — how much control flow within the op can diverge
/// across lanes/workers.
///
/// GPU-eligibility requires `≤ Low`. CPU SIMD can tolerate `Low`. `High`
/// divergence ops stay on the scalar path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Divergence {
    /// All lanes follow the same control-flow path.
    Uniform = 0,
    /// Limited intra-lane branching (bounded loops, small conditionals).
    Low = 1,
    /// Arbitrary branching across lanes — unsuitable for SIMD/GPU mapping.
    High = 2,
}

/// Trait: op self-reports its divergence class.
///
/// Unlike `Pure` / `HasParallelism` (which are markers), divergence is a
/// value — an op may be `Uniform` at some dialect levels and `Low` at
/// others. The trait returns it at interface-query time.
pub trait DivergenceClass {
    /// The op's divergence class.
    fn divergence(&self) -> Divergence;
}

// -----------------------------------------------------------------------------
// Capability snapshot
// -----------------------------------------------------------------------------

/// Snapshot of an op's capability interfaces for pass consumption.
///
/// Built by the op's `capabilities()` method (see the [`HasCapabilities`]
/// trait below). Passes inspect this snapshot instead of calling each
/// interface's methods directly — this is the handoff between ops and
/// passes.
///
/// Fields are deliberately `bool` + `Option<Divergence>` rather than
/// `dyn`-erased interface pointers: ops declare capabilities at compile
/// time, and this snapshot captures that declaration for runtime
/// routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Capabilities {
    /// `true` iff the op implements [`Pure`].
    pub pure_: bool,
    /// `true` iff the op implements [`HasParallelism`].
    pub parallel: bool,
    /// `Some(d)` iff the op implements [`DivergenceClass`]; `None` means
    /// the op did not declare a divergence class (treated as
    /// worst-case `Divergence::High` by [`is_gpu_eligible`]).
    pub divergence: Option<Divergence>,
}

impl Capabilities {
    /// An op that declares no capabilities.
    #[must_use]
    pub const fn none() -> Self {
        Self {
            pure_: false,
            parallel: false,
            divergence: None,
        }
    }

    /// Set the `Pure` capability.
    #[must_use]
    pub const fn with_pure(mut self) -> Self {
        self.pure_ = true;
        self
    }

    /// Set the `HasParallelism` capability.
    #[must_use]
    pub const fn with_parallelism(mut self) -> Self {
        self.parallel = true;
        self
    }

    /// Set the divergence class.
    #[must_use]
    pub const fn with_divergence(mut self, d: Divergence) -> Self {
        self.divergence = Some(d);
        self
    }
}

/// Trait that every op with declared capabilities implements.
///
/// Separated from [`crate::DialectOp`] so ops without any interface
/// declarations do not pay for a blanket default impl — they simply do
/// not implement `HasCapabilities`. Pass-level queries go through the
/// free-function router [`op_capabilities`] which takes a concrete op by
/// generic parameter.
pub trait HasCapabilities {
    /// Snapshot of the op's capability interfaces.
    fn capabilities(&self) -> Capabilities;
}

// -----------------------------------------------------------------------------
// Kernel-extraction predicate
// -----------------------------------------------------------------------------

/// GPU-eligibility predicate. Supremacy plan §5: an op migrates to a GPU
/// kernel iff it is pure, data-parallel, and has uniform-or-low
/// divergence.
///
/// Returns `false` if any required interface is missing. Passes never
/// need to inspect `Capabilities` fields directly — they call this
/// predicate.
#[must_use]
pub fn is_gpu_eligible(caps: &Capabilities) -> bool {
    caps.pure_ && caps.parallel && matches!(caps.divergence, Some(d) if d <= Divergence::Low)
}

/// Convenience: directly query a `HasCapabilities` op for GPU eligibility.
///
/// Equivalent to `is_gpu_eligible(&op.capabilities())`.
#[must_use]
pub fn op_is_gpu_eligible<T: HasCapabilities>(op: &T) -> bool {
    is_gpu_eligible(&op.capabilities())
}

// -----------------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Stand-in op with no capabilities.
    struct NoCaps;
    impl HasCapabilities for NoCaps {
        fn capabilities(&self) -> Capabilities {
            Capabilities::none()
        }
    }

    /// Stand-in op that is Pure + HasParallelism + Uniform divergence.
    struct PureParallelUniform;
    impl Pure for PureParallelUniform {}
    impl HasParallelism for PureParallelUniform {}
    impl DivergenceClass for PureParallelUniform {
        fn divergence(&self) -> Divergence {
            Divergence::Uniform
        }
    }
    impl HasCapabilities for PureParallelUniform {
        fn capabilities(&self) -> Capabilities {
            Capabilities::none()
                .with_pure()
                .with_parallelism()
                .with_divergence(self.divergence())
        }
    }

    /// Stand-in op that is Pure + Parallel but High divergence (GPU-ineligible).
    struct PureParallelHigh;
    impl Pure for PureParallelHigh {}
    impl HasParallelism for PureParallelHigh {}
    impl DivergenceClass for PureParallelHigh {
        fn divergence(&self) -> Divergence {
            Divergence::High
        }
    }
    impl HasCapabilities for PureParallelHigh {
        fn capabilities(&self) -> Capabilities {
            Capabilities::none()
                .with_pure()
                .with_parallelism()
                .with_divergence(self.divergence())
        }
    }

    #[test]
    fn capabilities_none_is_not_gpu_eligible() {
        let caps = Capabilities::none();
        assert!(!is_gpu_eligible(&caps));
    }

    #[test]
    fn capabilities_builder_sets_fields() {
        let caps = Capabilities::none()
            .with_pure()
            .with_parallelism()
            .with_divergence(Divergence::Low);
        assert!(caps.pure_);
        assert!(caps.parallel);
        assert_eq!(caps.divergence, Some(Divergence::Low));
    }

    #[test]
    fn divergence_ordering_matches_declaration() {
        assert!(Divergence::Uniform < Divergence::Low);
        assert!(Divergence::Low < Divergence::High);
    }

    #[test]
    fn gpu_eligible_requires_all_three_interfaces() {
        // Only Pure — not eligible.
        let c = Capabilities::none().with_pure();
        assert!(!is_gpu_eligible(&c));
        // Pure + parallel but missing divergence — not eligible.
        let c = Capabilities::none().with_pure().with_parallelism();
        assert!(!is_gpu_eligible(&c));
        // Full triple with Uniform — eligible.
        let c = Capabilities::none()
            .with_pure()
            .with_parallelism()
            .with_divergence(Divergence::Uniform);
        assert!(is_gpu_eligible(&c));
        // Full triple with Low — still eligible (boundary case).
        let c = Capabilities::none()
            .with_pure()
            .with_parallelism()
            .with_divergence(Divergence::Low);
        assert!(is_gpu_eligible(&c));
        // Full triple with High — NOT eligible.
        let c = Capabilities::none()
            .with_pure()
            .with_parallelism()
            .with_divergence(Divergence::High);
        assert!(!is_gpu_eligible(&c));
    }

    #[test]
    fn op_is_gpu_eligible_matches_manual_snapshot() {
        let op = PureParallelUniform;
        assert!(op_is_gpu_eligible(&op));
        assert!(is_gpu_eligible(&op.capabilities()));
    }

    #[test]
    fn high_divergence_op_is_not_gpu_eligible() {
        let op = PureParallelHigh;
        assert!(!op_is_gpu_eligible(&op));
    }

    #[test]
    fn no_caps_op_is_not_gpu_eligible() {
        let op = NoCaps;
        assert!(!op_is_gpu_eligible(&op));
    }

    /// Kernel-extract style pass: given a heterogeneous list of ops,
    /// partition GPU-eligible ones from scalar ones. This is the
    /// acceptance-test pattern from issue #4253: adding a new op that
    /// implements `Pure+HasParallelism+DivergenceClass(Low)` becomes
    /// GPU-eligible without modifying the pass.
    fn gpu_partition(caps: &[Capabilities]) -> (usize, usize) {
        let gpu = caps.iter().filter(|c| is_gpu_eligible(c)).count();
        let scalar = caps.len() - gpu;
        (gpu, scalar)
    }

    #[test]
    fn pass_level_partition_uses_capabilities_not_op_kind() {
        let caps = [
            PureParallelUniform.capabilities(),
            PureParallelHigh.capabilities(),
            NoCaps.capabilities(),
            PureParallelUniform.capabilities(),
        ];
        let (gpu, scalar) = gpu_partition(&caps);
        assert_eq!(gpu, 2);
        assert_eq!(scalar, 2);
    }
}
