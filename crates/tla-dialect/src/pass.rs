// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pass infrastructure for progressive lowering.
//!
//! A [`DialectPass`] transforms a vector of ops from one dialect into a
//! vector of ops in the next dialect down the tower. The
//! [`PassManager`] chains passes in order and validates the dialect
//! boundaries between them.
//!
//! Today the framework ships two passes — `tla -> verif` and `verif -> llvm`
//! (leaf-only) — as required by the skeleton. More passes, folding hooks, and
//! a pattern-rewrite system can be added in follow-up issues without breaking
//! this API.

use crate::{DialectError, DialectOp, Lowered};

/// Transform ops from `from_dialect` to `to_dialect`.
pub trait DialectPass {
    #[allow(clippy::wrong_self_convention)] // dialect "from/to" is meaningful, not a conversion
    fn from_dialect(&self) -> &'static str;
    fn to_dialect(&self) -> &'static str;
    /// Run the pass. Input ops must all be in `from_dialect`. Output ops must
    /// all be in `to_dialect` — unless `to_dialect == "llvm"`, in which case
    /// leaf-only output is permitted (i.e. the pass has terminated lowering
    /// at the `verif -> llvm` boundary; leaves are not `DialectOp`s).
    fn run(&self, ops: Vec<Box<dyn DialectOp>>) -> Result<PassOutput, DialectError>;
}

/// Output of a pass — either more ops (continue the tower) or leaves
/// (terminal backend).
#[derive(Debug)]
pub enum PassOutput {
    Ops(Vec<Box<dyn DialectOp>>),
    Leaves(Vec<crate::LlvmLeaf>),
}

// -----------------------------------------------------------------------------
// TlaToVerifPass
// -----------------------------------------------------------------------------

/// Lower every `tla::` op in the input by delegating to the op's
/// [`DialectOp::lower`] method and collecting the produced `verif::` ops.
#[derive(Debug, Default)]
pub struct TlaToVerifPass;

impl DialectPass for TlaToVerifPass {
    fn from_dialect(&self) -> &'static str {
        "tla"
    }
    fn to_dialect(&self) -> &'static str {
        "verif"
    }
    fn run(&self, ops: Vec<Box<dyn DialectOp>>) -> Result<PassOutput, DialectError> {
        let mut out: Vec<Box<dyn DialectOp>> = Vec::with_capacity(ops.len());
        for op in ops {
            if op.dialect() != "tla" {
                return Err(DialectError::DialectMismatch {
                    expected: "tla",
                    actual: op.dialect(),
                });
            }
            match op.lower()? {
                Lowered::Ops(children) => {
                    for child in children {
                        if child.dialect() != "verif" {
                            return Err(DialectError::LoweringFailed {
                                dialect: "tla",
                                op: op.op_name(),
                                message: format!(
                                    "tla op must lower to verif, got {}",
                                    child.dialect()
                                ),
                            });
                        }
                        out.push(child);
                    }
                }
                Lowered::Leaf(_) => {
                    return Err(DialectError::LoweringFailed {
                        dialect: "tla",
                        op: op.op_name(),
                        message: "tla op must not lower directly to a leaf".into(),
                    });
                }
            }
        }
        Ok(PassOutput::Ops(out))
    }
}

// -----------------------------------------------------------------------------
// VerifToLlvmPass
// -----------------------------------------------------------------------------

/// Lower every `verif::` op to its terminal [`LlvmLeaf`]. In the skeleton the
/// leaf is always `LlvmLeaf::Todo(...)`; future backends will produce richer
/// structured emit records.
#[derive(Debug, Default)]
pub struct VerifToLlvmPass;

impl DialectPass for VerifToLlvmPass {
    fn from_dialect(&self) -> &'static str {
        "verif"
    }
    fn to_dialect(&self) -> &'static str {
        "llvm"
    }
    fn run(&self, ops: Vec<Box<dyn DialectOp>>) -> Result<PassOutput, DialectError> {
        let mut leaves = Vec::with_capacity(ops.len());
        for op in ops {
            if op.dialect() != "verif" {
                return Err(DialectError::DialectMismatch {
                    expected: "verif",
                    actual: op.dialect(),
                });
            }
            match op.lower()? {
                Lowered::Ops(_) => {
                    return Err(DialectError::LoweringFailed {
                        dialect: "verif",
                        op: op.op_name(),
                        message: "verif op must lower to a leaf".into(),
                    });
                }
                Lowered::Leaf(leaf) => leaves.push(leaf),
            }
        }
        Ok(PassOutput::Leaves(leaves))
    }
}

// -----------------------------------------------------------------------------
// PassManager
// -----------------------------------------------------------------------------

/// Ordered collection of passes. Validates that adjacent passes agree on the
/// dialect handoff.
#[derive(Default)]
pub struct PassManager {
    passes: Vec<Box<dyn DialectPass>>,
}

impl PassManager {
    pub fn new() -> Self {
        Self { passes: Vec::new() }
    }

    /// Add a pass to the end of the pipeline.
    pub fn add(&mut self, pass: Box<dyn DialectPass>) -> &mut Self {
        self.passes.push(pass);
        self
    }

    /// Run the full pipeline over `ops`. Every pass is applied in order.
    /// The intermediate output of each pass must be a `PassOutput::Ops` whose
    /// ops are in the *next* pass's `from_dialect()`. Only the final pass may
    /// produce `PassOutput::Leaves`.
    pub fn run(&self, ops: Vec<Box<dyn DialectOp>>) -> Result<PassOutput, DialectError> {
        let n = self.passes.len();
        if n == 0 {
            return Ok(PassOutput::Ops(ops));
        }
        let mut current: PassOutput = PassOutput::Ops(ops);
        for (i, pass) in self.passes.iter().enumerate() {
            let is_last = i == n - 1;
            current = match current {
                PassOutput::Ops(o) => pass.run(o)?,
                PassOutput::Leaves(_) => {
                    return Err(DialectError::LoweringFailed {
                        dialect: pass.from_dialect(),
                        op: "<pass-manager>",
                        message: "cannot apply pass to leaf-only output".into(),
                    });
                }
            };
            if !is_last {
                if let PassOutput::Leaves(_) = current {
                    return Err(DialectError::LoweringFailed {
                        dialect: pass.to_dialect(),
                        op: "<pass-manager>",
                        message: "intermediate pass produced leaves; only the final pass may"
                            .into(),
                    });
                }
            }
        }
        Ok(current)
    }
}

impl std::fmt::Debug for PassManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names: Vec<(&'static str, &'static str)> = self
            .passes
            .iter()
            .map(|p| (p.from_dialect(), p.to_dialect()))
            .collect();
        f.debug_struct("PassManager")
            .field("passes", &names)
            .finish()
    }
}

// -----------------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::TlaInit;
    use crate::verif::{BfsKind, VerifBfsStep};
    use crate::LlvmLeaf;

    #[test]
    fn tla_to_verif_pass_expands_init() {
        let pass = TlaToVerifPass;
        let init: Box<dyn DialectOp> = Box::new(TlaInit::new(vec!["x".into()], 0));
        let out = pass.run(vec![init]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].dialect(), "verif");
                assert_eq!(ops[0].op_name(), "verif.bfs_step");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn tla_to_verif_pass_rejects_wrong_dialect() {
        let pass = TlaToVerifPass;
        let op: Box<dyn DialectOp> = Box::new(VerifBfsStep {
            kind: BfsKind::Expand,
            action_id: 0,
            ..Default::default()
        });
        let err = pass.run(vec![op]).unwrap_err();
        assert!(matches!(
            err,
            DialectError::DialectMismatch {
                expected: "tla",
                actual: "verif"
            }
        ));
    }

    #[test]
    fn verif_to_llvm_pass_emits_leaves() {
        let pass = VerifToLlvmPass;
        let op: Box<dyn DialectOp> = Box::new(VerifBfsStep {
            kind: BfsKind::Seed,
            action_id: 0,
            ..Default::default()
        });
        let out = pass.run(vec![op]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(leaves.len(), 1);
                assert!(matches!(
                    leaves[0],
                    LlvmLeaf::BfsStep {
                        kind: 0,
                        action_id: 0,
                        ..
                    }
                ));
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn pass_manager_chains_tla_to_verif_to_llvm() {
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let init: Box<dyn DialectOp> = Box::new(TlaInit::new(vec!["x".into()], 0));
        let out = pm.run(vec![init]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(leaves.len(), 1);
                assert!(matches!(leaves[0], LlvmLeaf::BfsStep { kind: 0, .. }));
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn pass_manager_empty_pipeline_is_identity() {
        let pm = PassManager::new();
        let init: Box<dyn DialectOp> = Box::new(TlaInit::new(vec!["x".into()], 0));
        let out = pm.run(vec![init]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].dialect(), "tla");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn pass_manager_rejects_leaves_feeding_next_pass() {
        // Construct a pipeline where VerifToLlvmPass runs before another pass.
        // The second pass should never execute — error should surface as
        // LoweringFailed when we try to feed leaves into the next pass.
        let mut pm = PassManager::new();
        pm.add(Box::new(VerifToLlvmPass));
        pm.add(Box::new(VerifToLlvmPass));
        let op: Box<dyn DialectOp> = Box::new(VerifBfsStep {
            kind: BfsKind::Expand,
            action_id: 0,
            ..Default::default()
        });
        let err = pm.run(vec![op]).unwrap_err();
        assert!(matches!(err, DialectError::LoweringFailed { .. }));
    }

    #[test]
    fn pass_manager_debug_includes_dialect_pairs() {
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let dbg = format!("{pm:?}");
        assert!(dbg.contains("tla"));
        assert!(dbg.contains("verif"));
        assert!(dbg.contains("llvm"));
    }

    // -------------------------------------------------------------------------
    // Wave 12 end-to-end pass tests: `tla::` arith/bool/cmp -> verif:: sequence.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_to_verif_pass_expands_add() {
        // `tla.add(x, y)` with var_ref operands lowers to the 3-op sequence
        // [verif.scalar_int, verif.scalar_int, verif.int_add].
        use crate::tla::{TlaAdd, TlaVarRef};
        let pass = TlaToVerifPass;
        let add: Box<dyn DialectOp> = Box::new(TlaAdd::new(
            Box::new(TlaVarRef::new("x")),
            Box::new(TlaVarRef::new("y")),
        ));
        let out = pass.run(vec![add]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 3);
                assert_eq!(ops[0].op_name(), "verif.scalar_int");
                assert_eq!(ops[1].op_name(), "verif.scalar_int");
                assert_eq!(ops[2].op_name(), "verif.int_add");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn tla_to_verif_pass_expands_nested_and_of_eqs() {
        // `(x = y) /\ (a = b)` — stresses recursive lowering: the outer
        // `tla.and` should lower via two `tla.eq` operands, each of which
        // lowers through two `tla.var_ref`s. Final flat sequence:
        //   [scalar_int, scalar_int, int_eq,
        //    scalar_int, scalar_int, int_eq,
        //    bool_and]  (length 7)
        use crate::tla::{TlaAnd, TlaEq, TlaVarRef};
        let pass = TlaToVerifPass;
        let eq1 = Box::new(TlaEq::new(
            Box::new(TlaVarRef::new("x")),
            Box::new(TlaVarRef::new("y")),
        )) as Box<dyn DialectOp>;
        let eq2 = Box::new(TlaEq::new(
            Box::new(TlaVarRef::new("a")),
            Box::new(TlaVarRef::new("b")),
        )) as Box<dyn DialectOp>;
        let and_op: Box<dyn DialectOp> = Box::new(TlaAnd::new(eq1, eq2));
        let out = pass.run(vec![and_op]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 7);
                let names: Vec<&str> = ops.iter().map(|o| o.op_name()).collect();
                assert_eq!(
                    names,
                    vec![
                        "verif.scalar_int",
                        "verif.scalar_int",
                        "verif.int_eq",
                        "verif.scalar_int",
                        "verif.scalar_int",
                        "verif.int_eq",
                        "verif.bool_and",
                    ]
                );
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn tla_to_verif_pass_expands_not() {
        // Unary `tla.not(x)` lowers to the 2-op sequence
        // [verif.scalar_int, verif.bool_not].
        use crate::tla::{TlaNot, TlaVarRef};
        let pass = TlaToVerifPass;
        let not_op: Box<dyn DialectOp> = Box::new(TlaNot::new(Box::new(TlaVarRef::new("p"))));
        let out = pass.run(vec![not_op]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 2);
                assert_eq!(ops[0].op_name(), "verif.scalar_int");
                assert_eq!(ops[1].op_name(), "verif.bool_not");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn pass_manager_lowers_arith_all_the_way_to_leaves() {
        // End-to-end: `tla.add(x, y)` -> verif ops -> llvm leaves.
        // Final leaves are `scalar_int, scalar_int, int_add`.
        // Wave 14 TL3h: `int_add` is now a structured `LlvmLeaf::IntAdd` unit variant,
        // not a `Todo("int_add")` placeholder.
        use crate::tla::{TlaAdd, TlaVarRef};
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let add: Box<dyn DialectOp> = Box::new(TlaAdd::new(
            Box::new(TlaVarRef::new("x")),
            Box::new(TlaVarRef::new("y")),
        ));
        let out = pm.run(vec![add]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(leaves.len(), 3);
                assert!(matches!(leaves[0], LlvmLeaf::ScalarInt { .. }));
                assert!(matches!(leaves[1], LlvmLeaf::ScalarInt { .. }));
                assert_eq!(leaves[2], LlvmLeaf::IntAdd);
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn tla_to_verif_pass_propagates_lowering_failure_for_unlowered_operand() {
        // `TlaSetRef.lower()` still returns NotImplemented; an arith op
        // enclosing a set_ref operand must surface that error — the pass
        // should NOT swallow it.
        use crate::tla::{TlaAdd, TlaSetRef, TlaVarRef};
        let pass = TlaToVerifPass;
        let op: Box<dyn DialectOp> = Box::new(TlaAdd::new(
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaVarRef::new("y")),
        ));
        let err = pass.run(vec![op]).unwrap_err();
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.set_ref"
            }
        ));
    }

    // -------------------------------------------------------------------------
    // Wave 13 pass tests — verification primitives through the full pipeline.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_to_verif_pass_expands_fingerprint() {
        // `tla.fingerprint(slot=3)` lowers to a single `verif.state_fingerprint`.
        use crate::tla::TlaFingerprint;
        let pass = TlaToVerifPass;
        let op: Box<dyn DialectOp> = Box::new(TlaFingerprint::new(3));
        let out = pass.run(vec![op]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].op_name(), "verif.state_fingerprint");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn tla_to_verif_pass_expands_invariant() {
        // `tla.invariant("TypeOK", id=1)` lowers to a single
        // `verif.invariant_check`.
        use crate::tla::TlaInvariant;
        let pass = TlaToVerifPass;
        let op: Box<dyn DialectOp> = Box::new(TlaInvariant::new("TypeOK", 1));
        let out = pass.run(vec![op]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].op_name(), "verif.invariant_check");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn pass_manager_lowers_fingerprint_all_the_way_to_leaf() {
        // End-to-end: `tla.fingerprint` -> `verif.state_fingerprint` ->
        // `LlvmLeaf::StateFingerprint`. Graduated Wave 14 TL3d (#4286).
        use crate::tla::TlaFingerprint;
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let op: Box<dyn DialectOp> = Box::new(TlaFingerprint::new(0));
        let out = pm.run(vec![op]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![LlvmLeaf::StateFingerprint {
                        state_slot: 0,
                        depth: 0,
                    }]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn pass_manager_lowers_invariant_all_the_way_to_leaf() {
        // End-to-end: `tla.invariant` -> `verif.invariant_check` ->
        // `LlvmLeaf::InvariantCheck`. Graduated Wave 14 TL3d (#4286).
        use crate::tla::TlaInvariant;
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let op: Box<dyn DialectOp> = Box::new(TlaInvariant::new("SafetyP", 0));
        let out = pm.run(vec![op]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![LlvmLeaf::InvariantCheck {
                        invariant_id: 0,
                        state_slot: 0,
                        depth: 0,
                    }]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn pass_manager_lowers_spec_like_batch() {
        // End-to-end mini-spec: Init -> Fingerprint -> InvariantCheck.
        // Exercises the "batch of heterogeneous tla ops" scenario that a real
        // spec-to-IR lowering produces. Expected leaves (in order):
        //   [bfs_step, state_fingerprint, invariant_check].
        // The latter two are now structured (Wave 14 TL3d, #4286).
        use crate::tla::{TlaFingerprint, TlaInit, TlaInvariant};
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let ops: Vec<Box<dyn DialectOp>> = vec![
            Box::new(TlaInit::new(vec!["x".into()], 0)),
            Box::new(TlaFingerprint::new(0)),
            Box::new(TlaInvariant::new("TypeOK", 0)),
        ];
        let out = pm.run(ops).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(leaves.len(), 3);
                assert!(matches!(leaves[0], LlvmLeaf::BfsStep { kind: 0, .. }));
                assert_eq!(
                    leaves[1],
                    LlvmLeaf::StateFingerprint {
                        state_slot: 0,
                        depth: 0,
                    }
                );
                assert_eq!(
                    leaves[2],
                    LlvmLeaf::InvariantCheck {
                        invariant_id: 0,
                        state_slot: 0,
                        depth: 0,
                    }
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn verif_to_llvm_pass_handles_wave13_primitives() {
        // Direct `verif::` dialect primitives (not via tla lowering) flow
        // through VerifToLlvmPass. After the Wave 14 TL3 graduation (#4286),
        // frontier_drain + fingerprint_batch lower to structured leaves that
        // carry their full field set, not `Todo(...)` placeholders.
        use crate::verif::{VerifFingerprintBatch, VerifFrontierDrain};
        let pass = VerifToLlvmPass;
        let ops: Vec<Box<dyn DialectOp>> = vec![
            Box::new(VerifFrontierDrain::new_on_worker(128, 2)),
            Box::new(VerifFingerprintBatch::new_at_depth(0, 32, 4)),
        ];
        let out = pass.run(ops).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![
                        LlvmLeaf::FrontierDrain {
                            max: 128,
                            worker_id: 2,
                        },
                        LlvmLeaf::FingerprintBatch {
                            state_base: 0,
                            count: 32,
                            depth: 4,
                        },
                    ]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3 pass tests — graduated structured lowering end-to-end
    // through the VerifToLlvmPass (#4286).
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3_frontier_drain_batch_pass_preserves_fields() {
        // A heterogeneous batch of graduated ops should preserve every field
        // across the pass boundary. The pass must not reorder, rewrite, or
        // drop fields.
        use crate::verif::{VerifFingerprintBatch, VerifFrontierDrain};
        let pass = VerifToLlvmPass;
        let ops: Vec<Box<dyn DialectOp>> = vec![
            Box::new(VerifFrontierDrain::new_on_worker(1, 0)),
            Box::new(VerifFrontierDrain::new_on_worker(u32::MAX, u32::MAX)),
            Box::new(VerifFingerprintBatch::new_at_depth(10, 1, 0)),
            Box::new(VerifFingerprintBatch::new_at_depth(
                u32::MAX,
                u32::MAX,
                u32::MAX,
            )),
        ];
        let out = pass.run(ops).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(leaves.len(), 4);
                assert_eq!(
                    leaves[0],
                    LlvmLeaf::FrontierDrain {
                        max: 1,
                        worker_id: 0
                    }
                );
                assert_eq!(
                    leaves[1],
                    LlvmLeaf::FrontierDrain {
                        max: u32::MAX,
                        worker_id: u32::MAX,
                    }
                );
                assert_eq!(
                    leaves[2],
                    LlvmLeaf::FingerprintBatch {
                        state_base: 10,
                        count: 1,
                        depth: 0,
                    }
                );
                assert_eq!(
                    leaves[3],
                    LlvmLeaf::FingerprintBatch {
                        state_base: u32::MAX,
                        count: u32::MAX,
                        depth: u32::MAX,
                    }
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn wave14_tl3_pass_propagates_verify_errors_from_graduated_ops() {
        // A zero-max drain / zero-count batch must surface as
        // DialectError::VerifyFailed through the pass, never silently produce
        // a bogus leaf.
        use crate::verif::VerifFrontierDrain;
        let pass = VerifToLlvmPass;
        let ops: Vec<Box<dyn DialectOp>> = vec![Box::new(VerifFrontierDrain::new_on_worker(0, 4))];
        let err = pass.run(ops).unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3e pass tests (#4286) — graduated tla-level ops thread their
    // depth + state_slot fields all the way to the terminal LlvmLeaf.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3e_pass_manager_preserves_tla_fingerprint_depth() {
        // End-to-end: tla.fingerprint(slot=5, depth=17) ->
        // verif.state_fingerprint(slot=5, depth=17) ->
        // LlvmLeaf::StateFingerprint { state_slot: 5, depth: 17 }.
        // Graduated Wave 14 TL3e — previously the depth field was 0-defaulted
        // by the tla -> verif lowering.
        use crate::tla::TlaFingerprint;
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let op: Box<dyn DialectOp> = Box::new(TlaFingerprint::new_at_depth(5, 17));
        let out = pm.run(vec![op]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![LlvmLeaf::StateFingerprint {
                        state_slot: 5,
                        depth: 17,
                    }]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn wave14_tl3e_pass_manager_preserves_tla_invariant_state_slot_and_depth() {
        // End-to-end: tla.invariant("SafetyP", id=7, slot=13, depth=25) ->
        // verif.invariant_check(id=7, slot=13, depth=25) ->
        // LlvmLeaf::InvariantCheck { invariant_id: 7, state_slot: 13,
        // depth: 25 }. Graduated Wave 14 TL3e — previously slot + depth
        // were 0-defaulted by the tla -> verif lowering.
        use crate::tla::TlaInvariant;
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let op: Box<dyn DialectOp> = Box::new(TlaInvariant::new_at_depth("SafetyP", 7, 13, 25));
        let out = pm.run(vec![op]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![LlvmLeaf::InvariantCheck {
                        invariant_id: 7,
                        state_slot: 13,
                        depth: 25,
                    }]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn wave14_tl3e_pass_manager_lowers_depth_carrying_spec_batch() {
        // Heterogeneous batch: the graduated tla surface ops preserve every
        // field through a two-step pipeline. Uses distinct depths per op to
        // prove field-by-field propagation, not a shared fallback.
        use crate::tla::{TlaFingerprint, TlaInit, TlaInvariant};
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let ops: Vec<Box<dyn DialectOp>> = vec![
            Box::new(TlaInit::new(vec!["x".into()], 0)),
            Box::new(TlaFingerprint::new_at_depth(2, 1)),
            Box::new(TlaInvariant::new_at_depth("TypeOK", 3, 4, 5)),
        ];
        let out = pm.run(ops).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(leaves.len(), 3);
                assert!(matches!(leaves[0], LlvmLeaf::BfsStep { kind: 0, .. }));
                assert_eq!(
                    leaves[1],
                    LlvmLeaf::StateFingerprint {
                        state_slot: 2,
                        depth: 1,
                    }
                );
                assert_eq!(
                    leaves[2],
                    LlvmLeaf::InvariantCheck {
                        invariant_id: 3,
                        state_slot: 4,
                        depth: 5,
                    }
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3f pass tests (#4286) — TlaActionEval + TlaEnabled thread
    // their full field sets through the two-step pipeline to the terminal
    // LlvmLeaf::ActionEval / LlvmLeaf::EnabledCheck variants.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_to_verif_pass_expands_action_eval() {
        // `tla.action_eval("Send", id=3, slot=5, depth=7, worker=2)` lowers to
        // a single `verif.action_eval` carrying all fields.
        use crate::tla::TlaActionEval;
        let pass = TlaToVerifPass;
        let op: Box<dyn DialectOp> = Box::new(TlaActionEval::new_at_depth("Send", 3, 5, 7, 2));
        let out = pass.run(vec![op]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].op_name(), "verif.action_eval");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn tla_to_verif_pass_expands_enabled() {
        // `tla.enabled("Ack", id=4, slot=6, depth=9)` lowers to a single
        // `verif.enabled_check`.
        use crate::tla::TlaEnabled;
        let pass = TlaToVerifPass;
        let op: Box<dyn DialectOp> = Box::new(TlaEnabled::new_at_depth("Ack", 4, 6, 9));
        let out = pass.run(vec![op]).unwrap();
        match out {
            PassOutput::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].op_name(), "verif.enabled_check");
            }
            PassOutput::Leaves(_) => panic!("expected ops, got leaves"),
        }
    }

    #[test]
    fn wave14_tl3f_pass_manager_preserves_tla_action_eval_fields() {
        // End-to-end: tla.action_eval("Send", id=3, slot=5, depth=7, worker=2)
        // -> verif.action_eval -> LlvmLeaf::ActionEval. All four numeric
        // fields must survive.
        use crate::tla::TlaActionEval;
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let op: Box<dyn DialectOp> = Box::new(TlaActionEval::new_at_depth("Send", 3, 5, 7, 2));
        let out = pm.run(vec![op]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![LlvmLeaf::ActionEval {
                        action_id: 3,
                        source_slot: 5,
                        depth: 7,
                        worker_id: 2,
                    }]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn wave14_tl3f_pass_manager_preserves_tla_enabled_fields() {
        // End-to-end: tla.enabled("Ack", id=4, slot=6, depth=9) ->
        // verif.enabled_check -> LlvmLeaf::EnabledCheck. All three numeric
        // fields must survive.
        use crate::tla::TlaEnabled;
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        let op: Box<dyn DialectOp> = Box::new(TlaEnabled::new_at_depth("Ack", 4, 6, 9));
        let out = pm.run(vec![op]).unwrap();
        match out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![LlvmLeaf::EnabledCheck {
                        action_id: 4,
                        state_slot: 6,
                        depth: 9,
                    }]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }

    #[test]
    fn wave14_tl3f_pass_manager_propagates_verify_errors() {
        // `tla.action_eval` with `action_id == 0` must surface as a
        // DialectError::VerifyFailed from the pipeline — the pass must NOT
        // silently emit a bogus leaf. Same for `tla.enabled` with 0 id.
        use crate::tla::{TlaActionEval, TlaEnabled};
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));

        let bad_action: Box<dyn DialectOp> = Box::new(TlaActionEval::new("Next", 0));
        let err = pm.run(vec![bad_action]).unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));

        let bad_enabled: Box<dyn DialectOp> = Box::new(TlaEnabled::new("Send", 0));
        let err = pm.run(vec![bad_enabled]).unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave14_tl3f_pass_manager_lowers_full_bfs_worker_batch() {
        // A realistic BFS worker loop batch: dequeue (frontier_drain) ->
        // evaluate action (action_eval) -> check enabled (enabled_check) ->
        // fingerprint successor (state_fingerprint) -> check invariant
        // (invariant_check). Every op is graduated; every field propagates.
        use crate::tla::{TlaActionEval, TlaEnabled, TlaFingerprint, TlaInvariant};
        use crate::verif::VerifFrontierDrain;
        let mut pm = PassManager::new();
        pm.add(Box::new(TlaToVerifPass));
        pm.add(Box::new(VerifToLlvmPass));
        // Note: VerifFrontierDrain is a verif-level op, so we run the pipeline
        // *starting* from verif. Instead we run two separate pipelines here
        // and interleave leaves manually — a real driver would chain them.
        let tla_ops: Vec<Box<dyn DialectOp>> = vec![
            Box::new(TlaActionEval::new_at_depth("Send", 1, 10, 2, 0)),
            Box::new(TlaEnabled::new_at_depth("Send", 1, 10, 2)),
            Box::new(TlaFingerprint::new_at_depth(11, 3)),
            Box::new(TlaInvariant::new_at_depth("TypeOK", 5, 11, 3)),
        ];
        let tla_out = pm.run(tla_ops).unwrap();
        let expected = vec![
            LlvmLeaf::ActionEval {
                action_id: 1,
                source_slot: 10,
                depth: 2,
                worker_id: 0,
            },
            LlvmLeaf::EnabledCheck {
                action_id: 1,
                state_slot: 10,
                depth: 2,
            },
            LlvmLeaf::StateFingerprint {
                state_slot: 11,
                depth: 3,
            },
            LlvmLeaf::InvariantCheck {
                invariant_id: 5,
                state_slot: 11,
                depth: 3,
            },
        ];
        match tla_out {
            PassOutput::Leaves(leaves) => assert_eq!(leaves, expected),
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
        // Sanity: the pure verif-level pass also graduates drain on its own.
        let verif_pass = VerifToLlvmPass;
        let drain_out = verif_pass
            .run(vec![Box::new(VerifFrontierDrain::new_on_worker(64, 0))])
            .unwrap();
        match drain_out {
            PassOutput::Leaves(leaves) => {
                assert_eq!(
                    leaves,
                    vec![LlvmLeaf::FrontierDrain {
                        max: 64,
                        worker_id: 0,
                    }]
                );
            }
            PassOutput::Ops(_) => panic!("expected leaves, got ops"),
        }
    }
}
