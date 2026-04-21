// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla::` dialect — TLA+ operators.
//!
//! Ops at this level correspond to TLA+ semantic concepts: `Init`, `Next`,
//! actions, state references, invariants, fingerprints. They lower to the
//! `verif::` dialect, which expresses the verification primitives (BFS steps,
//! fingerprint calls, invariant checks).
//!
//! # Skeleton contents
//!
//! - [`TlaInit`] — concrete, exercises the full `DialectOp` + lowering path.
//! - [`TlaSetUnion`] — first populated expression op. Binary set union
//!   (`left \union right`). Structural verify + pretty-print wired; lowering
//!   deferred (returns `NotImplemented`) until the `tla -> verif` expression
//!   path lands in a later wave under epic #4251.
//! - [`TlaSetIntersect`] — binary set intersection (`left \intersect right`).
//!   Mirror of [`TlaSetUnion`]. Same operand discipline, deferred lowering.
//! - [`TlaSetCardinality`] — unary cardinality (`Cardinality(S)`). Expression
//!   op producing an integer from a set-valued operand.
//! - [`TlaSetMember`] — binary membership test (`x \in S`). Expression op
//!   producing a boolean. Operand kind rules are identical to set_union.
//! - [`TlaAnd`], [`TlaOr`] — binary boolean connectives (`/\`, `\/`). Wave 7
//!   population. Expression ops producing a boolean from two boolean-valued
//!   operands.
//! - [`TlaNot`] — unary boolean negation (`~expr`). Wave 7 population.
//! - [`TlaEq`] — binary value equality (`lhs = rhs`). Wave 7 population.
//!   Expression op producing a boolean from two value-valued operands.
//! - [`TlaIfThenElse`] — ternary conditional expression (`IF p THEN a ELSE b`).
//!   Wave 8 population. Three expression operands.
//! - [`TlaVarRef`] — named primed-variable target for `TlaAssign`. Wave 8
//!   operand primitive, paralleling [`TlaSetRef`].
//! - [`TlaAssign`] — primed-variable assignment (`v' = expr`). Wave 8
//!   population. First `OpKind::StateTransform` non-stub op.
//! - [`TlaLt`], [`TlaLe`], [`TlaGt`], [`TlaGe`] — integer comparison ops
//!   (`<`, `<=`, `>`, `>=`). Wave 9 population. Binary expressions yielding
//!   a boolean from two integer-valued operands.
//! - [`TlaAdd`], [`TlaSub`], [`TlaMul`], [`TlaDiv`], [`TlaMod`] — integer
//!   arithmetic ops (`+`, `-`, `*`, `\div`, `%`). Wave 9 population. Binary
//!   expressions yielding an integer from two integer-valued operands.
//! - [`TlaAction`] — named action (`<name>: <body>`). Wave 10 population.
//!   First compound `OpKind::StateTransform` op — body is a conjunctive
//!   tree of `TlaAssign` + guard operands (or a pure guard expression).
//! - [`TlaNext`] — next-state disjunction (`Next == A1 \/ A2 \/ ...`).
//!   Wave 10 population. Vector of `TlaAction` children; every element
//!   must be a state-transform op.
//! - [`TlaExists`], [`TlaForall`] — bounded quantifiers
//!   (`\E v \in S : P(v)`, `\A v \in S : P(v)`). Wave 11 population.
//!   Three-operand expression ops; variable operand must be a `TlaVarRef`.
//! - [`TlaChoose`] — Hilbert choice (`CHOOSE v \in S : P(v)`). Wave 11
//!   population. Value-producing (not a boolean predicate).
//! - [`TlaSetBuilder`] — set-filter comprehension
//!   (`{ v \in S : P(v) }`). Wave 11 population. Produces a set.
//! - [`TlaSetMap`] — set-map comprehension
//!   (`{ expr(v) : v \in S }`). Wave 11 population. Produces a set; the
//!   third operand is the mapped value expression, not a predicate.
//! - [`TlaFingerprint`] — fingerprint of a named state slot. Wave 13
//!   population. Lowers to `verif::VerifStateFingerprint`.
//! - [`TlaInvariant`] — named invariant assertion. Wave 13 population.
//!   Lowers to `verif::VerifInvariantCheck`.
//! - [`TlaState`] — namespace-pin stub for "the current TLA state slab"
//!   as an operand. Still returns `DialectError::NotImplemented` from
//!   `lower()` until state-slot indexing is wired in a follow-up wave.
//!
//! Migration of real TLA+ lowering into these ops is follow-up work under
//! epic #4251.

#[cfg(test)]
use crate::verif::BfsKind;
use crate::verif::{
    VerifBfsStep, VerifBoolAnd, VerifBoolNot, VerifBoolOr, VerifIntAdd, VerifIntDiv, VerifIntEq,
    VerifIntGe, VerifIntGt, VerifIntLe, VerifIntLt, VerifIntMod, VerifIntMul, VerifIntSub,
    VerifScalarInt,
};
use crate::{Dialect, DialectError, DialectOp, Lowered, OpKind};

#[cfg(test)]
use crate::LlvmLeaf;

/// The name of this dialect.
pub const DIALECT_NAME: &str = "tla";

/// The op mnemonics owned by this dialect.
pub const OP_NAMES: &[&str] = &[
    "tla.init",
    "tla.next",
    "tla.action",
    "tla.state",
    "tla.bfs_step",
    "tla.fingerprint",
    "tla.invariant",
    "tla.action_eval",
    "tla.enabled",
    "tla.set_union",
    "tla.set_intersect",
    "tla.set_cardinality",
    "tla.set_member",
    "tla.and",
    "tla.or",
    "tla.not",
    "tla.eq",
    "tla.if_then_else",
    "tla.var_ref",
    "tla.assign",
    "tla.lt",
    "tla.le",
    "tla.gt",
    "tla.ge",
    "tla.add",
    "tla.sub",
    "tla.mul",
    "tla.div",
    "tla.mod",
    "tla.exists",
    "tla.forall",
    "tla.choose",
    "tla.set_builder",
    "tla.set_map",
];

/// Registration struct for the `tla::` dialect.
#[derive(Debug, Default, Clone, Copy)]
pub struct TlaDialect;

impl Dialect for TlaDialect {
    fn name(&self) -> &'static str {
        "tla"
    }
    fn op_names(&self) -> &'static [&'static str] {
        &[
            "tla.init",
            "tla.next",
            "tla.action",
            "tla.state",
            "tla.bfs_step",
            "tla.fingerprint",
            "tla.invariant",
            "tla.action_eval",
            "tla.enabled",
            "tla.set_union",
            "tla.set_intersect",
            "tla.set_cardinality",
            "tla.set_member",
            "tla.and",
            "tla.or",
            "tla.not",
            "tla.eq",
            "tla.if_then_else",
            "tla.var_ref",
            "tla.assign",
            "tla.lt",
            "tla.le",
            "tla.gt",
            "tla.ge",
            "tla.add",
            "tla.sub",
            "tla.mul",
            "tla.div",
            "tla.mod",
            "tla.exists",
            "tla.forall",
            "tla.choose",
            "tla.set_builder",
            "tla.set_map",
        ]
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaInit
// -----------------------------------------------------------------------------

/// The `Init` predicate of a TLA+ spec.
///
/// Lowers to a `verif::VerifBfsStep { kind: Seed, ... }` sequence — one step
/// per initial state variable assignment. In the skeleton we emit exactly one
/// `BfsStep::Seed` per call to keep the test footprint small; real lowering
/// will emit per-assignment steps keyed on an action id.
#[derive(Debug, Clone)]
pub struct TlaInit {
    /// Names of state variables touched by `Init`. Used only for verification
    /// and debug output.
    pub state_vars: Vec<String>,
    /// Synthetic action id used when emitting the seed `VerifBfsStep`.
    pub action_id: u32,
}

impl TlaInit {
    /// Convenience constructor.
    pub fn new(state_vars: Vec<String>, action_id: u32) -> Self {
        Self {
            state_vars,
            action_id,
        }
    }
}

impl DialectOp for TlaInit {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.init"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.state_vars.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.init",
                message: "state_vars must be non-empty".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        // One seed step per Init op in the skeleton. A real impl would emit
        // one per initial-state branch.
        // Wave 14: VerifBfsStep gained worker_id + frontier_size + depth
        // fields. `action_id` is plumbed through (defaults to 0 — seeds have
        // no action dispatch); `worker_id` / `frontier_size` / `depth` are
        // supplied by runtime consumers (see tla-check dialect tracer) and
        // default to 0 at the lowering boundary.
        let _ = self.action_id; // action_id intentionally unused in skeleton (Seed forces 0)
        let step = VerifBfsStep::new_seed(0, 0);
        Ok(Lowered::Ops(vec![Box::new(step) as Box<dyn DialectOp>]))
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaSetRef — a named set-valued expression reference.
// -----------------------------------------------------------------------------

/// Reference to a named set-valued expression, e.g. `S` in `S \union T`.
///
/// This is the minimum operand type required to build a meaningful
/// `TlaSetUnion`. It carries the surface name only — binding resolution and
/// actual set enumeration happen at a lower level. The op is an
/// `OpKind::Expression` with no side effects.
///
/// Verify rejects empty names. Lowering is deferred (`NotImplemented`) until
/// the `tla -> verif` expression path is wired in a follow-up wave.
#[derive(Debug, Clone)]
pub struct TlaSetRef {
    /// Surface name of the set-valued expression. Must be non-empty.
    pub name: String,
}

impl TlaSetRef {
    /// Construct a new set reference.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

impl std::fmt::Display for TlaSetRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}

impl DialectOp for TlaSetRef {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.set_ref"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.name.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.set_ref",
                message: "set reference name must be non-empty".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        // Lowering of expressions into verif:: is a follow-up wave.
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.set_ref",
        })
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaSetUnion — first real op populating the `tla::` dialect.
// -----------------------------------------------------------------------------

/// Binary set union: `left \union right`.
///
/// First real op populating the `tla::` dialect beyond `TlaInit`. Exercises
/// the verify + pretty-print paths on a compound expression. Lowering to
/// `verif::` is intentionally deferred — this wave proves the op-definition
/// pattern scales to real TLA+ semantics; the expression-lowering pipeline
/// arrives in a later wave under epic #4251.
///
/// Corresponds to the tMIR bytecode opcode `SetUnion { rd, r1, r2 }`
/// (see `crates/tla-tir/src/bytecode/opcode.rs`).
///
/// # Verification rules
///
/// - Both operands must live in the `tla::` dialect (no cross-dialect mixing).
/// - Both operands must be [`OpKind::Expression`] — no state transforms,
///   invariant checks, or control flow inside a set-union operand.
/// - Both operands recursively `verify()` themselves.
#[derive(Debug)]
pub struct TlaSetUnion {
    pub left: Box<dyn DialectOp>,
    pub right: Box<dyn DialectOp>,
}

impl TlaSetUnion {
    /// Construct a new set-union op.
    #[must_use]
    pub fn new(left: Box<dyn DialectOp>, right: Box<dyn DialectOp>) -> Self {
        Self { left, right }
    }

    /// Check a single operand for the shared structural rules.
    fn verify_operand(op: &dyn DialectOp, side: &'static str) -> Result<(), DialectError> {
        if op.dialect() != "tla" {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.set_union",
                message: format!(
                    "{side} operand must be in `tla` dialect, got `{}`",
                    op.dialect()
                ),
            });
        }
        if op.kind() != OpKind::Expression {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.set_union",
                message: format!(
                    "{side} operand must be OpKind::Expression, got {:?}",
                    op.kind()
                ),
            });
        }
        op.verify()
    }
}

impl std::fmt::Display for TlaSetUnion {
    /// Render as `(<left-op-name> \union <right-op-name>)`.
    ///
    /// The trait object `dyn DialectOp` doesn't require `Display`, so we
    /// render each operand by its stable `op_name()` token. That is enough
    /// to distinguish compound expressions in debug output and keeps the
    /// printer deterministic. A richer printer that walks structured
    /// operands is a follow-up under epic #4251.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} \\union {})",
            self.left.op_name(),
            self.right.op_name()
        )
    }
}

impl DialectOp for TlaSetUnion {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.set_union"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        Self::verify_operand(self.left.as_ref(), "left")?;
        Self::verify_operand(self.right.as_ref(), "right")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        // Expression lowering to `verif::` is deferred — see module docs
        // and the design doc at designs/2026-04-19-llvm2-dialect-framework.md.
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.set_union",
        })
    }
}

// -----------------------------------------------------------------------------
// Shared operand check for binary set-valued expression ops.
// -----------------------------------------------------------------------------

/// Shared structural check used by `TlaSetIntersect`, `TlaSetCardinality`, and
/// `TlaSetMember` for any operand that is required to be a `tla::`-dialect
/// `OpKind::Expression`. Recurses into the operand's own `verify()`.
///
/// The checker is written to mirror the exact shape of
/// [`TlaSetUnion::verify_operand`] so all populated binary/unary set ops
/// report uniform error messages (`"<side> operand must be in 'tla' dialect,
/// got '<other>'"` etc.). This keeps the op family pattern legible for
/// follow-up ops and for anyone reading a verify failure without guessing
/// which op's rules are in play.
fn verify_set_operand(
    op: &dyn DialectOp,
    side: &'static str,
    parent_op: &'static str,
) -> Result<(), DialectError> {
    if op.dialect() != "tla" {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!(
                "{side} operand must be in `tla` dialect, got `{}`",
                op.dialect()
            ),
        });
    }
    if op.kind() != OpKind::Expression {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!(
                "{side} operand must be OpKind::Expression, got {:?}",
                op.kind()
            ),
        });
    }
    op.verify()
}

// -----------------------------------------------------------------------------
// Concrete: TlaSetIntersect — binary set intersection, mirrors TlaSetUnion.
// -----------------------------------------------------------------------------

/// Binary set intersection: `left \intersect right`.
///
/// Mirror of [`TlaSetUnion`] — same operand discipline, same verify rules,
/// same deferred-lowering contract. Exists to prove the op-definition
/// pattern generalizes beyond a single binary op. Corresponds to the tMIR
/// bytecode opcode `SetIntersect { rd, r1, r2 }`.
///
/// # Verification rules
///
/// - Both operands must live in the `tla::` dialect.
/// - Both operands must be [`OpKind::Expression`].
/// - Both operands recursively `verify()` themselves.
#[derive(Debug)]
pub struct TlaSetIntersect {
    pub left: Box<dyn DialectOp>,
    pub right: Box<dyn DialectOp>,
}

impl TlaSetIntersect {
    /// Construct a new set-intersect op.
    #[must_use]
    pub fn new(left: Box<dyn DialectOp>, right: Box<dyn DialectOp>) -> Self {
        Self { left, right }
    }
}

impl std::fmt::Display for TlaSetIntersect {
    /// Render as `(<left-op-name> \intersect <right-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} \\intersect {})",
            self.left.op_name(),
            self.right.op_name()
        )
    }
}

impl DialectOp for TlaSetIntersect {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.set_intersect"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_set_operand(self.left.as_ref(), "left", "tla.set_intersect")?;
        verify_set_operand(self.right.as_ref(), "right", "tla.set_intersect")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.set_intersect",
        })
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaSetCardinality — unary cardinality of a set-valued expression.
// -----------------------------------------------------------------------------

/// Unary cardinality: `Cardinality(S)`.
///
/// Expression op that takes a set-valued `tla::` expression and yields an
/// integer. Corresponds to the tMIR bytecode opcode `Cardinality { rd, r1 }`.
///
/// # Verification rules
///
/// - Operand must live in the `tla::` dialect.
/// - Operand must be [`OpKind::Expression`].
/// - Operand recursively `verify()`s itself.
#[derive(Debug)]
pub struct TlaSetCardinality {
    pub set: Box<dyn DialectOp>,
}

impl TlaSetCardinality {
    /// Construct a new cardinality op.
    #[must_use]
    pub fn new(set: Box<dyn DialectOp>) -> Self {
        Self { set }
    }
}

impl std::fmt::Display for TlaSetCardinality {
    /// Render as `Cardinality(<set-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cardinality({})", self.set.op_name())
    }
}

impl DialectOp for TlaSetCardinality {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.set_cardinality"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_set_operand(self.set.as_ref(), "set", "tla.set_cardinality")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.set_cardinality",
        })
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaSetMember — binary membership test (value \in set).
// -----------------------------------------------------------------------------

/// Binary set membership: `element \in set`.
///
/// Expression op producing a boolean. Both operands are required to be
/// `tla::`-dialect expressions — the element carries an expression that
/// evaluates to a value, the set carries an expression that evaluates to a
/// set. Corresponds to the tMIR bytecode opcode `In { rd, r1, r2 }`.
///
/// # Verification rules
///
/// - Both operands must live in the `tla::` dialect.
/// - Both operands must be [`OpKind::Expression`].
/// - Both operands recursively `verify()` themselves.
#[derive(Debug)]
pub struct TlaSetMember {
    pub element: Box<dyn DialectOp>,
    pub set: Box<dyn DialectOp>,
}

impl TlaSetMember {
    /// Construct a new set-member op.
    #[must_use]
    pub fn new(element: Box<dyn DialectOp>, set: Box<dyn DialectOp>) -> Self {
        Self { element, set }
    }
}

impl std::fmt::Display for TlaSetMember {
    /// Render as `(<element-op-name> \in <set-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} \\in {})",
            self.element.op_name(),
            self.set.op_name()
        )
    }
}

impl DialectOp for TlaSetMember {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.set_member"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_set_operand(self.element.as_ref(), "element", "tla.set_member")?;
        verify_set_operand(self.set.as_ref(), "set", "tla.set_member")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.set_member",
        })
    }
}

// -----------------------------------------------------------------------------
// Shared operand check for boolean/comparison expression ops (Wave 7).
// -----------------------------------------------------------------------------

/// Structural operand check shared by `TlaAnd`, `TlaOr`, `TlaNot`, and
/// `TlaEq`. Operands must be `tla::`-dialect `OpKind::Expression` and
/// recursively pass their own `verify()`.
///
/// This mirrors [`verify_set_operand`] exactly — the structural rules are the
/// same. A separate function is kept so verify-failure messages name the
/// *parent op* accurately (`"tla.and"` vs `"tla.set_union"`), which is what
/// debugging a compound expression leans on.
///
/// We intentionally do NOT attempt to type-check that a boolean-expecting
/// operand actually produces a boolean, or that the two sides of a `TlaEq`
/// agree on a common value type. Typing of expression results is a follow-up
/// concern that belongs in a typed-IR layer; the structural check here is all
/// the skeleton owes.
fn verify_boolean_operand(
    op: &dyn DialectOp,
    side: &'static str,
    parent_op: &'static str,
) -> Result<(), DialectError> {
    if op.dialect() != "tla" {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!(
                "{side} operand must be in `tla` dialect, got `{}`",
                op.dialect()
            ),
        });
    }
    if op.kind() != OpKind::Expression {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!(
                "{side} operand must be OpKind::Expression, got {:?}",
                op.kind()
            ),
        });
    }
    op.verify()
}

// -----------------------------------------------------------------------------
// Concrete: TlaAnd — binary logical conjunction.
// -----------------------------------------------------------------------------

/// Binary logical conjunction: `left /\ right`.
///
/// Wave 7 population. Variadic `n`-ary `/\` is represented via left-nesting
/// (`TlaAnd(TlaAnd(a, b), c)`) rather than a variable-length operand list —
/// this keeps the op-definition pattern uniform with the Wave 5/6 binary
/// set ops. Corresponds to the tMIR bytecode opcode `And { rd, r1, r2 }`.
///
/// # Verification rules
///
/// - Both operands must live in the `tla::` dialect.
/// - Both operands must be [`OpKind::Expression`].
/// - Both operands recursively `verify()` themselves.
#[derive(Debug)]
pub struct TlaAnd {
    pub left: Box<dyn DialectOp>,
    pub right: Box<dyn DialectOp>,
}

impl TlaAnd {
    /// Construct a new conjunction op.
    #[must_use]
    pub fn new(left: Box<dyn DialectOp>, right: Box<dyn DialectOp>) -> Self {
        Self { left, right }
    }
}

impl std::fmt::Display for TlaAnd {
    /// Render as `(<left-op-name> /\ <right-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} /\\ {})", self.left.op_name(), self.right.op_name())
    }
}

impl DialectOp for TlaAnd {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.and"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_boolean_operand(self.left.as_ref(), "left", "tla.and")?;
        verify_boolean_operand(self.right.as_ref(), "right", "tla.and")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        lower_binary_to_verif_marker(
            "tla.and",
            self.left.as_ref(),
            self.right.as_ref(),
            VerifBoolAnd,
        )
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaOr — binary logical disjunction.
// -----------------------------------------------------------------------------

/// Binary logical disjunction: `left \/ right`.
///
/// Wave 7 population. Mirror of [`TlaAnd`]. Corresponds to the tMIR bytecode
/// opcode `Or { rd, r1, r2 }`.
///
/// # Verification rules
///
/// - Both operands must live in the `tla::` dialect.
/// - Both operands must be [`OpKind::Expression`].
/// - Both operands recursively `verify()` themselves.
#[derive(Debug)]
pub struct TlaOr {
    pub left: Box<dyn DialectOp>,
    pub right: Box<dyn DialectOp>,
}

impl TlaOr {
    /// Construct a new disjunction op.
    #[must_use]
    pub fn new(left: Box<dyn DialectOp>, right: Box<dyn DialectOp>) -> Self {
        Self { left, right }
    }
}

impl std::fmt::Display for TlaOr {
    /// Render as `(<left-op-name> \/ <right-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} \\/ {})", self.left.op_name(), self.right.op_name())
    }
}

impl DialectOp for TlaOr {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.or"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_boolean_operand(self.left.as_ref(), "left", "tla.or")?;
        verify_boolean_operand(self.right.as_ref(), "right", "tla.or")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        lower_binary_to_verif_marker(
            "tla.or",
            self.left.as_ref(),
            self.right.as_ref(),
            VerifBoolOr,
        )
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaNot — unary logical negation.
// -----------------------------------------------------------------------------

/// Unary logical negation: `~expr`.
///
/// Wave 7 population. Single-operand expression op; operand must be a
/// `tla::` expression. Corresponds to the tMIR bytecode opcode
/// `Not { rd, r1 }`. TLA+ also uses the lexeme `\lnot`; the stable
/// pretty-print token is `~` to match the tMIR disassembly convention.
///
/// # Verification rules
///
/// - Operand must live in the `tla::` dialect.
/// - Operand must be [`OpKind::Expression`].
/// - Operand recursively `verify()`s itself.
#[derive(Debug)]
pub struct TlaNot {
    pub operand: Box<dyn DialectOp>,
}

impl TlaNot {
    /// Construct a new negation op.
    #[must_use]
    pub fn new(operand: Box<dyn DialectOp>) -> Self {
        Self { operand }
    }
}

impl std::fmt::Display for TlaNot {
    /// Render as `~<operand-op-name>`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "~{}", self.operand.op_name())
    }
}

impl DialectOp for TlaNot {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.not"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_boolean_operand(self.operand.as_ref(), "operand", "tla.not")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        lower_unary_to_verif_marker("tla.not", self.operand.as_ref(), VerifBoolNot)
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaEq — binary value equality test.
// -----------------------------------------------------------------------------

/// Binary equality test: `lhs = rhs`.
///
/// Wave 7 population. Expression op producing a boolean. Both operands must
/// be `tla::`-dialect expressions, but the *value types* they produce need
/// not agree at this layer — TLA+ equality is total across value kinds, and
/// typed checking is deferred to a later typed-IR layer. Corresponds to the
/// tMIR bytecode opcode `Eq { rd, r1, r2 }`.
///
/// Operand field names are `lhs` / `rhs` rather than `left` / `right` so
/// verify-failure messages can reference operands by semantic role — the
/// sides of an equality test are symmetric, but naming them `lhs`/`rhs`
/// tracks the primed-variable assignment convention (`v' = expr`) that a
/// later `TlaAssign` op will lean on.
///
/// # Verification rules
///
/// - Both operands must live in the `tla::` dialect.
/// - Both operands must be [`OpKind::Expression`].
/// - Both operands recursively `verify()` themselves.
#[derive(Debug)]
pub struct TlaEq {
    pub lhs: Box<dyn DialectOp>,
    pub rhs: Box<dyn DialectOp>,
}

impl TlaEq {
    /// Construct a new equality op.
    #[must_use]
    pub fn new(lhs: Box<dyn DialectOp>, rhs: Box<dyn DialectOp>) -> Self {
        Self { lhs, rhs }
    }
}

impl std::fmt::Display for TlaEq {
    /// Render as `(<lhs-op-name> = <rhs-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} = {})", self.lhs.op_name(), self.rhs.op_name())
    }
}

impl DialectOp for TlaEq {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.eq"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_boolean_operand(self.lhs.as_ref(), "lhs", "tla.eq")?;
        verify_boolean_operand(self.rhs.as_ref(), "rhs", "tla.eq")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        // Reject set-typed operands at lowering time. Without a typed IR, the
        // best structural signal is the operand's op name — `tla.set_*` ops
        // indicate set-valued expressions that have no meaningful
        // `verif.int_eq` lowering in this wave. Bool vs int operands are
        // indistinguishable structurally and both flow through VerifIntEq
        // as a placeholder until the typed-IR layer lands.
        for (side, operand) in [("lhs", self.lhs.as_ref()), ("rhs", self.rhs.as_ref())] {
            let name = operand.op_name();
            if name.starts_with("tla.set_") {
                return Err(DialectError::LoweringFailed {
                    dialect: "tla",
                    op: "tla.eq",
                    message: format!(
                        "{side} operand is set-typed (`{name}`); equality over sets has no `verif::` lowering in this wave"
                    ),
                });
            }
        }
        lower_binary_to_verif_marker("tla.eq", self.lhs.as_ref(), self.rhs.as_ref(), VerifIntEq)
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaIfThenElse — Wave 8 population, ternary conditional expression.
// -----------------------------------------------------------------------------

/// Ternary conditional expression: `IF cond THEN then_value ELSE else_value`.
///
/// Wave 8 population. Three-operand expression op. Corresponds loosely to a
/// tMIR `select`-style sequence (tMIR realizes `IF` as conditional branch +
/// select; the dialect-level op is the unlowered `IF/THEN/ELSE` form, which a
/// later lowering wave will expand).
///
/// # Verification rules
///
/// - All three operands must live in the `tla::` dialect.
/// - All three operands must be [`OpKind::Expression`] — no state transforms,
///   invariants, or control-flow inside a conditional expression. The outer
///   op is an *expression* producing a value from a branch selection.
/// - All three operands recursively `verify()` themselves.
///
/// # Deferred type checking
///
/// TLA+ does not distinguish a boolean "type" at the structural skeleton
/// layer — the framework has no `Ty` type today. The design doc (Wave 7
/// notes) is explicit: type agreement between `then_value` and `else_value`,
/// and the constraint that `cond` evaluates to a boolean, are deferred to a
/// later typed-IR layer. The structural check here enforces the maximum the
/// skeleton can check: dialect + kind + recursive verify. This matches the
/// `TlaEq` convention and keeps the layering honest.
#[derive(Debug)]
pub struct TlaIfThenElse {
    pub cond: Box<dyn DialectOp>,
    pub then_value: Box<dyn DialectOp>,
    pub else_value: Box<dyn DialectOp>,
}

impl TlaIfThenElse {
    /// Construct a new conditional expression.
    #[must_use]
    pub fn new(
        cond: Box<dyn DialectOp>,
        then_value: Box<dyn DialectOp>,
        else_value: Box<dyn DialectOp>,
    ) -> Self {
        Self {
            cond,
            then_value,
            else_value,
        }
    }
}

impl std::fmt::Display for TlaIfThenElse {
    /// Render as `IF <cond-op-name> THEN <then-op-name> ELSE <else-op-name>`.
    ///
    /// Uses stable `op_name()` tokens for operands (matches the rest of the
    /// dialect's deterministic print convention).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "IF {} THEN {} ELSE {}",
            self.cond.op_name(),
            self.then_value.op_name(),
            self.else_value.op_name()
        )
    }
}

impl DialectOp for TlaIfThenElse {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.if_then_else"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_boolean_operand(self.cond.as_ref(), "cond", "tla.if_then_else")?;
        verify_boolean_operand(self.then_value.as_ref(), "then_value", "tla.if_then_else")?;
        verify_boolean_operand(self.else_value.as_ref(), "else_value", "tla.if_then_else")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.if_then_else",
        })
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaVarRef — named state-variable reference, target of TlaAssign.
// -----------------------------------------------------------------------------

/// Reference to a named state variable, e.g. `x` in `x' = e`.
///
/// Wave 8 operand primitive. Parallels [`TlaSetRef`] but is tagged with a
/// distinct `op_name()` so verifies and pretty-printers can distinguish
/// set-valued references from state-variable references. The structural
/// invariant is the same: non-empty surface name.
///
/// The design doc lists this as a prerequisite for `tla.assign` (Wave 7
/// remaining-vocabulary notes: *"Needs a state-variable reference type that
/// is distinct from `TlaSetRef`"*). Keeping them as separate op types — not
/// a shared "named ref" with a tag field — pays for itself in verify-error
/// clarity: `TlaAssign` can assert `target_var_ref.op_name() == "tla.var_ref"`
/// without re-reading a runtime tag.
///
/// Expression kind because the target of an assignment is, structurally, a
/// value reference. The state-transform-ness belongs to the enclosing
/// [`TlaAssign`] op. Lowering to `verif::` is deferred.
#[derive(Debug, Clone)]
pub struct TlaVarRef {
    /// Surface name of the state variable. Must be non-empty.
    pub name: String,
}

impl TlaVarRef {
    /// Construct a new state-variable reference.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

impl std::fmt::Display for TlaVarRef {
    /// Render as the bare surface name (matching `TlaSetRef`'s convention).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}

impl DialectOp for TlaVarRef {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.var_ref"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.name.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.var_ref",
                message: "state variable name must be non-empty".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        // Wave 12 placeholder: state-variable reference lowers to a single
        // `verif.scalar_int(0)` op. This is a structural placeholder — the
        // real lowering needs a state-indexing primitive in `verif::` plus a
        // symbol table to resolve the name, both out of scope for Wave 12.
        // Using a concrete `verif::` op (rather than a leaf) keeps the flat
        // `Lowered::Ops` sequence shape consistent so enclosing binary ops
        // can compose their operand sequences without special-casing.
        Ok(Lowered::Ops(vec![
            Box::new(VerifScalarInt::new(0)) as Box<dyn DialectOp>
        ]))
    }
}

// -----------------------------------------------------------------------------
// Concrete: TlaAssign — Wave 8 population, primed-variable assignment.
// -----------------------------------------------------------------------------

/// Primed-variable assignment: `v' = expr`.
///
/// Wave 8 population. First non-stub [`OpKind::StateTransform`] op in the
/// `tla::` dialect — this is the surface-level statement that drives a
/// state transition in an action body. Statement-level: no return value,
/// consumed for its effect on the next state.
///
/// The target is required to be a [`TlaVarRef`] specifically (not a
/// [`TlaSetRef`] or an arbitrary expression). This is checked structurally
/// via `target_var_ref.op_name() == "tla.var_ref"` — the tightest check the
/// skeleton can enforce without a typed IR. The value side is an expression
/// operand on the usual boolean-operand discipline (dialect + kind + verify).
///
/// Corresponds loosely to a tMIR `StoreState { var, src }`-shaped emission —
/// real lowering will arrive in a follow-up wave alongside `TlaAction` and
/// `TlaNext`.
#[derive(Debug)]
pub struct TlaAssign {
    pub target_var_ref: Box<dyn DialectOp>,
    pub value: Box<dyn DialectOp>,
}

impl TlaAssign {
    /// Construct a new primed-variable assignment.
    #[must_use]
    pub fn new(target_var_ref: Box<dyn DialectOp>, value: Box<dyn DialectOp>) -> Self {
        Self {
            target_var_ref,
            value,
        }
    }
}

impl std::fmt::Display for TlaAssign {
    /// Render as `<target-op-name>' = <value-op-name>`.
    ///
    /// The primed-apostrophe is on the target token to make the intent
    /// obvious in debug output even though the assignment doesn't mutate the
    /// target-op's name.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}' = {}",
            self.target_var_ref.op_name(),
            self.value.op_name()
        )
    }
}

impl DialectOp for TlaAssign {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.assign"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        // The target must specifically be a TlaVarRef — not an arbitrary
        // tla:: expression. Check dialect first so cross-dialect noise is
        // reported with the cross-dialect message, then check op_name.
        if self.target_var_ref.dialect() != "tla" {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.assign",
                message: format!(
                    "target must be in `tla` dialect, got `{}`",
                    self.target_var_ref.dialect()
                ),
            });
        }
        if self.target_var_ref.op_name() != "tla.var_ref" {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.assign",
                message: format!(
                    "target must be `tla.var_ref`, got `{}`",
                    self.target_var_ref.op_name()
                ),
            });
        }
        // Recursively verify the target (catches empty-name TlaVarRef).
        self.target_var_ref.verify()?;
        // Value is a standard boolean-operand (tla-dialect + Expression + verify).
        verify_boolean_operand(self.value.as_ref(), "value", "tla.assign")?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.assign",
        })
    }
}

// -----------------------------------------------------------------------------
// Wave 9: binary integer comparison + arithmetic ops.
// -----------------------------------------------------------------------------

/// Shared structural operand check for Wave 9 comparison/arithmetic ops.
///
/// `TlaLt`, `TlaLe`, `TlaGt`, `TlaGe`, `TlaAdd`, `TlaSub`, `TlaMul`, `TlaDiv`,
/// and `TlaMod` all accept two expression operands with identical structural
/// rules: `tla::` dialect + `OpKind::Expression` + recursive verify. This
/// helper parallels [`verify_set_operand`] and [`verify_boolean_operand`] — a
/// separate function rather than a shared "any expression operand" utility is
/// kept so verify-failure messages can name the parent op accurately (e.g.
/// `"tla.add"` vs `"tla.lt"`).
///
/// Value-type agreement (both operands integer-valued, result boolean for
/// comparisons, integer for arithmetic) is **not** checked here — the
/// framework has no `Ty` today and inventing one is out of scope. That check
/// belongs in a later typed-IR layer; see the design doc's "Remaining
/// vocabulary" / Wave 7 notes.
fn verify_arith_operand(
    op: &dyn DialectOp,
    side: &'static str,
    parent_op: &'static str,
) -> Result<(), DialectError> {
    if op.dialect() != "tla" {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!(
                "{side} operand must be in `tla` dialect, got `{}`",
                op.dialect()
            ),
        });
    }
    if op.kind() != OpKind::Expression {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!(
                "{side} operand must be OpKind::Expression, got {:?}",
                op.kind()
            ),
        });
    }
    op.verify()
}

/// Lower a `tla::` binary expression op to a flat `Lowered::Ops` sequence.
///
/// Wave 12 linear-sequence convention: the output is
/// `[...left_lowered, ...right_lowered, self_verif_marker]`. Operand
/// lowerings must themselves be `Lowered::Ops` — a `Lowered::Leaf` would
/// indicate an operand jumped to the terminal backend without passing
/// through the `verif::` layer, which is a lowering error.
///
/// The `self_verif_marker` is a Wave 12 `verif::` op (e.g. `VerifIntAdd`)
/// whose `kind()` is `Expression` and which has no operand fields — the
/// sequence is the source of truth for operand wiring.
///
/// See [`crate::verif`] module docs for the linear-sequence convention.
fn lower_binary_to_verif_marker<Marker>(
    parent_op: &'static str,
    left: &dyn DialectOp,
    right: &dyn DialectOp,
    marker: Marker,
) -> Result<Lowered, DialectError>
where
    Marker: DialectOp + 'static,
{
    let mut out: Vec<Box<dyn DialectOp>> = Vec::new();
    for (side, operand) in [("left", left), ("right", right)] {
        match operand.lower()? {
            Lowered::Ops(children) => {
                for child in children {
                    if child.dialect() != "verif" {
                        return Err(DialectError::LoweringFailed {
                            dialect: "tla",
                            op: parent_op,
                            message: format!(
                                "{side} operand lowered to non-verif dialect `{}`",
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
                    op: parent_op,
                    message: format!(
                        "{side} operand lowered directly to a terminal leaf; expected a sequence of `verif::` ops"
                    ),
                });
            }
        }
    }
    out.push(Box::new(marker) as Box<dyn DialectOp>);
    Ok(Lowered::Ops(out))
}

/// Lower a `tla::` unary expression op to a flat `Lowered::Ops` sequence.
///
/// Parallels [`lower_binary_to_verif_marker`]. Output shape:
/// `[...operand_lowered, self_verif_marker]`.
fn lower_unary_to_verif_marker<Marker>(
    parent_op: &'static str,
    operand: &dyn DialectOp,
    marker: Marker,
) -> Result<Lowered, DialectError>
where
    Marker: DialectOp + 'static,
{
    let mut out: Vec<Box<dyn DialectOp>> = Vec::new();
    match operand.lower()? {
        Lowered::Ops(children) => {
            for child in children {
                if child.dialect() != "verif" {
                    return Err(DialectError::LoweringFailed {
                        dialect: "tla",
                        op: parent_op,
                        message: format!(
                            "operand lowered to non-verif dialect `{}`",
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
                op: parent_op,
                message: "operand lowered directly to a terminal leaf; expected a sequence of `verif::` ops".into(),
            });
        }
    }
    out.push(Box::new(marker) as Box<dyn DialectOp>);
    Ok(Lowered::Ops(out))
}

/// Generates a Wave 9 binary expression op (comparison or arithmetic).
///
/// All 9 ops share the same shape — two expression operands, the shared
/// `verify_arith_operand` helper — so a macro is the right abstraction here.
/// Per-op docs stay attached to the emitted struct so rustdoc still renders
/// one entry per op. Structurally identical to the Wave 5-8 binary-op
/// pattern, just with a different render symbol.
///
/// Wave 12 wires `lower()` to a `verif::` marker op — the macro takes the
/// target verif op type as the fourth argument.
macro_rules! binary_arith_op {
    (
        $(#[$outer:meta])*
        $name:ident,
        $mnemonic:literal,
        $symbol:literal,
        $verif_marker:ty
    ) => {
        $(#[$outer])*
        #[derive(Debug)]
        pub struct $name {
            pub left: Box<dyn DialectOp>,
            pub right: Box<dyn DialectOp>,
        }

        impl $name {
            /// Construct a new binary arithmetic/comparison op.
            #[must_use]
            pub fn new(left: Box<dyn DialectOp>, right: Box<dyn DialectOp>) -> Self {
                Self { left, right }
            }
        }

        impl std::fmt::Display for $name {
            /// Render as `(<left-op-name> <symbol> <right-op-name>)`, matching
            /// the Wave 5-8 binary-op print convention.
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "({} {} {})",
                    self.left.op_name(),
                    $symbol,
                    self.right.op_name()
                )
            }
        }

        impl DialectOp for $name {
            fn dialect(&self) -> &'static str {
                "tla"
            }
            fn op_name(&self) -> &'static str {
                $mnemonic
            }
            fn kind(&self) -> OpKind {
                OpKind::Expression
            }
            fn verify(&self) -> Result<(), DialectError> {
                verify_arith_operand(self.left.as_ref(), "left", $mnemonic)?;
                verify_arith_operand(self.right.as_ref(), "right", $mnemonic)?;
                Ok(())
            }
            fn lower(&self) -> Result<Lowered, DialectError> {
                self.verify()?;
                lower_binary_to_verif_marker(
                    $mnemonic,
                    self.left.as_ref(),
                    self.right.as_ref(),
                    <$verif_marker>::default(),
                )
            }
        }
    };
}

binary_arith_op!(
    /// Integer less-than comparison: `left < right`.
    ///
    /// Wave 9 population. Expression op producing a boolean from two
    /// integer-valued operands. Corresponds to the tMIR bytecode opcode
    /// `LtInt { rd, r1, r2 }` (see `crates/tla-tir/src/bytecode/opcode.rs`).
    ///
    /// # Verification rules
    ///
    /// - Both operands must live in the `tla::` dialect.
    /// - Both operands must be [`OpKind::Expression`].
    /// - Both operands recursively `verify()` themselves.
    ///
    /// Integer-typing of operands is deferred to the follow-up typed-IR
    /// layer.
    TlaLt,
    "tla.lt",
    "<",
    VerifIntLt
);

binary_arith_op!(
    /// Integer less-or-equal comparison: `left <= right`.
    ///
    /// Wave 9 population. Mirror of [`TlaLt`]. Corresponds to the tMIR
    /// bytecode opcode `LeInt { rd, r1, r2 }`.
    TlaLe,
    "tla.le",
    "<=",
    VerifIntLe
);

binary_arith_op!(
    /// Integer greater-than comparison: `left > right`.
    ///
    /// Wave 9 population. Mirror of [`TlaLt`]. Corresponds to the tMIR
    /// bytecode opcode `GtInt { rd, r1, r2 }`.
    TlaGt,
    "tla.gt",
    ">",
    VerifIntGt
);

binary_arith_op!(
    /// Integer greater-or-equal comparison: `left >= right`.
    ///
    /// Wave 9 population. Mirror of [`TlaLt`]. Corresponds to the tMIR
    /// bytecode opcode `GeInt { rd, r1, r2 }`.
    TlaGe,
    "tla.ge",
    ">=",
    VerifIntGe
);

binary_arith_op!(
    /// Integer addition: `left + right`.
    ///
    /// Wave 9 population. Expression op producing an integer from two
    /// integer-valued operands. Corresponds to the tMIR bytecode opcode
    /// `AddInt { rd, r1, r2 }`.
    TlaAdd,
    "tla.add",
    "+",
    VerifIntAdd
);

binary_arith_op!(
    /// Integer subtraction: `left - right`.
    ///
    /// Wave 9 population. Mirror of [`TlaAdd`]. Corresponds to the tMIR
    /// bytecode opcode `SubInt { rd, r1, r2 }`.
    TlaSub,
    "tla.sub",
    "-",
    VerifIntSub
);

binary_arith_op!(
    /// Integer multiplication: `left * right`.
    ///
    /// Wave 9 population. Mirror of [`TlaAdd`]. Corresponds to the tMIR
    /// bytecode opcode `MulInt { rd, r1, r2 }`.
    TlaMul,
    "tla.mul",
    "*",
    VerifIntMul
);

binary_arith_op!(
    /// Euclidean integer division: `left \div right` (TLC semantics).
    ///
    /// Wave 9 population. Corresponds to the tMIR bytecode opcode
    /// `IntDiv { rd, r1, r2 }`. The pretty-print token is the TLA+ lexeme
    /// `\div` (not `/`) to keep the textual form unambiguous — TLA+ also has
    /// a real-division `/` operator that is a distinct concept and would
    /// arrive as a different dialect op in a later wave if ever needed.
    TlaDiv,
    "tla.div",
    "\\div",
    VerifIntDiv
);

binary_arith_op!(
    /// Euclidean integer modulus: `left % right` (TLC semantics).
    ///
    /// Wave 9 population. Corresponds to the tMIR bytecode opcode
    /// `ModInt { rd, r1, r2 }`. TLA+ surface syntax is `%`; the pretty-print
    /// token matches.
    TlaMod,
    "tla.mod",
    "%",
    VerifIntMod
);

// -----------------------------------------------------------------------------
// Wave 10: compound state-transform ops (`tla.action`, `tla.next`).
// -----------------------------------------------------------------------------

/// A named TLA+ action: `<name>: <body>`.
///
/// Wave 10 population — first compound [`OpKind::StateTransform`] op in the
/// `tla::` dialect. An action body is either (a) a conjunctive tree of
/// primed-variable assignments and guard expressions (a [`TlaAnd`]-rooted
/// expression or a bare [`TlaAssign`]) that drives a single state
/// transition, or (b) a pure guard expression for actions that don't modify
/// state (e.g. a `UNCHANGED <<x,y,z>>`-only action). The `name` field carries
/// the surface action name (e.g. `"Send"`, `"Receive"`) for debug / lowering
/// attribution.
///
/// Corresponds to the TLA+ surface form `Action == body`. Lowering to
/// `verif::` is deferred alongside [`TlaNext`] and the full expression-path
/// lowering wave.
///
/// # Verification rules
///
/// - `name` must be non-empty.
/// - `body` must live in the `tla::` dialect.
/// - `body` kind must be either [`OpKind::StateTransform`] (for action bodies
///   built around `tla.assign`/`tla.and` trees — the common case) or
///   [`OpKind::Expression`] (for guard-only actions). Invariant- and
///   Control-kinded bodies are structurally invalid at this layer.
/// - `body` recursively `verify()`s itself.
///
/// The two accepted kinds are deliberate: a pure `tla.and` of a `tla.assign`
/// and a guard is an `Expression`-kinded tree at the type level (boolean
/// conjunction), while a bare `tla.assign` is a `StateTransform`. Both are
/// structurally valid action bodies, and the verify contract accepts both
/// rather than forcing callers to always wrap state-transform bodies in a
/// single-operand conjunction.
#[derive(Debug)]
pub struct TlaAction {
    /// Surface action name, e.g. `"Send"`. Must be non-empty.
    pub name: String,
    /// Action body — typically a [`TlaAnd`] of [`TlaAssign`] + guard
    /// operands, or a bare [`TlaAssign`], or a guard-only expression.
    pub body: Box<dyn DialectOp>,
}

impl TlaAction {
    /// Construct a new named action.
    #[must_use]
    pub fn new(name: impl Into<String>, body: Box<dyn DialectOp>) -> Self {
        Self {
            name: name.into(),
            body,
        }
    }
}

impl std::fmt::Display for TlaAction {
    /// Render as `<action-name>: <body-op-name>`.
    ///
    /// Uses the body's stable `op_name()` rather than a structural walk to
    /// match the rest of the dialect's deterministic pretty-print
    /// convention.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.body.op_name())
    }
}

impl DialectOp for TlaAction {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.action"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.name.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.action",
                message: "action name must be non-empty".into(),
            });
        }
        if self.body.dialect() != "tla" {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.action",
                message: format!(
                    "body must be in `tla` dialect, got `{}`",
                    self.body.dialect()
                ),
            });
        }
        let body_kind = self.body.kind();
        if body_kind != OpKind::StateTransform && body_kind != OpKind::Expression {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.action",
                message: format!(
                    "body must be OpKind::StateTransform or OpKind::Expression, got {body_kind:?}"
                ),
            });
        }
        self.body.verify()?;
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.action",
        })
    }
}

/// TLA+ next-state relation: disjunction of actions.
///
/// Wave 10 population — represents `Next == A1 \/ A2 \/ ...` as a compound
/// [`OpKind::StateTransform`] op with a vector of child [`TlaAction`] ops.
/// Each child is expected to be a `tla.action`; the verify rules enforce the
/// structural shape (dialect + state-transform kind + recursive verify) but
/// do not gate on `op_name() == "tla.action"` — that would over-constrain
/// follow-up waves that may legally nest a `TlaNext` within a `TlaNext`
/// (e.g. a refinement mapping). The common case is a flat list of
/// [`TlaAction`] children.
///
/// # Verification rules
///
/// - `actions` must be non-empty.
/// - Every element must live in the `tla::` dialect.
/// - Every element's kind must be [`OpKind::StateTransform`].
/// - Every element recursively `verify()`s itself.
#[derive(Debug)]
pub struct TlaNext {
    /// Disjunct actions. Must be non-empty.
    pub actions: Vec<Box<dyn DialectOp>>,
}

impl TlaNext {
    /// Construct a new next-state relation from a vector of action ops.
    #[must_use]
    pub fn new(actions: Vec<Box<dyn DialectOp>>) -> Self {
        Self { actions }
    }
}

impl std::fmt::Display for TlaNext {
    /// Render as `Next(<a1-op-name>, <a2-op-name>, ...)`.
    ///
    /// Renders each child by its stable `op_name()` for the same reason as
    /// the rest of the dialect's pretty-printers — the trait object doesn't
    /// require `Display` and the stable-token form is enough to distinguish
    /// compound structures deterministically.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Next(")?;
        for (i, action) in self.actions.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            f.write_str(action.op_name())?;
        }
        f.write_str(")")
    }
}

impl DialectOp for TlaNext {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.next"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.actions.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.next",
                message: "actions must be non-empty".into(),
            });
        }
        for (i, action) in self.actions.iter().enumerate() {
            if action.dialect() != "tla" {
                return Err(DialectError::VerifyFailed {
                    dialect: "tla",
                    op: "tla.next",
                    message: format!(
                        "action[{i}] must be in `tla` dialect, got `{}`",
                        action.dialect()
                    ),
                });
            }
            if action.kind() != OpKind::StateTransform {
                return Err(DialectError::VerifyFailed {
                    dialect: "tla",
                    op: "tla.next",
                    message: format!(
                        "action[{i}] must be OpKind::StateTransform, got {:?}",
                        action.kind()
                    ),
                });
            }
            action.verify()?;
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.next",
        })
    }
}

// -----------------------------------------------------------------------------
// Wave 11: bounded quantifiers + set-builder comprehensions.
// -----------------------------------------------------------------------------

/// Shared structural check for a three-operand quantifier / set-comprehension
/// op's *variable* position.
///
/// All five Wave 11 ops (`tla.exists`, `tla.forall`, `tla.choose`,
/// `tla.set_builder`, `tla.set_map`) bind a single variable ranging over a
/// domain set, so the variable operand must specifically be a [`TlaVarRef`]
/// rather than an arbitrary expression. This check mirrors the Wave 8
/// `TlaAssign` discipline: dialect + op_name comparison, then recursive
/// verify on the `TlaVarRef` itself (catches empty-name regressions).
///
/// The parent op mnemonic is surfaced in the verify-failure message so a
/// deeply-nested tree still identifies which op's rule failed.
fn verify_quantifier_operand(
    var: &dyn DialectOp,
    domain: &dyn DialectOp,
    body: &dyn DialectOp,
    body_side: &'static str,
    parent_op: &'static str,
) -> Result<(), DialectError> {
    // Variable operand: must be a `tla.var_ref`, checked by dialect + op_name.
    if var.dialect() != "tla" {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!(
                "var operand must be in `tla` dialect, got `{}`",
                var.dialect()
            ),
        });
    }
    if var.op_name() != "tla.var_ref" {
        return Err(DialectError::VerifyFailed {
            dialect: "tla",
            op: parent_op,
            message: format!("var operand must be `tla.var_ref`, got `{}`", var.op_name()),
        });
    }
    var.verify()?;
    // Domain + body/expr operands: standard `verify_arith_operand` discipline
    // (dialect + Expression kind + recursive verify). The domain side is
    // checked before the body side so a malformed domain surfaces first —
    // matches the left-to-right evaluation order TLA+ itself uses.
    verify_arith_operand(domain, "domain", parent_op)?;
    verify_arith_operand(body, body_side, parent_op)?;
    Ok(())
}

/// Bounded existential quantifier: `\E v \in domain : body`.
///
/// Wave 11 population. Expression op producing a boolean. Structurally a
/// three-operand op: a variable binder (must be [`TlaVarRef`]), a domain
/// expression, and a body predicate expression. Corresponds to the tMIR
/// `Exists` / `ExistsSubsetConstrained` opcodes.
///
/// # Verification rules
///
/// - `var` must be a `tla.var_ref` op (checked via `op_name()`), non-empty name.
/// - `domain` must be `tla::`-dialect [`OpKind::Expression`] + recursively verify.
/// - `body` must be `tla::`-dialect [`OpKind::Expression`] + recursively verify.
///
/// # Deferred type checking
///
/// The body should yield a boolean and the domain should yield a set; neither
/// is enforced at this layer (no `Ty` in the skeleton). Typed checking moves
/// to the later typed-IR layer.
#[derive(Debug)]
pub struct TlaExists {
    pub var: Box<dyn DialectOp>,
    pub domain: Box<dyn DialectOp>,
    pub body: Box<dyn DialectOp>,
}

impl TlaExists {
    /// Construct a new bounded existential quantifier.
    #[must_use]
    pub fn new(
        var: Box<dyn DialectOp>,
        domain: Box<dyn DialectOp>,
        body: Box<dyn DialectOp>,
    ) -> Self {
        Self { var, domain, body }
    }
}

impl std::fmt::Display for TlaExists {
    /// Render as `(\E <var-op-name> \in <domain-op-name> : <body-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(\\E {} \\in {} : {})",
            self.var.op_name(),
            self.domain.op_name(),
            self.body.op_name()
        )
    }
}

impl DialectOp for TlaExists {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.exists"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_quantifier_operand(
            self.var.as_ref(),
            self.domain.as_ref(),
            self.body.as_ref(),
            "body",
            "tla.exists",
        )
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.exists",
        })
    }
}

/// Bounded universal quantifier: `\A v \in domain : body`.
///
/// Wave 11 population. Mirror of [`TlaExists`] — same operand discipline,
/// same deferred-lowering contract. Expression op producing a boolean.
#[derive(Debug)]
pub struct TlaForall {
    pub var: Box<dyn DialectOp>,
    pub domain: Box<dyn DialectOp>,
    pub body: Box<dyn DialectOp>,
}

impl TlaForall {
    /// Construct a new bounded universal quantifier.
    #[must_use]
    pub fn new(
        var: Box<dyn DialectOp>,
        domain: Box<dyn DialectOp>,
        body: Box<dyn DialectOp>,
    ) -> Self {
        Self { var, domain, body }
    }
}

impl std::fmt::Display for TlaForall {
    /// Render as `(\A <var-op-name> \in <domain-op-name> : <body-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(\\A {} \\in {} : {})",
            self.var.op_name(),
            self.domain.op_name(),
            self.body.op_name()
        )
    }
}

impl DialectOp for TlaForall {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.forall"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_quantifier_operand(
            self.var.as_ref(),
            self.domain.as_ref(),
            self.body.as_ref(),
            "body",
            "tla.forall",
        )
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.forall",
        })
    }
}

/// Hilbert choice: `CHOOSE v \in domain : body`.
///
/// Wave 11 population. Three-operand expression op, but unlike
/// [`TlaExists`] / [`TlaForall`] this is **value-producing**, not boolean —
/// it returns an element of `domain` satisfying `body`. Corresponds to tMIR
/// `Choose`.
///
/// # Verification rules
///
/// Identical shape to [`TlaExists`] (var must be `tla.var_ref`, domain + body
/// are `tla::`-dialect expressions + recursive verify). Semantic domain /
/// value-type agreement is deferred to the typed-IR layer.
#[derive(Debug)]
pub struct TlaChoose {
    pub var: Box<dyn DialectOp>,
    pub domain: Box<dyn DialectOp>,
    pub body: Box<dyn DialectOp>,
}

impl TlaChoose {
    /// Construct a new CHOOSE op.
    #[must_use]
    pub fn new(
        var: Box<dyn DialectOp>,
        domain: Box<dyn DialectOp>,
        body: Box<dyn DialectOp>,
    ) -> Self {
        Self { var, domain, body }
    }
}

impl std::fmt::Display for TlaChoose {
    /// Render as `(CHOOSE <var-op-name> \in <domain-op-name> : <body-op-name>)`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(CHOOSE {} \\in {} : {})",
            self.var.op_name(),
            self.domain.op_name(),
            self.body.op_name()
        )
    }
}

impl DialectOp for TlaChoose {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.choose"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_quantifier_operand(
            self.var.as_ref(),
            self.domain.as_ref(),
            self.body.as_ref(),
            "body",
            "tla.choose",
        )
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.choose",
        })
    }
}

/// Set-filter comprehension: `{ v \in domain : body }`.
///
/// Wave 11 population. Three-operand expression op producing a set: the
/// subset of `domain` where `body` holds. Corresponds to tMIR `SetOfAll` /
/// `ForSetOf`-style filter emission.
///
/// # Verification rules
///
/// Identical shape to [`TlaExists`] (var must be `tla.var_ref`, domain + body
/// are `tla::`-dialect expressions + recursive verify).
#[derive(Debug)]
pub struct TlaSetBuilder {
    pub var: Box<dyn DialectOp>,
    pub domain: Box<dyn DialectOp>,
    pub body: Box<dyn DialectOp>,
}

impl TlaSetBuilder {
    /// Construct a new set-filter comprehension.
    #[must_use]
    pub fn new(
        var: Box<dyn DialectOp>,
        domain: Box<dyn DialectOp>,
        body: Box<dyn DialectOp>,
    ) -> Self {
        Self { var, domain, body }
    }
}

impl std::fmt::Display for TlaSetBuilder {
    /// Render as `{ <var-op-name> \in <domain-op-name> : <body-op-name> }`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{ {} \\in {} : {} }}",
            self.var.op_name(),
            self.domain.op_name(),
            self.body.op_name()
        )
    }
}

impl DialectOp for TlaSetBuilder {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.set_builder"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_quantifier_operand(
            self.var.as_ref(),
            self.domain.as_ref(),
            self.body.as_ref(),
            "body",
            "tla.set_builder",
        )
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.set_builder",
        })
    }
}

/// Set-map comprehension: `{ expr(v) : v \in domain }`.
///
/// Wave 11 population. Three-operand expression op producing a set: the
/// image of `domain` under the mapping `expr`. Structurally mirrors
/// [`TlaSetBuilder`] — same operand disciplines — but the third operand
/// semantically plays a *map value* role rather than a *predicate* role, so
/// the field name is `expr` (not `body`) and the error-side tag is `"expr"`.
/// Corresponds to tMIR `ForSetOf` / `SetOfAll`.
///
/// # Verification rules
///
/// - `var` must be a `tla.var_ref` op (checked via `op_name()`), non-empty name.
/// - `domain` must be `tla::`-dialect [`OpKind::Expression`] + recursively verify.
/// - `expr` must be `tla::`-dialect [`OpKind::Expression`] + recursively verify.
#[derive(Debug)]
pub struct TlaSetMap {
    pub var: Box<dyn DialectOp>,
    pub domain: Box<dyn DialectOp>,
    pub expr: Box<dyn DialectOp>,
}

impl TlaSetMap {
    /// Construct a new set-map comprehension.
    #[must_use]
    pub fn new(
        var: Box<dyn DialectOp>,
        domain: Box<dyn DialectOp>,
        expr: Box<dyn DialectOp>,
    ) -> Self {
        Self { var, domain, expr }
    }
}

impl std::fmt::Display for TlaSetMap {
    /// Render as `{ <expr-op-name> : <var-op-name> \in <domain-op-name> }`.
    ///
    /// Note the surface-form ordering: TLA+ writes the mapped expression
    /// *before* the variable binder (`{ f(v) : v \in S }`), unlike
    /// `TlaSetBuilder` which writes the binder first (`{ v \in S : P(v) }`).
    /// The pretty-printer matches TLA+ surface syntax.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{ {} : {} \\in {} }}",
            self.expr.op_name(),
            self.var.op_name(),
            self.domain.op_name()
        )
    }
}

impl DialectOp for TlaSetMap {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.set_map"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        verify_quantifier_operand(
            self.var.as_ref(),
            self.domain.as_ref(),
            self.expr.as_ref(),
            "expr",
            "tla.set_map",
        )
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        Err(DialectError::NotImplemented {
            dialect: "tla",
            op: "tla.set_map",
        })
    }
}

// -----------------------------------------------------------------------------
// Stubs — namespace pins
// -----------------------------------------------------------------------------

macro_rules! stub_op {
    ($name:ident, $mnemonic:literal, $kind:expr) => {
        /// Skeleton stub. See module docs.
        #[derive(Debug, Clone, Default)]
        pub struct $name;

        impl DialectOp for $name {
            fn dialect(&self) -> &'static str {
                "tla"
            }
            fn op_name(&self) -> &'static str {
                $mnemonic
            }
            fn kind(&self) -> OpKind {
                $kind
            }
            fn verify(&self) -> Result<(), DialectError> {
                Ok(())
            }
            fn lower(&self) -> Result<Lowered, DialectError> {
                Err(DialectError::NotImplemented {
                    dialect: "tla",
                    op: $mnemonic,
                })
            }
        }
    };
}

// `TlaState` is the only remaining namespace-pin stub — it represents "the
// current TLA state slab" as an operand to lower-level ops, and the correct
// lowering shape depends on caller context (which slot, which action step).
// Leaving it NotImplemented until a follow-up wave wires state-indexing.
stub_op!(TlaState, "tla.state", OpKind::Expression);

// -----------------------------------------------------------------------------
// Wave 13: TlaFingerprint + TlaInvariant — lower to verif primitives.
//
// Wave 14 TL3e (#4286): graduated both ops to carry the full structured
// field set their `verif::` counterparts hold. TlaFingerprint gained `depth`;
// TlaInvariant gained `state_slot` + `depth`. Both lower through the
// depth-aware `verif::Verif*::new_at_depth` constructors so the BFS level
// attribution reaches the terminal `LlvmLeaf` variant.
// -----------------------------------------------------------------------------

/// Compute a fingerprint of a named state slot at a BFS depth. Surface-level
/// analogue of [`crate::verif::VerifStateFingerprint`]; lowers to a single
/// `verif.state_fingerprint` op that carries both fields through to the
/// terminal [`crate::LlvmLeaf::StateFingerprint`].
///
/// # Fields
///
/// - `state_slot`: slot index of the state slab to fingerprint. `0` = the
///   canonical "current state" slot in the skeleton.
/// - `depth`: BFS depth (TLC level) at which the fingerprint was observed.
///   `0` = the Init-produced seed level. Carrying depth at the surface op
///   lets callers (e.g. the `tla-check` dialect tracer) attribute a
///   fingerprint to its BFS level without a side-channel lookup.
///
/// # Verification rules
///
/// Both fields are `u32` so non-negativity is type-enforced. No other
/// structural invariants today — every `(state_slot, depth)` combination is
/// well-formed.
///
/// # Graduation history (#4286)
///
/// - **Wave 13**: stub — only `state_slot`; lowered to
///   `VerifStateFingerprint::new(state_slot)` (depth defaulted to 0 in the
///   verif op). The `depth` concept was not threaded through at all.
/// - **Wave 14 TL3e**: added `depth`; added
///   [`TlaFingerprint::new_at_depth`] constructor; lowered through
///   `VerifStateFingerprint::new_at_depth` so the BFS level reaches the
///   terminal leaf.
#[derive(Debug, Clone, Copy, Default)]
pub struct TlaFingerprint {
    /// Slot index of the state slab to fingerprint. Defaults to 0 (the
    /// canonical "current state" slot in the skeleton).
    pub state_slot: u32,
    /// BFS depth (TLC level) at which the fingerprint was observed. `0` =
    /// the Init-produced seed level.
    pub depth: u32,
}

impl TlaFingerprint {
    /// Construct a new fingerprint op targeting the given state slot at BFS
    /// depth `0` (the Init level). Equivalent to
    /// [`TlaFingerprint::new_at_depth`] with `depth = 0`.
    #[must_use]
    pub fn new(state_slot: u32) -> Self {
        Self {
            state_slot,
            depth: 0,
        }
    }

    /// Construct a new fingerprint op with every field explicit. Both fields
    /// accept any `u32`.
    #[must_use]
    pub fn new_at_depth(state_slot: u32, depth: u32) -> Self {
        Self { state_slot, depth }
    }
}

impl DialectOp for TlaFingerprint {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.fingerprint"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        // state_slot and depth are u32, so non-negativity is type-enforced.
        // Mirrors the verif-level rule (no other structural invariants today).
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        let verif_op =
            crate::verif::VerifStateFingerprint::new_at_depth(self.state_slot, self.depth);
        Ok(Lowered::Ops(vec![Box::new(verif_op) as Box<dyn DialectOp>]))
    }
}

/// Assert a named invariant holds against a state slot at a BFS depth. Target
/// of TLA+ `INVARIANT SafetyP` declarations. Surface-level analogue of
/// [`crate::verif::VerifInvariantCheck`]; lowers to a single
/// `verif.invariant_check` op that carries every field through to the
/// terminal [`crate::LlvmLeaf::InvariantCheck`].
///
/// The `name` is descriptive only and used in verify diagnostics;
/// `invariant_id` is the stable numeric key the backend resolves to a
/// compiled predicate.
///
/// # Fields
///
/// - `name`: surface name of the invariant (for diagnostics). Must be
///   non-empty.
/// - `invariant_id`: stable id of the invariant (lowered through to verif).
/// - `state_slot`: slot index of the state slab to check against the
///   invariant. `0` = the canonical "current state" slot in the skeleton.
/// - `depth`: BFS depth (TLC level) at which the check was run. `0` =
///   Init-produced seed level. Carrying depth at the surface op lets callers
///   attribute a violation to its BFS level without a side-channel lookup.
///
/// # Verification rules
///
/// - `name` must be non-empty.
/// - `invariant_id`, `state_slot`, and `depth` are `u32` — non-negativity is
///   type-enforced.
///
/// # Graduation history (#4286)
///
/// - **Wave 13**: stub — only `name` + `invariant_id`; lowered to
///   `VerifInvariantCheck::new(invariant_id)` (state_slot + depth defaulted
///   to 0 in the verif op). Neither field was reachable from the surface
///   op.
/// - **Wave 14 TL3e**: added `state_slot` + `depth`; added
///   [`TlaInvariant::new_on_state`] and [`TlaInvariant::new_at_depth`]
///   constructors; lowered through `VerifInvariantCheck::new_at_depth` so
///   every field reaches the terminal leaf.
#[derive(Debug, Clone)]
pub struct TlaInvariant {
    /// Surface name of the invariant (for diagnostics). Must be non-empty.
    pub name: String,
    /// Stable id of the invariant (lowered through to verif).
    pub invariant_id: u32,
    /// Slot index of the state slab to check against the invariant.
    pub state_slot: u32,
    /// BFS depth (TLC level) at which the check was run.
    pub depth: u32,
}

impl TlaInvariant {
    /// Construct a new invariant op at state slot `0` and BFS depth `0`
    /// (the Init level). Equivalent to [`TlaInvariant::new_at_depth`] with
    /// `state_slot = 0` and `depth = 0`.
    #[must_use]
    pub fn new(name: impl Into<String>, invariant_id: u32) -> Self {
        Self {
            name: name.into(),
            invariant_id,
            state_slot: 0,
            depth: 0,
        }
    }

    /// Construct a new invariant op against a specific state slot at BFS
    /// depth `0`. Equivalent to [`TlaInvariant::new_at_depth`] with
    /// `depth = 0`.
    #[must_use]
    pub fn new_on_state(name: impl Into<String>, invariant_id: u32, state_slot: u32) -> Self {
        Self {
            name: name.into(),
            invariant_id,
            state_slot,
            depth: 0,
        }
    }

    /// Construct a new invariant op with every field explicit. The numeric
    /// fields accept any `u32`; `name` must be non-empty.
    #[must_use]
    pub fn new_at_depth(
        name: impl Into<String>,
        invariant_id: u32,
        state_slot: u32,
        depth: u32,
    ) -> Self {
        Self {
            name: name.into(),
            invariant_id,
            state_slot,
            depth,
        }
    }
}

impl Default for TlaInvariant {
    fn default() -> Self {
        // Default value kept only to match the previous unit-struct surface.
        // Real callers should use `TlaInvariant::new` (or the depth-aware
        // constructors).
        Self {
            name: "__unnamed__".into(),
            invariant_id: 0,
            state_slot: 0,
            depth: 0,
        }
    }
}

impl DialectOp for TlaInvariant {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.invariant"
    }
    fn kind(&self) -> OpKind {
        OpKind::Invariant
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.name.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.invariant",
                message: "invariant name must be non-empty".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        let verif_op = crate::verif::VerifInvariantCheck::new_at_depth(
            self.invariant_id,
            self.state_slot,
            self.depth,
        );
        Ok(Lowered::Ops(vec![Box::new(verif_op) as Box<dyn DialectOp>]))
    }
}

// -----------------------------------------------------------------------------
// Wave 14: TlaBfsStep — surface-level BFS step op, lowers to verif.bfs_step.
// -----------------------------------------------------------------------------

/// A BFS step at the `tla::` level — the surface-syntax analogue of
/// [`crate::verif::VerifBfsStep`]. Consumers that want to emit a BFS step
/// without directly reaching into the `verif::` dialect use this op; it
/// lowers to a single `verif.bfs_step` via [`crate::TlaToVerifPass`].
///
/// `TlaInit` lowers to a **seed** `verif.bfs_step`. `TlaBfsStep` is the
/// expand-side sibling, produced once per frontier dequeue at the runtime
/// consumer layer (see the `tla-check` dialect tracer).
///
/// # Fields
///
/// Mirrors [`crate::verif::VerifBfsStep`] 1:1 to keep the tla → verif lowering
/// trivial. `action_id` and `depth` are runtime-resolved by the consumer;
/// `worker_id` and `frontier_size` are hint fields that backend schedulers
/// may use for load balancing.
///
/// # Verification rules
///
/// The tla-level verify is minimal — `action_id > 0` is enforced (an expand
/// step must name a real action). Structural checks on `(worker_id, depth)`
/// are delegated to the lowered `verif.bfs_step` op.
#[derive(Debug, Clone, Copy)]
pub struct TlaBfsStep {
    /// Stable id of the action that produced this step.
    pub action_id: u32,
    /// Worker lane id (0 for single-threaded; parallel BFS worker index).
    pub worker_id: u32,
    /// Frontier size at emission time (`0` = unknown).
    pub frontier_size: u32,
    /// BFS depth (TLC level) of the state being processed.
    pub depth: u32,
}

impl TlaBfsStep {
    /// Construct a new BFS step op.
    #[must_use]
    pub fn new(action_id: u32, worker_id: u32, frontier_size: u32, depth: u32) -> Self {
        Self {
            action_id,
            worker_id,
            frontier_size,
            depth,
        }
    }
}

impl DialectOp for TlaBfsStep {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.bfs_step"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.action_id == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.bfs_step",
                message: "action_id must be > 0 (0 is reserved for the seed step)".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        let verif_op = crate::verif::VerifBfsStep::new_expand(
            self.action_id,
            self.worker_id,
            self.frontier_size,
            self.depth,
        );
        Ok(Lowered::Ops(vec![Box::new(verif_op) as Box<dyn DialectOp>]))
    }
}

// -----------------------------------------------------------------------------
// Wave 14 TL3f (#4286): TlaActionEval — surface op for per-action successor
// expansion. Lowers to verif.action_eval.
// -----------------------------------------------------------------------------

/// Evaluate a named TLA+ action against a source state. Surface-syntax
/// analogue of [`crate::verif::VerifActionEval`]; lowers to a single
/// `verif.action_eval` op that carries every field through to the terminal
/// [`crate::LlvmLeaf::ActionEval`].
///
/// The `name` is descriptive only and used in verify diagnostics;
/// `action_id` is the stable numeric key the backend resolves to a compiled
/// action evaluator (TIR / bytecode / JIT).
///
/// # Fields
///
/// - `name`: surface name of the action (for diagnostics). Must be non-empty.
/// - `action_id`: stable id of the action (lowered through to verif). Must
///   be `>= 1` — `0` is reserved for Init (use [`TlaInit`] for seed-level
///   evaluation).
/// - `source_slot`: slot index of the source state slab that drives the
///   evaluator. `0` = the canonical "current state" slot in the skeleton.
/// - `depth`: BFS depth (TLC level) at which the evaluator ran. `0` =
///   Init-produced seed level.
/// - `worker_id`: zero-based BFS worker lane. Single-threaded BFS uses `0`.
///
/// # Verification rules
///
/// - `name` must be non-empty.
/// - `action_id` must be `>= 1`.
///
/// # Graduation history (#4286)
///
/// - **Wave 14 TL3f**: new op — introduced as a graduated surface op, not
///   as a stub-then-graduated pair. Lowered through
///   `VerifActionEval::new_at_depth` so every field reaches the terminal
///   leaf.
#[derive(Debug, Clone)]
pub struct TlaActionEval {
    /// Surface name of the action (for diagnostics). Must be non-empty.
    pub name: String,
    /// Stable id of the action (`>= 1`; `0` reserved for Init).
    pub action_id: u32,
    /// Slot index of the source state driving evaluation.
    pub source_slot: u32,
    /// BFS depth (TLC level) at which the evaluator ran.
    pub depth: u32,
    /// Zero-based BFS worker lane id.
    pub worker_id: u32,
}

impl TlaActionEval {
    /// Construct a new action-eval op on source slot `0` at BFS depth `0`
    /// and worker lane `0`. Equivalent to [`TlaActionEval::new_at_depth`]
    /// with the latter three fields all `0`.
    #[must_use]
    pub fn new(name: impl Into<String>, action_id: u32) -> Self {
        Self {
            name: name.into(),
            action_id,
            source_slot: 0,
            depth: 0,
            worker_id: 0,
        }
    }

    /// Construct a new action-eval op against a specific source slot at
    /// BFS depth `0` and worker lane `0`.
    #[must_use]
    pub fn new_on_source(name: impl Into<String>, action_id: u32, source_slot: u32) -> Self {
        Self {
            name: name.into(),
            action_id,
            source_slot,
            depth: 0,
            worker_id: 0,
        }
    }

    /// Construct a new action-eval op with every field explicit. `name`
    /// must be non-empty; `action_id` must be `>= 1`; the other fields
    /// accept any `u32`.
    #[must_use]
    pub fn new_at_depth(
        name: impl Into<String>,
        action_id: u32,
        source_slot: u32,
        depth: u32,
        worker_id: u32,
    ) -> Self {
        Self {
            name: name.into(),
            action_id,
            source_slot,
            depth,
            worker_id,
        }
    }
}

impl DialectOp for TlaActionEval {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.action_eval"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.name.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.action_eval",
                message: "action name must be non-empty".into(),
            });
        }
        if self.action_id == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.action_eval",
                message: "action_id must be >= 1; 0 is reserved for Init (use tla.init)".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        let verif_op = crate::verif::VerifActionEval::new_at_depth(
            self.action_id,
            self.source_slot,
            self.depth,
            self.worker_id,
        );
        Ok(Lowered::Ops(vec![Box::new(verif_op) as Box<dyn DialectOp>]))
    }
}

// -----------------------------------------------------------------------------
// Wave 14 TL3f (#4286): TlaEnabled — surface op for TLA+ `ENABLED A`.
// Lowers to verif.enabled_check.
// -----------------------------------------------------------------------------

/// The TLA+ `ENABLED A` predicate — true iff action `A` has at least one
/// successor from the given state. Surface-syntax analogue of
/// [`crate::verif::VerifEnabledCheck`]; lowers to a single
/// `verif.enabled_check` op that carries every field through to the
/// terminal [`crate::LlvmLeaf::EnabledCheck`].
///
/// # Fields
///
/// - `name`: surface name of the action (for diagnostics). Must be
///   non-empty.
/// - `action_id`: stable id of the action whose enabledness is being
///   queried. Must be `>= 1` — `ENABLED Init` is nonsensical.
/// - `state_slot`: slot index of the state slab to check against. `0` =
///   the canonical "current state" slot in the skeleton.
/// - `depth`: BFS depth (TLC level) at which the check was run. `0` =
///   Init-produced seed level.
///
/// # Verification rules
///
/// - `name` must be non-empty.
/// - `action_id` must be `>= 1`.
///
/// # Graduation history (#4286)
///
/// - **Wave 14 TL3f**: new op — introduced as a graduated surface op, not
///   as a stub-then-graduated pair. Lowered through
///   `VerifEnabledCheck::new_at_depth` so every field reaches the
///   terminal leaf.
#[derive(Debug, Clone)]
pub struct TlaEnabled {
    /// Surface name of the action whose enabledness is queried. Must be
    /// non-empty.
    pub name: String,
    /// Stable id of the action (`>= 1`; 0 forbidden — ENABLED Init is
    /// nonsensical).
    pub action_id: u32,
    /// Slot index of the state slab to check against.
    pub state_slot: u32,
    /// BFS depth (TLC level) at which the check was run.
    pub depth: u32,
}

impl TlaEnabled {
    /// Construct a new enabled-check op on state slot `0` at BFS depth `0`.
    /// Equivalent to [`TlaEnabled::new_at_depth`] with `state_slot = 0`
    /// and `depth = 0`.
    #[must_use]
    pub fn new(name: impl Into<String>, action_id: u32) -> Self {
        Self {
            name: name.into(),
            action_id,
            state_slot: 0,
            depth: 0,
        }
    }

    /// Construct a new enabled-check op against a specific state slot at
    /// BFS depth `0`. Equivalent to [`TlaEnabled::new_at_depth`] with
    /// `depth = 0`.
    #[must_use]
    pub fn new_on_state(name: impl Into<String>, action_id: u32, state_slot: u32) -> Self {
        Self {
            name: name.into(),
            action_id,
            state_slot,
            depth: 0,
        }
    }

    /// Construct a new enabled-check op with every field explicit. `name`
    /// must be non-empty; `action_id` must be `>= 1`; `state_slot` and
    /// `depth` accept any `u32`.
    #[must_use]
    pub fn new_at_depth(
        name: impl Into<String>,
        action_id: u32,
        state_slot: u32,
        depth: u32,
    ) -> Self {
        Self {
            name: name.into(),
            action_id,
            state_slot,
            depth,
        }
    }
}

impl DialectOp for TlaEnabled {
    fn dialect(&self) -> &'static str {
        "tla"
    }
    fn op_name(&self) -> &'static str {
        "tla.enabled"
    }
    fn kind(&self) -> OpKind {
        // ENABLED is a pure predicate — it produces a Bool value. Kind mirrors
        // verif.enabled_check.
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.name.is_empty() {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.enabled",
                message: "action name must be non-empty".into(),
            });
        }
        if self.action_id == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.enabled",
                message: "action_id must be >= 1; ENABLED Init is nonsensical".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        let verif_op = crate::verif::VerifEnabledCheck::new_at_depth(
            self.action_id,
            self.state_slot,
            self.depth,
        );
        Ok(Lowered::Ops(vec![Box::new(verif_op) as Box<dyn DialectOp>]))
    }
}

// -----------------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tla_dialect_registration_exposes_op_names() {
        let d = TlaDialect;
        assert_eq!(d.name(), "tla");
        assert!(d.op_names().contains(&"tla.init"));
        assert!(d.op_names().contains(&"tla.invariant"));
    }

    #[test]
    fn tla_init_verify_rejects_empty_state_vars() {
        let init = TlaInit::new(vec![], 0);
        let err = init.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.init");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_init_verify_accepts_nonempty_state_vars() {
        let init = TlaInit::new(vec!["x".into(), "y".into()], 0);
        init.verify().unwrap();
    }

    #[test]
    fn tla_init_lowers_to_verif_bfs_seed() {
        let init = TlaInit::new(vec!["x".into()], 42);
        let lowered = init.lower().unwrap();
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].dialect(), "verif");
                assert_eq!(ops[0].op_name(), "verif.bfs_step");
            }
            Lowered::Leaf(_) => panic!("TlaInit should not return Leaf"),
        }
    }

    #[test]
    fn tla_init_lower_propagates_verify_failure() {
        let init = TlaInit::new(vec![], 0);
        let err = init.lower().unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn tla_init_op_metadata() {
        let init = TlaInit::new(vec!["x".into()], 0);
        assert_eq!(init.dialect(), "tla");
        assert_eq!(init.op_name(), "tla.init");
        assert_eq!(init.kind(), OpKind::StateTransform);
    }

    #[test]
    fn stubs_return_not_implemented_on_lower() {
        // `TlaNext` and `TlaAction` graduated from stubs to compound ops in
        // Wave 10. `TlaFingerprint` and `TlaInvariant` graduated in Wave 13
        // (they now lower to `verif::VerifStateFingerprint` and
        // `verif::VerifInvariantCheck` respectively). The only remaining
        // namespace-pin stub is `TlaState` — it still returns NotImplemented
        // from `lower()` until state-slot indexing is wired in a follow-up
        // wave.
        let ops: Vec<Box<dyn DialectOp>> = vec![Box::new(TlaState)];
        for op in ops {
            let err = op.lower().unwrap_err();
            assert!(
                matches!(err, DialectError::NotImplemented { dialect: "tla", .. }),
                "expected NotImplemented for {}, got {err:?}",
                op.op_name()
            );
        }
    }

    // -------------------------------------------------------------------------
    // Wave 13 tests — TlaFingerprint + TlaInvariant lower to verif primitives.
    // -------------------------------------------------------------------------

    #[test]
    fn wave13_tla_fingerprint_reports_dialect_and_mnemonic() {
        let op = TlaFingerprint::new(5);
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.fingerprint");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.state_slot, 5);
    }

    #[test]
    fn wave13_tla_fingerprint_lowers_to_verif_state_fingerprint() {
        let op = TlaFingerprint::new(3);
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].dialect(), "verif");
                assert_eq!(ops[0].op_name(), "verif.state_fingerprint");
            }
            Lowered::Leaf(_) => panic!("expected verif ops, got leaf"),
        }
    }

    #[test]
    fn wave13_tla_invariant_reports_dialect_and_mnemonic() {
        let op = TlaInvariant::new("TypeOK", 1);
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.invariant");
        assert_eq!(op.kind(), OpKind::Invariant);
        assert_eq!(op.name, "TypeOK");
        assert_eq!(op.invariant_id, 1);
    }

    #[test]
    fn wave13_tla_invariant_verify_rejects_empty_name() {
        let op = TlaInvariant::new("", 0);
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.invariant");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave13_tla_invariant_lower_propagates_verify_failure() {
        let op = TlaInvariant::new("", 0);
        let err = op.lower().unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave13_tla_invariant_lowers_to_verif_invariant_check() {
        let op = TlaInvariant::new("SafetyP", 7);
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].dialect(), "verif");
                assert_eq!(ops[0].op_name(), "verif.invariant_check");
            }
            Lowered::Leaf(_) => panic!("expected verif ops, got leaf"),
        }
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3e tests (#4286) — TlaFingerprint + TlaInvariant graduation:
    // depth + state_slot fields thread through the lowering to the terminal
    // LlvmLeaf so BFS-level attribution survives the full tla -> verif -> llvm
    // pipeline.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3e_tla_fingerprint_default_depth_is_zero() {
        // Backcompat: `TlaFingerprint::new(slot)` carries `depth = 0`.
        let op = TlaFingerprint::new(9);
        assert_eq!(op.state_slot, 9);
        assert_eq!(op.depth, 0);
    }

    #[test]
    fn wave14_tl3e_tla_fingerprint_new_at_depth_sets_both_fields() {
        // Graduated constructor: `new_at_depth(slot, depth)` fills both
        // fields; every `(u32, u32)` combination is well-formed.
        let op = TlaFingerprint::new_at_depth(5, 17);
        assert_eq!(op.state_slot, 5);
        assert_eq!(op.depth, 17);
    }

    #[test]
    fn wave14_tl3e_tla_fingerprint_lowering_threads_depth_to_leaf() {
        // Lowering: tla.fingerprint at depth 23 -> verif.state_fingerprint
        // at depth 23 -> LlvmLeaf::StateFingerprint { depth: 23, ... }.
        // Proves the depth field reaches the terminal leaf through the
        // full two-step lowering path.
        use crate::verif::VerifStateFingerprint;

        let tla_op = TlaFingerprint::new_at_depth(4, 23);
        let lowered = tla_op.lower().unwrap();
        let verif_op = match lowered {
            Lowered::Ops(mut ops) => {
                assert_eq!(ops.len(), 1);
                ops.pop().unwrap()
            }
            Lowered::Leaf(_) => panic!("expected verif ops, got leaf"),
        };
        // Lower the verif op to its LlvmLeaf and assert depth is preserved.
        match verif_op.lower().unwrap() {
            Lowered::Leaf(crate::LlvmLeaf::StateFingerprint { state_slot, depth }) => {
                assert_eq!(state_slot, 4);
                assert_eq!(depth, 23);
            }
            other => panic!("expected StateFingerprint leaf, got {other:?}"),
        }
        // Sanity: the verif-level op reports the same depth, confirming the
        // tla surface op constructed the depth-aware verif constructor.
        let direct = VerifStateFingerprint::new_at_depth(4, 23);
        assert_eq!(direct.state_slot, 4);
        assert_eq!(direct.depth, 23);
    }

    #[test]
    fn wave14_tl3e_tla_invariant_default_state_slot_and_depth_are_zero() {
        // Backcompat: `TlaInvariant::new(name, id)` carries `state_slot = 0`
        // and `depth = 0`.
        let op = TlaInvariant::new("TypeOK", 11);
        assert_eq!(op.name, "TypeOK");
        assert_eq!(op.invariant_id, 11);
        assert_eq!(op.state_slot, 0);
        assert_eq!(op.depth, 0);
    }

    #[test]
    fn wave14_tl3e_tla_invariant_new_on_state_sets_state_slot() {
        // `new_on_state(name, id, slot)` fills state_slot and leaves
        // depth at its default (0).
        let op = TlaInvariant::new_on_state("Safety", 3, 42);
        assert_eq!(op.name, "Safety");
        assert_eq!(op.invariant_id, 3);
        assert_eq!(op.state_slot, 42);
        assert_eq!(op.depth, 0);
    }

    #[test]
    fn wave14_tl3e_tla_invariant_new_at_depth_sets_all_fields() {
        // Fully-explicit constructor: `new_at_depth(name, id, slot, depth)`.
        let op = TlaInvariant::new_at_depth("SafetyP", 9, 13, 25);
        assert_eq!(op.name, "SafetyP");
        assert_eq!(op.invariant_id, 9);
        assert_eq!(op.state_slot, 13);
        assert_eq!(op.depth, 25);
    }

    #[test]
    fn wave14_tl3e_tla_invariant_lowering_threads_fields_to_leaf() {
        // Lowering: tla.invariant(id=7, slot=13, depth=25) ->
        // verif.invariant_check(id=7, slot=13, depth=25) ->
        // LlvmLeaf::InvariantCheck { invariant_id: 7, state_slot: 13,
        // depth: 25 }. Proves all three numeric fields survive the full
        // two-step lowering path (graduation contract).
        let tla_op = TlaInvariant::new_at_depth("SafetyP", 7, 13, 25);
        let lowered = tla_op.lower().unwrap();
        let verif_op = match lowered {
            Lowered::Ops(mut ops) => {
                assert_eq!(ops.len(), 1);
                ops.pop().unwrap()
            }
            Lowered::Leaf(_) => panic!("expected verif ops, got leaf"),
        };
        match verif_op.lower().unwrap() {
            Lowered::Leaf(crate::LlvmLeaf::InvariantCheck {
                invariant_id,
                state_slot,
                depth,
            }) => {
                assert_eq!(invariant_id, 7);
                assert_eq!(state_slot, 13);
                assert_eq!(depth, 25);
            }
            other => panic!("expected InvariantCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn op_names_constant_is_exported() {
        // OP_NAMES and DIALECT_NAME are part of the crate's public API; keep
        // a reachability test so refactors don't silently drop them.
        // Wave 14: +1 for tla.bfs_step — surface-level BFS step op.
        // Wave 14 TL3f: +2 (tla.action_eval, tla.enabled) = 34.
        assert_eq!(OP_NAMES.len(), 34);
        assert!(OP_NAMES.contains(&"tla.bfs_step"));
        assert!(OP_NAMES.contains(&"tla.action_eval"));
        assert!(OP_NAMES.contains(&"tla.enabled"));
        assert!(OP_NAMES.contains(&"tla.set_union"));
        assert!(OP_NAMES.contains(&"tla.set_intersect"));
        assert!(OP_NAMES.contains(&"tla.set_cardinality"));
        assert!(OP_NAMES.contains(&"tla.set_member"));
        assert!(OP_NAMES.contains(&"tla.and"));
        assert!(OP_NAMES.contains(&"tla.or"));
        assert!(OP_NAMES.contains(&"tla.not"));
        assert!(OP_NAMES.contains(&"tla.eq"));
        assert!(OP_NAMES.contains(&"tla.if_then_else"));
        assert!(OP_NAMES.contains(&"tla.var_ref"));
        assert!(OP_NAMES.contains(&"tla.assign"));
        // Wave 9 — comparison + arithmetic.
        assert!(OP_NAMES.contains(&"tla.lt"));
        assert!(OP_NAMES.contains(&"tla.le"));
        assert!(OP_NAMES.contains(&"tla.gt"));
        assert!(OP_NAMES.contains(&"tla.ge"));
        assert!(OP_NAMES.contains(&"tla.add"));
        assert!(OP_NAMES.contains(&"tla.sub"));
        assert!(OP_NAMES.contains(&"tla.mul"));
        assert!(OP_NAMES.contains(&"tla.div"));
        assert!(OP_NAMES.contains(&"tla.mod"));
        // Wave 11 — quantifiers + set comprehensions.
        assert!(OP_NAMES.contains(&"tla.exists"));
        assert!(OP_NAMES.contains(&"tla.forall"));
        assert!(OP_NAMES.contains(&"tla.choose"));
        assert!(OP_NAMES.contains(&"tla.set_builder"));
        assert!(OP_NAMES.contains(&"tla.set_map"));
        assert!(!DIALECT_NAME.is_empty());
    }

    #[test]
    fn leaf_tag_for_bfs_is_stable() {
        // Wave 14 TL3h: all Wave 12 expression ops (int_add, int_sub, …,
        // bool_not) graduated to structured `LlvmLeaf` unit variants. The
        // `Todo` variant is kept as an escape hatch for future
        // placeholder-only ops; this equality probe exercises it with a
        // sentinel string so the `Todo` shape stays stable as a test
        // fixture without relying on any currently-lowered op.
        let leaf = LlvmLeaf::Todo("placeholder_sentinel");
        assert_eq!(leaf, LlvmLeaf::Todo("placeholder_sentinel"));
    }

    // -------------------------------------------------------------------------
    // Wave 14 tests — TlaBfsStep surface op + verif.bfs_step lowering.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tla_bfs_step_reports_dialect_and_mnemonic() {
        let op = TlaBfsStep::new(7, 2, 128, 3);
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.bfs_step");
        assert_eq!(op.kind(), OpKind::StateTransform);
        assert_eq!(op.action_id, 7);
        assert_eq!(op.worker_id, 2);
        assert_eq!(op.frontier_size, 128);
        assert_eq!(op.depth, 3);
    }

    #[test]
    fn wave14_tla_bfs_step_verify_rejects_zero_action_id() {
        // action_id == 0 is reserved for seeds and not valid at the tla-level
        // expand op.
        let op = TlaBfsStep::new(0, 0, 0, 0);
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.bfs_step");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tla_bfs_step_lower_propagates_verify_failure() {
        let op = TlaBfsStep::new(0, 0, 0, 0);
        let err = op.lower().unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave14_tla_bfs_step_lowers_to_verif_expand_step() {
        let op = TlaBfsStep::new(5, 1, 64, 2);
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].dialect(), "verif");
                assert_eq!(ops[0].op_name(), "verif.bfs_step");
            }
            Lowered::Leaf(_) => panic!("expected verif ops, got leaf"),
        }
    }

    #[test]
    fn wave14_tla_bfs_step_roundtrip_preserves_fields_in_verif() {
        // Cross-check: lowering a TlaBfsStep into a VerifBfsStep must
        // transport all fields through the boundary intact. This guards
        // the downstream backend from losing dispatch / locality info.
        let verif = crate::verif::VerifBfsStep::new_expand(42, 3, 256, 5);
        assert_eq!(verif.action_id, 42);
        assert_eq!(verif.worker_id, 3);
        assert_eq!(verif.frontier_size, 256);
        assert_eq!(verif.depth, 5);
        assert_eq!(verif.kind, BfsKind::Expand);
    }

    #[test]
    fn wave14_tla_bfs_step_is_registered_in_dialect() {
        let d = TlaDialect;
        assert!(d.op_names().contains(&"tla.bfs_step"));
    }

    // -------------------------------------------------------------------------
    // TlaSetRef — minimal operand for TlaSetUnion tests.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_set_ref_metadata_and_verify() {
        let r = TlaSetRef::new("S");
        assert_eq!(r.dialect(), "tla");
        assert_eq!(r.op_name(), "tla.set_ref");
        assert_eq!(r.kind(), OpKind::Expression);
        r.verify().expect("non-empty name should verify");
        // Display renders the name verbatim.
        assert_eq!(format!("{r}"), "S");
    }

    #[test]
    fn tla_set_ref_rejects_empty_name() {
        let r = TlaSetRef::new("");
        let err = r.verify().expect_err("empty name must fail verify");
        assert!(matches!(
            err,
            DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.set_ref",
                ..
            }
        ));
    }

    // -------------------------------------------------------------------------
    // TlaSetUnion — first populated tla:: expression op.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_set_union_construction_and_metadata() {
        let u = TlaSetUnion::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        assert_eq!(u.dialect(), "tla");
        assert_eq!(u.op_name(), "tla.set_union");
        assert_eq!(u.kind(), OpKind::Expression);
        assert_eq!(u.left.op_name(), "tla.set_ref");
        assert_eq!(u.right.op_name(), "tla.set_ref");
    }

    #[test]
    fn tla_set_union_verify_accepts_well_typed_operands() {
        let u = TlaSetUnion::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        u.verify()
            .expect("two set-ref expression operands should verify");
    }

    #[test]
    fn tla_set_union_verify_rejects_invariant_operand() {
        // TlaInvariant is OpKind::Invariant, not Expression — must be rejected.
        let u = TlaSetUnion::new(
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaInvariant::default()),
        );
        let err = u.verify().expect_err("Invariant-kind operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.set_union");
                assert!(message.contains("right"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_set_union_verify_rejects_cross_dialect_operand() {
        // A verif:: op is not a valid operand for a tla:: set_union.
        use crate::verif::{BfsKind, VerifBfsStep};
        let u = TlaSetUnion::new(
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
            Box::new(TlaSetRef::new("T")),
        );
        let err = u.verify().expect_err("cross-dialect operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.set_union");
                assert!(message.contains("left"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_set_union_verify_propagates_operand_verify_failure() {
        // TlaSetRef with empty name fails its own verify; set_union must
        // surface that via recursive verification.
        let u = TlaSetUnion::new(Box::new(TlaSetRef::new("")), Box::new(TlaSetRef::new("T")));
        let err = u.verify().expect_err("empty-name operand must fail");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                // Inner op reports itself, not the parent.
                assert_eq!(op, "tla.set_ref");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_set_union_pretty_print_is_stable() {
        let u = TlaSetUnion::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        // Display renders operand op_names, not the surface names — those are
        // structured and would need a richer printer walk. The stable token
        // form is what tests pin, keeping the printer deterministic.
        let rendered = format!("{u}");
        assert_eq!(rendered, "(tla.set_ref \\union tla.set_ref)");
    }

    #[test]
    fn tla_set_union_lowering_is_deferred() {
        // Lowering to `verif::` for expressions is a follow-up wave — today
        // the op should return NotImplemented so callers know it hasn't been
        // wired yet.
        let u = TlaSetUnion::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        let err = u.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.set_union"
            }
        ));
    }

    #[test]
    fn tla_dialect_lists_set_union() {
        let d = TlaDialect;
        assert!(d.op_names().contains(&"tla.set_union"));
    }

    // -------------------------------------------------------------------------
    // TlaSetIntersect — Wave 6 population, mirror of TlaSetUnion.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_set_intersect_construction_and_metadata() {
        let i = TlaSetIntersect::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        assert_eq!(i.dialect(), "tla");
        assert_eq!(i.op_name(), "tla.set_intersect");
        assert_eq!(i.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_set_intersect_verify_accepts_well_typed_operands() {
        let i = TlaSetIntersect::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        i.verify()
            .expect("two set-ref expression operands should verify");
    }

    #[test]
    fn tla_set_intersect_verify_rejects_invariant_operand() {
        // TlaInvariant is OpKind::Invariant, not Expression — must be rejected.
        let i = TlaSetIntersect::new(
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaInvariant::default()),
        );
        let err = i.verify().expect_err("Invariant-kind operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.set_intersect");
                assert!(message.contains("right"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_set_intersect_pretty_print_is_stable() {
        let i = TlaSetIntersect::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        assert_eq!(format!("{i}"), "(tla.set_ref \\intersect tla.set_ref)");
    }

    #[test]
    fn tla_set_intersect_lowering_is_deferred() {
        let i = TlaSetIntersect::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("T")));
        let err = i.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.set_intersect"
            }
        ));
    }

    // -------------------------------------------------------------------------
    // TlaSetCardinality — Wave 6 population, unary set → int.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_set_cardinality_construction_and_metadata() {
        let c = TlaSetCardinality::new(Box::new(TlaSetRef::new("S")));
        assert_eq!(c.dialect(), "tla");
        assert_eq!(c.op_name(), "tla.set_cardinality");
        assert_eq!(c.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_set_cardinality_verify_accepts_set_ref_operand() {
        let c = TlaSetCardinality::new(Box::new(TlaSetRef::new("S")));
        c.verify().expect("single set-ref operand should verify");
    }

    #[test]
    fn tla_set_cardinality_verify_rejects_cross_dialect_operand() {
        use crate::verif::{BfsKind, VerifBfsStep};
        let c = TlaSetCardinality::new(Box::new(VerifBfsStep {
            kind: BfsKind::Expand,
            action_id: 0,
            ..Default::default()
        }));
        let err = c.verify().expect_err("cross-dialect operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.set_cardinality");
                assert!(message.contains("set"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_set_cardinality_pretty_print_is_stable() {
        let c = TlaSetCardinality::new(Box::new(TlaSetRef::new("S")));
        assert_eq!(format!("{c}"), "Cardinality(tla.set_ref)");
    }

    #[test]
    fn tla_set_cardinality_verify_propagates_operand_failure() {
        // Inner operand fails its own verify — must surface.
        let c = TlaSetCardinality::new(Box::new(TlaSetRef::new("")));
        let err = c.verify().expect_err("empty-name operand must fail");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.set_ref");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    // -------------------------------------------------------------------------
    // TlaSetMember — Wave 6 population, binary (value, set) → bool.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_set_member_construction_and_metadata() {
        let m = TlaSetMember::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("S")));
        assert_eq!(m.dialect(), "tla");
        assert_eq!(m.op_name(), "tla.set_member");
        assert_eq!(m.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_set_member_verify_accepts_well_typed_operands() {
        let m = TlaSetMember::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("S")));
        m.verify()
            .expect("two set-ref expression operands should verify");
    }

    #[test]
    fn tla_set_member_verify_rejects_invariant_element() {
        // Invariant-kind element must be rejected — element side first.
        let m = TlaSetMember::new(
            Box::new(TlaInvariant::default()),
            Box::new(TlaSetRef::new("S")),
        );
        let err = m.verify().expect_err("Invariant-kind element must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.set_member");
                assert!(message.contains("element"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_set_member_pretty_print_is_stable() {
        let m = TlaSetMember::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("S")));
        assert_eq!(format!("{m}"), "(tla.set_ref \\in tla.set_ref)");
    }

    #[test]
    fn tla_set_member_lowering_is_deferred() {
        let m = TlaSetMember::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("S")));
        let err = m.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.set_member"
            }
        ));
    }

    // -------------------------------------------------------------------------
    // Dialect registration covers all Wave 6 additions.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_dialect_lists_wave6_ops() {
        let d = TlaDialect;
        let names = d.op_names();
        assert!(names.contains(&"tla.set_intersect"));
        assert!(names.contains(&"tla.set_cardinality"));
        assert!(names.contains(&"tla.set_member"));
    }

    // -------------------------------------------------------------------------
    // TlaAnd — Wave 7 population, binary logical conjunction.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_and_construction_and_metadata() {
        let a = TlaAnd::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("Q")));
        assert_eq!(a.dialect(), "tla");
        assert_eq!(a.op_name(), "tla.and");
        assert_eq!(a.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_and_verify_accepts_well_typed_operands() {
        let a = TlaAnd::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("Q")));
        a.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_and_verify_rejects_invariant_operand() {
        let a = TlaAnd::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaInvariant::default()),
        );
        let err = a.verify().expect_err("Invariant-kind operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.and");
                assert!(message.contains("right"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_and_verify_rejects_cross_dialect_operand() {
        use crate::verif::{BfsKind, VerifBfsStep};
        let a = TlaAnd::new(
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
            Box::new(TlaSetRef::new("Q")),
        );
        let err = a.verify().expect_err("cross-dialect operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.and");
                assert!(message.contains("left"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_and_pretty_print_is_stable() {
        let a = TlaAnd::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("Q")));
        assert_eq!(format!("{a}"), "(tla.set_ref /\\ tla.set_ref)");
    }

    #[test]
    fn tla_and_lowers_to_verif_bool_and() {
        let a = TlaAnd::new(Box::new(TlaVarRef::new("p")), Box::new(TlaVarRef::new("q")));
        let lowered = a.lower().expect("lowering should succeed");
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 3);
                assert_eq!(ops[0].op_name(), "verif.scalar_int");
                assert_eq!(ops[1].op_name(), "verif.scalar_int");
                assert_eq!(ops[2].op_name(), "verif.bool_and");
            }
            Lowered::Leaf(_) => panic!("expected Lowered::Ops"),
        }
    }

    #[test]
    fn tla_and_lowering_propagates_verify_failure() {
        // Cross-dialect operand fails verify; must surface via `self.verify()?`.
        let a = TlaAnd::new(
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
            Box::new(TlaVarRef::new("q")),
        );
        let err = a.lower().expect_err("cross-dialect operand must fail");
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    // -------------------------------------------------------------------------
    // TlaOr — Wave 7 population, binary logical disjunction.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_or_construction_and_metadata() {
        let o = TlaOr::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("Q")));
        assert_eq!(o.dialect(), "tla");
        assert_eq!(o.op_name(), "tla.or");
        assert_eq!(o.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_or_verify_accepts_well_typed_operands() {
        let o = TlaOr::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("Q")));
        o.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_or_verify_rejects_invariant_operand() {
        // Per-op adversarial facet — #4273. `TlaAnd` has this test, but
        // `TlaOr` did not, leaving the facet transitively covered through the
        // shared `verify_boolean_operand` helper but *not* pinned to the
        // `tla.or` mnemonic. A regression that, say, made `TlaOr::verify()`
        // check only the left operand would be caught by the `TlaAnd` test
        // but slip through here. This test pins it.
        let o = TlaOr::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaInvariant::default()),
        );
        let err = o.verify().expect_err("Invariant-kind operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.or");
                assert!(message.contains("right"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_or_verify_rejects_cross_dialect_operand() {
        // Per-op adversarial facet — #4273. Complements
        // `tla_or_verify_rejects_invariant_operand` by checking the
        // cross-dialect path on the *left* operand, which keeps this test
        // shape aligned with `tla_and_verify_rejects_cross_dialect_operand`.
        use crate::verif::{BfsKind, VerifBfsStep};
        let o = TlaOr::new(
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
            Box::new(TlaSetRef::new("Q")),
        );
        let err = o.verify().expect_err("cross-dialect operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.or");
                assert!(message.contains("left"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_or_verify_propagates_operand_failure() {
        // Inner TlaSetRef with empty name fails its own verify; must surface.
        let o = TlaOr::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("")));
        let err = o.verify().expect_err("empty-name operand must fail");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                // Inner op reports itself, not parent.
                assert_eq!(op, "tla.set_ref");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_or_pretty_print_is_stable() {
        let o = TlaOr::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("Q")));
        assert_eq!(format!("{o}"), "(tla.set_ref \\/ tla.set_ref)");
    }

    #[test]
    fn tla_or_lowers_to_verif_bool_or() {
        let o = TlaOr::new(Box::new(TlaVarRef::new("p")), Box::new(TlaVarRef::new("q")));
        let lowered = o.lower().expect("lowering should succeed");
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 3);
                assert_eq!(ops[2].op_name(), "verif.bool_or");
            }
            Lowered::Leaf(_) => panic!("expected Lowered::Ops"),
        }
    }

    // -------------------------------------------------------------------------
    // TlaNot — Wave 7 population, unary logical negation.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_not_construction_and_metadata() {
        let n = TlaNot::new(Box::new(TlaSetRef::new("P")));
        assert_eq!(n.dialect(), "tla");
        assert_eq!(n.op_name(), "tla.not");
        assert_eq!(n.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_not_verify_accepts_expression_operand() {
        let n = TlaNot::new(Box::new(TlaSetRef::new("P")));
        n.verify().expect("single expression operand should verify");
    }

    #[test]
    fn tla_not_verify_rejects_invariant_operand() {
        // TlaInvariant has OpKind::Invariant and must be rejected.
        let n = TlaNot::new(Box::new(TlaInvariant::default()));
        let err = n.verify().expect_err("Invariant-kind operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.not");
                assert!(message.contains("operand"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_not_verify_rejects_cross_dialect_operand() {
        // Per-op adversarial facet — #4273. `TlaNot`'s sole operand is
        // unary, so cross-dialect rejection had no explicit per-op test
        // before — only the transitive helper-level coverage through
        // `verify_boolean_operand`. This test pins the rejection to the
        // `tla.not` parent mnemonic directly.
        use crate::verif::{BfsKind, VerifBfsStep};
        let n = TlaNot::new(Box::new(VerifBfsStep {
            kind: BfsKind::Expand,
            action_id: 0,
            ..Default::default()
        }));
        let err = n.verify().expect_err("cross-dialect operand must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.not");
                assert!(message.contains("operand"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_not_verify_propagates_operand_failure() {
        // Per-op adversarial facet — #4273. Inner empty-name `TlaSetRef`
        // fails its own verify; `TlaNot` must surface the inner op's report
        // unchanged.
        let n = TlaNot::new(Box::new(TlaSetRef::new("")));
        let err = n.verify().expect_err("empty-name operand must fail");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                // Inner op reports itself, not the parent.
                assert_eq!(op, "tla.set_ref");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_not_pretty_print_is_stable() {
        let n = TlaNot::new(Box::new(TlaSetRef::new("P")));
        assert_eq!(format!("{n}"), "~tla.set_ref");
    }

    #[test]
    fn tla_not_lowers_to_verif_bool_not() {
        let n = TlaNot::new(Box::new(TlaVarRef::new("p")));
        let lowered = n.lower().expect("lowering should succeed");
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 2, "expected [verif.scalar_int, verif.bool_not]");
                assert_eq!(ops[0].op_name(), "verif.scalar_int");
                assert_eq!(ops[1].op_name(), "verif.bool_not");
            }
            Lowered::Leaf(_) => panic!("expected Lowered::Ops"),
        }
    }

    // -------------------------------------------------------------------------
    // TlaEq — Wave 7 population, binary value equality.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_eq_construction_and_metadata() {
        let e = TlaEq::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(e.dialect(), "tla");
        assert_eq!(e.op_name(), "tla.eq");
        assert_eq!(e.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_eq_verify_accepts_well_typed_operands() {
        let e = TlaEq::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        e.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_eq_verify_rejects_invariant_lhs() {
        // Invariant-kind lhs must be rejected — lhs side is checked first.
        let e = TlaEq::new(
            Box::new(TlaInvariant::default()),
            Box::new(TlaSetRef::new("y")),
        );
        let err = e.verify().expect_err("Invariant-kind lhs must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.eq");
                assert!(message.contains("lhs"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_eq_pretty_print_is_stable() {
        let e = TlaEq::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{e}"), "(tla.set_ref = tla.set_ref)");
    }

    #[test]
    fn tla_eq_lowers_to_verif_int_eq_for_non_set_operands() {
        let e = TlaEq::new(Box::new(TlaVarRef::new("x")), Box::new(TlaVarRef::new("y")));
        let lowered = e.lower().expect("lowering should succeed");
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 3);
                assert_eq!(ops[2].op_name(), "verif.int_eq");
            }
            Lowered::Leaf(_) => panic!("expected Lowered::Ops"),
        }
    }

    #[test]
    fn tla_eq_lowering_rejects_set_typed_operand() {
        // `TlaSetRef` is set-valued (its op_name starts with `tla.set_`).
        // TlaEq explicitly rejects set-typed operands at lowering time until
        // the typed IR lands. The error is LoweringFailed, not NotImplemented
        // — the lowering was attempted and failed structurally.
        let e = TlaEq::new(Box::new(TlaSetRef::new("S")), Box::new(TlaVarRef::new("y")));
        let err = e.lower().expect_err("set-typed operand must fail");
        match err {
            DialectError::LoweringFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.eq");
                assert!(message.contains("set-typed"));
                assert!(message.contains("lhs"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    // -------------------------------------------------------------------------
    // Dialect registration covers all Wave 7 additions.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_dialect_lists_wave7_ops() {
        let d = TlaDialect;
        let names = d.op_names();
        assert!(names.contains(&"tla.and"));
        assert!(names.contains(&"tla.or"));
        assert!(names.contains(&"tla.not"));
        assert!(names.contains(&"tla.eq"));
    }

    // -------------------------------------------------------------------------
    // TlaIfThenElse — Wave 8 population, ternary conditional expression.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_if_then_else_construction_and_metadata() {
        let i = TlaIfThenElse::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaSetRef::new("a")),
            Box::new(TlaSetRef::new("b")),
        );
        assert_eq!(i.dialect(), "tla");
        assert_eq!(i.op_name(), "tla.if_then_else");
        assert_eq!(i.kind(), OpKind::Expression);
        assert_eq!(i.cond.op_name(), "tla.set_ref");
        assert_eq!(i.then_value.op_name(), "tla.set_ref");
        assert_eq!(i.else_value.op_name(), "tla.set_ref");
    }

    #[test]
    fn tla_if_then_else_verify_accepts_three_expression_operands() {
        let i = TlaIfThenElse::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaSetRef::new("a")),
            Box::new(TlaSetRef::new("b")),
        );
        i.verify().expect("three expression operands should verify");
    }

    #[test]
    fn tla_if_then_else_verify_rejects_invariant_cond() {
        // Invariant-kind cond must be rejected — cond is checked first, so
        // the message should name `cond` specifically.
        let i = TlaIfThenElse::new(
            Box::new(TlaInvariant::default()),
            Box::new(TlaSetRef::new("a")),
            Box::new(TlaSetRef::new("b")),
        );
        let err = i.verify().expect_err("Invariant-kind cond must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.if_then_else");
                assert!(message.contains("cond"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_if_then_else_verify_rejects_invariant_then_value() {
        // then_value must be an Expression — Invariant-kind rejected.
        // cond is fine (an Expression), so the failure must name
        // `then_value` specifically.
        let i = TlaIfThenElse::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaInvariant::default()),
            Box::new(TlaSetRef::new("b")),
        );
        let err = i.verify().expect_err("Invariant-kind then_value must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.if_then_else");
                assert!(message.contains("then_value"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_if_then_else_verify_rejects_invariant_else_value() {
        // else_value must be an Expression — Invariant-kind rejected.
        // cond and then_value are fine (Expressions), so the failure must
        // name `else_value` specifically.
        let i = TlaIfThenElse::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaSetRef::new("a")),
            Box::new(TlaInvariant::default()),
        );
        let err = i.verify().expect_err("Invariant-kind else_value must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.if_then_else");
                assert!(message.contains("else_value"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_if_then_else_verify_rejects_cross_dialect_cond() {
        use crate::verif::{BfsKind, VerifBfsStep};
        let i = TlaIfThenElse::new(
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
            Box::new(TlaSetRef::new("a")),
            Box::new(TlaSetRef::new("b")),
        );
        let err = i.verify().expect_err("cross-dialect cond must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.if_then_else");
                assert!(message.contains("cond"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_if_then_else_verify_propagates_operand_verify_failure() {
        // Inner empty-name TlaSetRef fails its own verify — the then-branch
        // path here specifically exercises recursive verify propagation
        // (cond is fine, then is the one that fails).
        let i = TlaIfThenElse::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaSetRef::new("")),
            Box::new(TlaSetRef::new("b")),
        );
        let err = i.verify().expect_err("empty-name then operand must fail");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                // Inner op reports itself, not the parent.
                assert_eq!(op, "tla.set_ref");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_if_then_else_pretty_print_is_stable() {
        let i = TlaIfThenElse::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaSetRef::new("a")),
            Box::new(TlaSetRef::new("b")),
        );
        assert_eq!(
            format!("{i}"),
            "IF tla.set_ref THEN tla.set_ref ELSE tla.set_ref"
        );
    }

    #[test]
    fn tla_if_then_else_lowering_is_deferred() {
        let i = TlaIfThenElse::new(
            Box::new(TlaSetRef::new("P")),
            Box::new(TlaSetRef::new("a")),
            Box::new(TlaSetRef::new("b")),
        );
        let err = i.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.if_then_else"
            }
        ));
    }

    // -------------------------------------------------------------------------
    // TlaVarRef — Wave 8 operand primitive.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_var_ref_metadata_and_verify() {
        let v = TlaVarRef::new("x");
        assert_eq!(v.dialect(), "tla");
        assert_eq!(v.op_name(), "tla.var_ref");
        assert_eq!(v.kind(), OpKind::Expression);
        v.verify().expect("non-empty name should verify");
        assert_eq!(format!("{v}"), "x");
    }

    #[test]
    fn tla_var_ref_rejects_empty_name() {
        let v = TlaVarRef::new("");
        let err = v.verify().expect_err("empty name must fail verify");
        assert!(matches!(
            err,
            DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.var_ref",
                ..
            }
        ));
    }

    #[test]
    fn tla_var_ref_lowers_to_verif_scalar_int_placeholder() {
        // Wave 12 placeholder: var_ref lowers to a single `verif.scalar_int(0)`
        // op. Real lowering needs state indexing + symbol table, both out of
        // scope for Wave 12.
        let v = TlaVarRef::new("x");
        let lowered = v.lower().expect("lowering should succeed");
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(ops.len(), 1);
                assert_eq!(ops[0].dialect(), "verif");
                assert_eq!(ops[0].op_name(), "verif.scalar_int");
            }
            Lowered::Leaf(_) => panic!("expected Lowered::Ops"),
        }
    }

    #[test]
    fn tla_var_ref_lowering_propagates_empty_name_failure() {
        let v = TlaVarRef::new("");
        let err = v.lower().expect_err("empty name must fail");
        assert!(matches!(
            err,
            DialectError::VerifyFailed {
                dialect: "tla",
                op: "tla.var_ref",
                ..
            }
        ));
    }

    // -------------------------------------------------------------------------
    // TlaAssign — Wave 8 population, primed-variable assignment.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_assign_construction_and_metadata() {
        let a = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        assert_eq!(a.dialect(), "tla");
        assert_eq!(a.op_name(), "tla.assign");
        // First non-stub StateTransform op.
        assert_eq!(a.kind(), OpKind::StateTransform);
    }

    #[test]
    fn tla_assign_verify_accepts_var_ref_target_and_expression_value() {
        let a = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        a.verify()
            .expect("var_ref target + expression value should verify");
    }

    #[test]
    fn tla_assign_verify_rejects_non_var_ref_target() {
        // Target must specifically be tla.var_ref, not tla.set_ref.
        let a = TlaAssign::new(Box::new(TlaSetRef::new("S")), Box::new(TlaSetRef::new("e")));
        let err = a
            .verify()
            .expect_err("set_ref target must be rejected by tla.assign");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.assign");
                assert!(message.contains("tla.var_ref"));
                assert!(message.contains("tla.set_ref"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_assign_verify_rejects_cross_dialect_target() {
        use crate::verif::{BfsKind, VerifBfsStep};
        let a = TlaAssign::new(
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
            Box::new(TlaSetRef::new("e")),
        );
        let err = a.verify().expect_err("cross-dialect target must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.assign");
                assert!(message.contains("target"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_assign_verify_rejects_invariant_value() {
        // Value side must be Expression, not Invariant.
        let a = TlaAssign::new(
            Box::new(TlaVarRef::new("x")),
            Box::new(TlaInvariant::default()),
        );
        let err = a.verify().expect_err("Invariant-kind value must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.assign");
                assert!(message.contains("value"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_assign_verify_propagates_target_verify_failure() {
        // TlaVarRef with empty name fails its own verify; must surface.
        let a = TlaAssign::new(Box::new(TlaVarRef::new("")), Box::new(TlaSetRef::new("e")));
        let err = a.verify().expect_err("empty-name target must fail");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                // Inner op reports itself.
                assert_eq!(op, "tla.var_ref");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_assign_pretty_print_is_stable() {
        let a = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        // Target op_name + prime marker + value op_name.
        assert_eq!(format!("{a}"), "tla.var_ref' = tla.set_ref");
    }

    #[test]
    fn tla_assign_lowering_is_deferred() {
        let a = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        let err = a.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.assign"
            }
        ));
    }

    // -------------------------------------------------------------------------
    // Dialect registration covers all Wave 8 additions.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_dialect_lists_wave8_ops() {
        let d = TlaDialect;
        let names = d.op_names();
        assert!(names.contains(&"tla.if_then_else"));
        assert!(names.contains(&"tla.var_ref"));
        assert!(names.contains(&"tla.assign"));
    }

    // -------------------------------------------------------------------------
    // Wave 9 — binary integer comparison + arithmetic ops.
    //
    // The 9 new ops (`tla.lt`, `tla.le`, `tla.gt`, `tla.ge`, `tla.add`,
    // `tla.sub`, `tla.mul`, `tla.div`, `tla.mod`) are structurally identical:
    // two expression operands, `OpKind::Expression`, shared
    // `verify_arith_operand` helper, deferred lowering. To keep per-op
    // coverage without 54 near-identical test functions, the test rubric is:
    //
    //   - One *explicit* `tla_<op>_construction_and_metadata` test per op
    //     (9 tests) — pins struct name, mnemonic, kind, operand op_names.
    //   - One *explicit* `tla_<op>_verify_accepts_well_typed_operands` test
    //     per op (9 tests) — exercises the verify path on the specific type.
    //   - One *explicit* `tla_<op>_pretty_print_is_stable` test per op (9
    //     tests) — pins the Display symbol per op.
    //   - One *explicit* `tla_<op>_lowering_is_deferred` test per op (9
    //     tests) — pins the NotImplemented op-name per op.
    //   - A *parameterized* `wave9_verify_rejects_wrong_kind` test (1) that
    //     covers all 9 ops' verify-reject-on-Invariant facet in a loop
    //     keyed on the dyn-constructor, with asserts keyed on the parent
    //     mnemonic so failures localize to the offending op.
    //   - A *parameterized* `wave9_verify_rejects_cross_dialect` test (1)
    //     that covers all 9 ops' cross-dialect reject facet the same way.
    //   - A *parameterized* `wave9_verify_propagates_operand_failure` test
    //     (1) that covers recursive verify propagation for all 9 ops.
    //
    // That yields 39 explicit + 3 parameterized + 1 registration = 43 tests
    // with every op still exercising all 6 facets (construction, accept,
    // reject-kind, reject-dialect, pretty-print, lowering) + propagation.
    // The facets that are structurally identical across the 9 ops
    // (verify-reject shape, propagation) are tested once in a loop to keep
    // test LOC sane — the bug you'd miss from "6 explicit tests per op"
    // that the parameterized version catches is exactly the one where one
    // op's mnemonic or helper wiring drifts from the family shape, because
    // the loop asserts on each op's own mnemonic.
    // -------------------------------------------------------------------------

    // Type-erased constructor used by the Wave 9 parameterized tests so each
    // entry in the op-table can build the op under test with arbitrary
    // operands. Returning `Box<dyn DialectOp>` lets the tests iterate over a
    // uniform op handle regardless of the concrete type.
    type Wave9Ctor = fn(Box<dyn DialectOp>, Box<dyn DialectOp>) -> Box<dyn DialectOp>;

    /// The full Wave 9 op table. Kept in one place so a single `wave9_ops()`
    /// call drives all parameterized tests. Order is not significant.
    fn wave9_ops() -> Vec<(&'static str, Wave9Ctor)> {
        vec![
            ("tla.lt", |l, r| Box::new(TlaLt::new(l, r))),
            ("tla.le", |l, r| Box::new(TlaLe::new(l, r))),
            ("tla.gt", |l, r| Box::new(TlaGt::new(l, r))),
            ("tla.ge", |l, r| Box::new(TlaGe::new(l, r))),
            ("tla.add", |l, r| Box::new(TlaAdd::new(l, r))),
            ("tla.sub", |l, r| Box::new(TlaSub::new(l, r))),
            ("tla.mul", |l, r| Box::new(TlaMul::new(l, r))),
            ("tla.div", |l, r| Box::new(TlaDiv::new(l, r))),
            ("tla.mod", |l, r| Box::new(TlaMod::new(l, r))),
        ]
    }

    // --- Per-op construction + metadata (9 tests) ----------------------------

    #[test]
    fn tla_lt_construction_and_metadata() {
        let op = TlaLt::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.lt");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.left.op_name(), "tla.set_ref");
        assert_eq!(op.right.op_name(), "tla.set_ref");
    }

    #[test]
    fn tla_le_construction_and_metadata() {
        let op = TlaLe::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.le");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_gt_construction_and_metadata() {
        let op = TlaGt::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.gt");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_ge_construction_and_metadata() {
        let op = TlaGe::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.ge");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_add_construction_and_metadata() {
        let op = TlaAdd::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.add");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_sub_construction_and_metadata() {
        let op = TlaSub::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.sub");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_mul_construction_and_metadata() {
        let op = TlaMul::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.mul");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_div_construction_and_metadata() {
        let op = TlaDiv::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.div");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    #[test]
    fn tla_mod_construction_and_metadata() {
        let op = TlaMod::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.mod");
        assert_eq!(op.kind(), OpKind::Expression);
    }

    // --- Per-op verify-accept (9 tests) --------------------------------------

    #[test]
    fn tla_lt_verify_accepts_well_typed_operands() {
        let op = TlaLt::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_le_verify_accepts_well_typed_operands() {
        let op = TlaLe::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_gt_verify_accepts_well_typed_operands() {
        let op = TlaGt::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_ge_verify_accepts_well_typed_operands() {
        let op = TlaGe::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_add_verify_accepts_well_typed_operands() {
        let op = TlaAdd::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_sub_verify_accepts_well_typed_operands() {
        let op = TlaSub::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_mul_verify_accepts_well_typed_operands() {
        let op = TlaMul::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_div_verify_accepts_well_typed_operands() {
        let op = TlaDiv::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    #[test]
    fn tla_mod_verify_accepts_well_typed_operands() {
        let op = TlaMod::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        op.verify().expect("two expression operands should verify");
    }

    // --- Per-op pretty-print (9 tests) ---------------------------------------
    //
    // Separate explicit tests per op because the *rendered symbol* is what
    // distinguishes each op's Display impl — a parameterized loop would
    // obscure which op produces which symbol.

    #[test]
    fn tla_lt_pretty_print_is_stable() {
        let op = TlaLt::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref < tla.set_ref)");
    }

    #[test]
    fn tla_le_pretty_print_is_stable() {
        let op = TlaLe::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref <= tla.set_ref)");
    }

    #[test]
    fn tla_gt_pretty_print_is_stable() {
        let op = TlaGt::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref > tla.set_ref)");
    }

    #[test]
    fn tla_ge_pretty_print_is_stable() {
        let op = TlaGe::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref >= tla.set_ref)");
    }

    #[test]
    fn tla_add_pretty_print_is_stable() {
        let op = TlaAdd::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref + tla.set_ref)");
    }

    #[test]
    fn tla_sub_pretty_print_is_stable() {
        let op = TlaSub::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref - tla.set_ref)");
    }

    #[test]
    fn tla_mul_pretty_print_is_stable() {
        let op = TlaMul::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref * tla.set_ref)");
    }

    #[test]
    fn tla_div_pretty_print_is_stable() {
        let op = TlaDiv::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        // TLA+ convention: `\div` (escaped as `\\div` in the Rust string).
        assert_eq!(format!("{op}"), "(tla.set_ref \\div tla.set_ref)");
    }

    #[test]
    fn tla_mod_pretty_print_is_stable() {
        let op = TlaMod::new(Box::new(TlaSetRef::new("x")), Box::new(TlaSetRef::new("y")));
        assert_eq!(format!("{op}"), "(tla.set_ref % tla.set_ref)");
    }

    // --- Per-op Wave 12 lowering (9 tests) -----------------------------------
    //
    // Each `tla::` arith/cmp op lowers to the flat `Lowered::Ops` sequence
    // `[verif.scalar_int, verif.scalar_int, verif.<op>]` when the operands are
    // `TlaVarRef`s (each var_ref lowers to a single `VerifScalarInt(0)`
    // placeholder in Wave 12). Tests pin both the sequence length and the
    // terminal verif op name.

    fn wave12_arith_operands() -> (Box<dyn DialectOp>, Box<dyn DialectOp>) {
        (Box::new(TlaVarRef::new("x")), Box::new(TlaVarRef::new("y")))
    }

    fn assert_lowered_sequence_ends_with(lowered: Lowered, expected_mnemonic: &str) {
        match lowered {
            Lowered::Ops(ops) => {
                assert_eq!(
                    ops.len(),
                    3,
                    "expected [verif.scalar_int, verif.scalar_int, {expected_mnemonic}]"
                );
                assert_eq!(ops[0].dialect(), "verif");
                assert_eq!(ops[0].op_name(), "verif.scalar_int");
                assert_eq!(ops[1].dialect(), "verif");
                assert_eq!(ops[1].op_name(), "verif.scalar_int");
                assert_eq!(ops[2].dialect(), "verif");
                assert_eq!(ops[2].op_name(), expected_mnemonic);
            }
            Lowered::Leaf(_) => panic!("expected Lowered::Ops for {expected_mnemonic}"),
        }
    }

    #[test]
    fn tla_lt_lowers_to_verif_int_lt() {
        let (l, r) = wave12_arith_operands();
        let op = TlaLt::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_lt");
    }

    #[test]
    fn tla_le_lowers_to_verif_int_le() {
        let (l, r) = wave12_arith_operands();
        let op = TlaLe::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_le");
    }

    #[test]
    fn tla_gt_lowers_to_verif_int_gt() {
        let (l, r) = wave12_arith_operands();
        let op = TlaGt::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_gt");
    }

    #[test]
    fn tla_ge_lowers_to_verif_int_ge() {
        let (l, r) = wave12_arith_operands();
        let op = TlaGe::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_ge");
    }

    #[test]
    fn tla_add_lowers_to_verif_int_add() {
        let (l, r) = wave12_arith_operands();
        let op = TlaAdd::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_add");
    }

    #[test]
    fn tla_sub_lowers_to_verif_int_sub() {
        let (l, r) = wave12_arith_operands();
        let op = TlaSub::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_sub");
    }

    #[test]
    fn tla_mul_lowers_to_verif_int_mul() {
        let (l, r) = wave12_arith_operands();
        let op = TlaMul::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_mul");
    }

    #[test]
    fn tla_div_lowers_to_verif_int_div() {
        let (l, r) = wave12_arith_operands();
        let op = TlaDiv::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_div");
    }

    #[test]
    fn tla_mod_lowers_to_verif_int_mod() {
        let (l, r) = wave12_arith_operands();
        let op = TlaMod::new(l, r);
        let lowered = op.lower().expect("lowering should succeed");
        assert_lowered_sequence_ends_with(lowered, "verif.int_mod");
    }

    #[test]
    fn tla_arith_lowering_propagates_operand_failure() {
        // Operand with empty name fails verify, which tla_add.lower() must
        // surface through its `self.verify()?` gate.
        let op = TlaAdd::new(Box::new(TlaVarRef::new("x")), Box::new(TlaVarRef::new("")));
        let err = op.lower().expect_err("empty-name operand must fail");
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn tla_arith_lowering_fails_when_operand_lacks_lowering() {
        // A TlaSetRef operand verifies (it's OpKind::Expression) but its own
        // `lower()` returns NotImplemented — that must propagate through the
        // parent's `lower_binary_to_verif_marker` call.
        let op = TlaAdd::new(Box::new(TlaSetRef::new("S")), Box::new(TlaVarRef::new("y")));
        let err = op
            .lower()
            .expect_err("operand without lowering must fail parent lowering");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.set_ref"
            }
        ));
    }

    // --- Parameterized verify-reject tests (3 tests covering all 9 ops) -----

    #[test]
    fn wave9_verify_rejects_invariant_operand() {
        // For each Wave 9 op: build it with an Invariant-kind right operand,
        // verify must fail with a message naming the parent op and the
        // `right` side. We check the right side specifically so a regression
        // where one op's verify forgets to check the right operand surfaces
        // as a failure on that specific op.
        for (mnemonic, ctor) in wave9_ops() {
            let op = ctor(
                Box::new(TlaSetRef::new("x")),
                Box::<TlaInvariant>::default(),
            );
            let err = op
                .verify()
                .expect_err("Invariant-kind operand must fail for Wave 9 op");
            match err {
                DialectError::VerifyFailed {
                    dialect,
                    op: parent,
                    message,
                } => {
                    assert_eq!(dialect, "tla", "dialect for {mnemonic}");
                    assert_eq!(
                        parent, mnemonic,
                        "verify-failure parent op should equal {mnemonic}"
                    );
                    assert!(
                        message.contains("right"),
                        "{mnemonic}: message should name the `right` side, got {message:?}"
                    );
                    assert!(
                        message.contains("Expression"),
                        "{mnemonic}: message should reference Expression kind, got {message:?}"
                    );
                }
                other => panic!("{mnemonic}: unexpected error shape: {other:?}"),
            }
        }
    }

    #[test]
    fn wave9_verify_rejects_cross_dialect_operand() {
        use crate::verif::{BfsKind, VerifBfsStep};
        for (mnemonic, ctor) in wave9_ops() {
            // Verif-dialect op on the *left* so failures point at the left
            // side — complements the Invariant-kind test above which targets
            // the right side.
            let op = ctor(
                Box::new(VerifBfsStep {
                    kind: BfsKind::Expand,
                    action_id: 0,
                    ..Default::default()
                }),
                Box::new(TlaSetRef::new("y")),
            );
            let err = op
                .verify()
                .expect_err("cross-dialect operand must fail for Wave 9 op");
            match err {
                DialectError::VerifyFailed {
                    dialect,
                    op: parent,
                    message,
                } => {
                    assert_eq!(dialect, "tla", "dialect for {mnemonic}");
                    assert_eq!(
                        parent, mnemonic,
                        "verify-failure parent op should equal {mnemonic}"
                    );
                    assert!(
                        message.contains("left"),
                        "{mnemonic}: message should name the `left` side, got {message:?}"
                    );
                    assert!(
                        message.contains("tla"),
                        "{mnemonic}: message should reference tla dialect, got {message:?}"
                    );
                }
                other => panic!("{mnemonic}: unexpected error shape: {other:?}"),
            }
        }
    }

    #[test]
    fn wave9_verify_propagates_operand_failure() {
        // Empty-name TlaSetRef fails its own verify — that must surface
        // through each Wave 9 op unchanged (inner op reports itself, not
        // the parent).
        for (mnemonic, ctor) in wave9_ops() {
            let op = ctor(Box::new(TlaSetRef::new("")), Box::new(TlaSetRef::new("y")));
            let err = op
                .verify()
                .expect_err("empty-name operand must fail through Wave 9 op");
            match err {
                DialectError::VerifyFailed {
                    dialect, op: inner, ..
                } => {
                    assert_eq!(dialect, "tla", "dialect for {mnemonic}");
                    // Inner op reports itself, not the parent.
                    assert_eq!(
                        inner, "tla.set_ref",
                        "{mnemonic}: inner op must report itself on recursive verify"
                    );
                }
                other => panic!("{mnemonic}: unexpected error shape: {other:?}"),
            }
        }
    }

    // --- Dialect registration covers all Wave 9 additions --------------------

    #[test]
    fn tla_dialect_lists_wave9_ops() {
        let d = TlaDialect;
        let names = d.op_names();
        assert!(names.contains(&"tla.lt"));
        assert!(names.contains(&"tla.le"));
        assert!(names.contains(&"tla.gt"));
        assert!(names.contains(&"tla.ge"));
        assert!(names.contains(&"tla.add"));
        assert!(names.contains(&"tla.sub"));
        assert!(names.contains(&"tla.mul"));
        assert!(names.contains(&"tla.div"));
        assert!(names.contains(&"tla.mod"));
    }

    // -------------------------------------------------------------------------
    // TlaAction — Wave 10 population, first compound StateTransform op.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_action_construction_and_metadata() {
        let body = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        let a = TlaAction::new("Send", Box::new(body));
        assert_eq!(a.dialect(), "tla");
        assert_eq!(a.op_name(), "tla.action");
        assert_eq!(a.kind(), OpKind::StateTransform);
        assert_eq!(a.name, "Send");
        assert_eq!(a.body.op_name(), "tla.assign");
    }

    #[test]
    fn tla_action_verify_accepts_state_transform_body() {
        // TlaAssign is the canonical state-transform body; pure
        // primed-variable assignment drives a state transition.
        let body = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        let a = TlaAction::new("Send", Box::new(body));
        a.verify()
            .expect("state-transform body should verify for an action");
    }

    #[test]
    fn tla_action_verify_accepts_expression_body() {
        // A guard-only action body is an Expression (e.g. a TlaAnd of
        // guards). Verify must accept this shape.
        let guard = TlaAnd::new(Box::new(TlaSetRef::new("P")), Box::new(TlaSetRef::new("Q")));
        let a = TlaAction::new("Guard", Box::new(guard));
        a.verify()
            .expect("expression-kind guard-only body should verify");
    }

    #[test]
    fn tla_action_verify_rejects_empty_name() {
        let body = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        let a = TlaAction::new("", Box::new(body));
        let err = a.verify().expect_err("empty name must fail verify");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.action");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_action_verify_rejects_wrong_kind_body() {
        // An Invariant-kind body is structurally invalid for an action —
        // accepted kinds are StateTransform and Expression only.
        let a = TlaAction::new("BadInv", Box::new(TlaInvariant::default()));
        let err = a
            .verify()
            .expect_err("Invariant-kind body must fail for an action");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.action");
                assert!(message.contains("StateTransform"));
                assert!(message.contains("Expression"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_action_verify_rejects_cross_dialect_body() {
        // A verif:: op is not a valid action body.
        use crate::verif::{BfsKind, VerifBfsStep};
        let a = TlaAction::new(
            "BadDialect",
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
        );
        let err = a.verify().expect_err("cross-dialect body must fail");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.action");
                assert!(message.contains("body"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_action_verify_propagates_body_failure() {
        // Inner TlaAssign with an empty-name TlaVarRef target fails its
        // own verify; TlaAction must surface that via recursive verification.
        let body = TlaAssign::new(Box::new(TlaVarRef::new("")), Box::new(TlaSetRef::new("e")));
        let a = TlaAction::new("Send", Box::new(body));
        let err = a.verify().expect_err("empty-name target must fail");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                // Inner op reports itself — TlaVarRef's verify fires first.
                assert_eq!(op, "tla.var_ref");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_action_pretty_print_is_stable() {
        let body = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        let a = TlaAction::new("Send", Box::new(body));
        // Surface action name + `: ` + body's stable op_name token.
        assert_eq!(format!("{a}"), "Send: tla.assign");
    }

    #[test]
    fn tla_action_lowering_is_deferred() {
        let body = TlaAssign::new(Box::new(TlaVarRef::new("x")), Box::new(TlaSetRef::new("e")));
        let a = TlaAction::new("Send", Box::new(body));
        let err = a.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.action"
            }
        ));
    }

    // -------------------------------------------------------------------------
    // TlaNext — Wave 10 population, disjunction of actions.
    // -------------------------------------------------------------------------

    /// Small helper to build a well-formed named action for `TlaNext` tests.
    fn make_action(name: &str, var: &str) -> Box<dyn DialectOp> {
        let body = TlaAssign::new(Box::new(TlaVarRef::new(var)), Box::new(TlaSetRef::new("e")));
        Box::new(TlaAction::new(name, Box::new(body)))
    }

    #[test]
    fn tla_next_construction_and_metadata() {
        let n = TlaNext::new(vec![make_action("A", "x"), make_action("B", "y")]);
        assert_eq!(n.dialect(), "tla");
        assert_eq!(n.op_name(), "tla.next");
        assert_eq!(n.kind(), OpKind::StateTransform);
        assert_eq!(n.actions.len(), 2);
        assert_eq!(n.actions[0].op_name(), "tla.action");
        assert_eq!(n.actions[1].op_name(), "tla.action");
    }

    #[test]
    fn tla_next_verify_accepts_nonempty_action_list() {
        let n = TlaNext::new(vec![make_action("A", "x"), make_action("B", "y")]);
        n.verify().expect("non-empty list of actions should verify");
    }

    #[test]
    fn tla_next_verify_rejects_empty_action_list() {
        let n = TlaNext::new(vec![]);
        let err = n.verify().expect_err("empty action list must fail verify");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.next");
                assert!(message.contains("non-empty"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_next_verify_rejects_element_wrong_kind() {
        // An Expression-kinded element is not a valid action — actions must
        // be StateTransform-kinded. TlaSetRef is Expression-kinded.
        let n = TlaNext::new(vec![make_action("A", "x"), Box::new(TlaSetRef::new("S"))]);
        let err = n
            .verify()
            .expect_err("Expression-kind element must fail for tla.next");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.next");
                assert!(message.contains("StateTransform"));
                // Index reported in the failure message for debugging.
                assert!(message.contains("action[1]"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_next_verify_rejects_element_cross_dialect() {
        use crate::verif::{BfsKind, VerifBfsStep};
        let n = TlaNext::new(vec![
            make_action("A", "x"),
            Box::new(VerifBfsStep {
                kind: BfsKind::Expand,
                action_id: 0,
                ..Default::default()
            }),
        ]);
        let err = n
            .verify()
            .expect_err("cross-dialect element must fail for tla.next");
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.next");
                assert!(message.contains("action[1]"));
                assert!(message.contains("tla"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_next_verify_propagates_element_failure() {
        // First action is fine; second carries an empty name which fails
        // its own verify. TlaNext must surface the inner report unchanged.
        let bad_body = TlaAssign::new(Box::new(TlaVarRef::new("y")), Box::new(TlaSetRef::new("e")));
        let bad_action: Box<dyn DialectOp> = Box::new(TlaAction::new("", Box::new(bad_body)));
        let n = TlaNext::new(vec![make_action("A", "x"), bad_action]);
        let err = n
            .verify()
            .expect_err("inner empty-name action must fail verify");
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "tla");
                // Inner action reports itself, not tla.next.
                assert_eq!(op, "tla.action");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn tla_next_pretty_print_is_stable() {
        let n = TlaNext::new(vec![make_action("A", "x"), make_action("B", "y")]);
        // Comma-separated children by their op_name, wrapped in `Next(...)`.
        assert_eq!(format!("{n}"), "Next(tla.action, tla.action)");
    }

    #[test]
    fn tla_next_pretty_print_single_action() {
        let n = TlaNext::new(vec![make_action("A", "x")]);
        // No trailing comma on a single-element list.
        assert_eq!(format!("{n}"), "Next(tla.action)");
    }

    #[test]
    fn tla_next_lowering_is_deferred() {
        let n = TlaNext::new(vec![make_action("A", "x")]);
        let err = n.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.next"
            }
        ));
    }

    // -------------------------------------------------------------------------
    // Dialect registration covers all Wave 10 additions.
    //
    // `tla.action` and `tla.next` were already in the `OP_NAMES` / dialect
    // registration (as stubs) before Wave 10 graduated them to compound
    // ops, so the registration check here is unchanged in spirit — it
    // still pins the mnemonics, but now they point at real compound ops
    // rather than namespace-pin stubs.
    // -------------------------------------------------------------------------

    #[test]
    fn tla_dialect_lists_wave10_ops() {
        let d = TlaDialect;
        let names = d.op_names();
        assert!(names.contains(&"tla.action"));
        assert!(names.contains(&"tla.next"));
    }

    // -------------------------------------------------------------------------
    // Wave 11 — quantifier + set-comprehension ops.
    //
    // The 5 new ops (`tla.exists`, `tla.forall`, `tla.choose`,
    // `tla.set_builder`, `tla.set_map`) share a three-operand shape: a
    // variable binder that must be `tla.var_ref`, a domain expression, and a
    // body/expr expression. All route through `verify_quantifier_operand`.
    //
    // Test rubric (matches the Wave 9 split between explicit per-op tests for
    // facets that differ per op, and parameterized tests for facets where all
    // ops are structurally identical):
    //
    //   - One *explicit* `tla_<op>_construction_and_metadata` per op (5) —
    //     pins struct name, mnemonic, kind, operand op_names.
    //   - One *explicit* `tla_<op>_verify_accepts_well_typed_operands` per op
    //     (5) — exercises the verify path on the specific type.
    //   - One *explicit* `tla_<op>_pretty_print_is_stable` per op (5) — pins
    //     each op's Display rendering (the forms differ: `\E`, `\A`, CHOOSE,
    //     `{ v \in S : P }`, `{ f(v) : v \in S }`).
    //   - One *explicit* `tla_<op>_lowering_is_deferred` per op (5) — pins
    //     the NotImplemented mnemonic per op.
    //   - A *parameterized* `wave11_verify_rejects_non_var_ref` (1) — covers
    //     all 5 ops' reject-non-var-ref facet in a loop keyed on the
    //     dyn-constructor; asserts fire the parent mnemonic so a drift in one
    //     op's wiring localizes.
    //   - A *parameterized* `wave11_verify_rejects_domain_wrong_kind` (1) —
    //     covers all 5 ops' reject-Invariant-domain facet.
    //   - A *parameterized* `wave11_verify_rejects_body_wrong_kind` (1) —
    //     covers all 5 ops' reject-Invariant-body/expr facet. TlaSetMap's
    //     body slot uses the `expr` tag — that is asserted per-op by the
    //     side-tag entry in the op table so the loop catches drift there.
    //   - A *parameterized* `wave11_verify_rejects_cross_dialect_domain` (1)
    //     — cross-dialect domain operand.
    //   - A *parameterized* `wave11_verify_propagates_operand_failure` (1) —
    //     recursive verify propagation (inner TlaVarRef with an empty name
    //     used as the variable operand fails its own verify).
    //   - A *parameterized* `wave11_verify_rejects_non_tla_var_ref_dialect`
    //     (1) — var operand whose dialect is not `tla`.
    //   - One *consolidated* `tla_dialect_lists_wave11_ops` (1) — pins all 5
    //     mnemonics in the dialect op_names() registration.
    //
    // That yields 20 explicit + 6 parameterized + 1 registration = 27 new
    // tests (<<36 but covers every rubric facet per op and doesn't inflate
    // LOC with near-duplicate verify-reject tests — matches Wave 9's
    // approach). Every op still exercises all 7 facets from the task brief:
    // construction, verify-accept, reject-non-var-ref, reject-domain-kind,
    // reject-body-kind, pretty-print, deferred-lowering (each facet covered
    // either explicitly or via a loop keyed on the op's own mnemonic).
    // -------------------------------------------------------------------------

    // --- Parameterized op table ---------------------------------------------
    //
    // Each entry carries the parent mnemonic, the body-side tag (`body` or
    // `expr`), and a 3-arg type-erased constructor. Both tags appear so
    // `wave11_verify_rejects_body_wrong_kind` can assert the right side tag
    // for the rejected-operand message per op.

    type Wave11Ctor =
        fn(Box<dyn DialectOp>, Box<dyn DialectOp>, Box<dyn DialectOp>) -> Box<dyn DialectOp>;

    fn wave11_ops() -> Vec<(&'static str, &'static str, Wave11Ctor)> {
        vec![
            ("tla.exists", "body", |v, d, b| {
                Box::new(TlaExists::new(v, d, b))
            }),
            ("tla.forall", "body", |v, d, b| {
                Box::new(TlaForall::new(v, d, b))
            }),
            ("tla.choose", "body", |v, d, b| {
                Box::new(TlaChoose::new(v, d, b))
            }),
            ("tla.set_builder", "body", |v, d, b| {
                Box::new(TlaSetBuilder::new(v, d, b))
            }),
            ("tla.set_map", "expr", |v, d, e| {
                Box::new(TlaSetMap::new(v, d, e))
            }),
        ]
    }

    // --- Per-op construction + metadata (5 tests) ---------------------------

    #[test]
    fn tla_exists_construction_and_metadata() {
        let op = TlaExists::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.exists");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.var.op_name(), "tla.var_ref");
        assert_eq!(op.domain.op_name(), "tla.set_ref");
        assert_eq!(op.body.op_name(), "tla.set_ref");
    }

    #[test]
    fn tla_forall_construction_and_metadata() {
        let op = TlaForall::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.forall");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.var.op_name(), "tla.var_ref");
        assert_eq!(op.domain.op_name(), "tla.set_ref");
        assert_eq!(op.body.op_name(), "tla.set_ref");
    }

    #[test]
    fn tla_choose_construction_and_metadata() {
        let op = TlaChoose::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.choose");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.var.op_name(), "tla.var_ref");
        assert_eq!(op.domain.op_name(), "tla.set_ref");
        assert_eq!(op.body.op_name(), "tla.set_ref");
    }

    #[test]
    fn tla_set_builder_construction_and_metadata() {
        let op = TlaSetBuilder::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.set_builder");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.var.op_name(), "tla.var_ref");
        assert_eq!(op.domain.op_name(), "tla.set_ref");
        assert_eq!(op.body.op_name(), "tla.set_ref");
    }

    #[test]
    fn tla_set_map_construction_and_metadata() {
        let op = TlaSetMap::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("F")),
        );
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.set_map");
        assert_eq!(op.kind(), OpKind::Expression);
        // Distinct field name — `expr` rather than `body`.
        assert_eq!(op.var.op_name(), "tla.var_ref");
        assert_eq!(op.domain.op_name(), "tla.set_ref");
        assert_eq!(op.expr.op_name(), "tla.set_ref");
    }

    // --- Per-op verify-accept (5 tests) -------------------------------------

    #[test]
    fn tla_exists_verify_accepts_well_typed_operands() {
        let op = TlaExists::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        op.verify()
            .expect("var_ref + two expression operands should verify");
    }

    #[test]
    fn tla_forall_verify_accepts_well_typed_operands() {
        let op = TlaForall::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        op.verify()
            .expect("var_ref + two expression operands should verify");
    }

    #[test]
    fn tla_choose_verify_accepts_well_typed_operands() {
        let op = TlaChoose::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        op.verify()
            .expect("var_ref + two expression operands should verify");
    }

    #[test]
    fn tla_set_builder_verify_accepts_well_typed_operands() {
        let op = TlaSetBuilder::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        op.verify()
            .expect("var_ref + two expression operands should verify");
    }

    #[test]
    fn tla_set_map_verify_accepts_well_typed_operands() {
        let op = TlaSetMap::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("F")),
        );
        op.verify()
            .expect("var_ref + two expression operands should verify");
    }

    // --- Per-op pretty-print (5 tests) --------------------------------------
    //
    // Explicit per-op because each op's Display rendering differs in surface
    // form — a loop would obscure which op produces which shape.

    #[test]
    fn tla_exists_pretty_print_is_stable() {
        let op = TlaExists::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(
            format!("{op}"),
            "(\\E tla.var_ref \\in tla.set_ref : tla.set_ref)"
        );
    }

    #[test]
    fn tla_forall_pretty_print_is_stable() {
        let op = TlaForall::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(
            format!("{op}"),
            "(\\A tla.var_ref \\in tla.set_ref : tla.set_ref)"
        );
    }

    #[test]
    fn tla_choose_pretty_print_is_stable() {
        let op = TlaChoose::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(
            format!("{op}"),
            "(CHOOSE tla.var_ref \\in tla.set_ref : tla.set_ref)"
        );
    }

    #[test]
    fn tla_set_builder_pretty_print_is_stable() {
        let op = TlaSetBuilder::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        assert_eq!(
            format!("{op}"),
            "{ tla.var_ref \\in tla.set_ref : tla.set_ref }"
        );
    }

    #[test]
    fn tla_set_map_pretty_print_is_stable() {
        // Expression-first surface form: `{ f(v) : v \in S }`.
        let op = TlaSetMap::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("F")),
        );
        assert_eq!(
            format!("{op}"),
            "{ tla.set_ref : tla.var_ref \\in tla.set_ref }"
        );
    }

    // --- Per-op deferred lowering (5 tests) ---------------------------------

    #[test]
    fn tla_exists_lowering_is_deferred() {
        let op = TlaExists::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        let err = op.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.exists"
            }
        ));
    }

    #[test]
    fn tla_forall_lowering_is_deferred() {
        let op = TlaForall::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        let err = op.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.forall"
            }
        ));
    }

    #[test]
    fn tla_choose_lowering_is_deferred() {
        let op = TlaChoose::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        let err = op.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.choose"
            }
        ));
    }

    #[test]
    fn tla_set_builder_lowering_is_deferred() {
        let op = TlaSetBuilder::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("P")),
        );
        let err = op.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.set_builder"
            }
        ));
    }

    #[test]
    fn tla_set_map_lowering_is_deferred() {
        let op = TlaSetMap::new(
            Box::new(TlaVarRef::new("v")),
            Box::new(TlaSetRef::new("S")),
            Box::new(TlaSetRef::new("F")),
        );
        let err = op.lower().expect_err("lowering must be deferred today");
        assert!(matches!(
            err,
            DialectError::NotImplemented {
                dialect: "tla",
                op: "tla.set_map"
            }
        ));
    }

    // --- Parameterized verify-reject tests (6) ------------------------------

    #[test]
    fn wave11_verify_rejects_non_var_ref() {
        // The variable operand must specifically be `tla.var_ref`. A
        // non-var_ref `tla::` op (e.g. `tla.set_ref`) must be rejected even
        // though it's in the right dialect.
        for (mnemonic, _body_side, ctor) in wave11_ops() {
            let op = ctor(
                Box::new(TlaSetRef::new("not_a_var")),
                Box::new(TlaSetRef::new("S")),
                Box::new(TlaSetRef::new("P")),
            );
            let err = op
                .verify()
                .err()
                .unwrap_or_else(|| panic!("{mnemonic}: non-var_ref var must fail"));
            match err {
                DialectError::VerifyFailed {
                    dialect,
                    op,
                    message,
                } => {
                    assert_eq!(dialect, "tla", "{mnemonic}: dialect tag");
                    assert_eq!(op, mnemonic, "{mnemonic}: parent mnemonic");
                    assert!(
                        message.contains("tla.var_ref"),
                        "{mnemonic}: message must mention required var_ref, got `{message}`"
                    );
                    assert!(
                        message.contains("tla.set_ref"),
                        "{mnemonic}: message must mention actual op_name, got `{message}`"
                    );
                }
                other => panic!("{mnemonic}: unexpected error: {other:?}"),
            }
        }
    }

    #[test]
    fn wave11_verify_rejects_domain_wrong_kind() {
        // Domain operand must be OpKind::Expression. TlaInvariant is
        // OpKind::Invariant and must be rejected, with the parent mnemonic
        // in the error and the side tag `domain` in the message.
        for (mnemonic, _body_side, ctor) in wave11_ops() {
            let op = ctor(
                Box::new(TlaVarRef::new("v")),
                Box::<TlaInvariant>::default(),
                Box::new(TlaSetRef::new("P")),
            );
            let err = op
                .verify()
                .err()
                .unwrap_or_else(|| panic!("{mnemonic}: Invariant-kind domain must fail"));
            match err {
                DialectError::VerifyFailed {
                    dialect,
                    op,
                    message,
                } => {
                    assert_eq!(dialect, "tla", "{mnemonic}: dialect tag");
                    assert_eq!(op, mnemonic, "{mnemonic}: parent mnemonic");
                    assert!(
                        message.contains("domain"),
                        "{mnemonic}: message must mention `domain` side tag, got `{message}`"
                    );
                    assert!(
                        message.contains("Expression"),
                        "{mnemonic}: message must mention required kind, got `{message}`"
                    );
                }
                other => panic!("{mnemonic}: unexpected error: {other:?}"),
            }
        }
    }

    #[test]
    fn wave11_verify_rejects_body_wrong_kind() {
        // Body (or expr) operand must be OpKind::Expression. The side tag
        // asserted here differs between ops: `body` for exists/forall/choose/
        // set_builder, `expr` for set_map. The op table carries the expected
        // side tag so a loop covers both.
        for (mnemonic, body_side, ctor) in wave11_ops() {
            let op = ctor(
                Box::new(TlaVarRef::new("v")),
                Box::new(TlaSetRef::new("S")),
                Box::<TlaInvariant>::default(),
            );
            let err = op
                .verify()
                .err()
                .unwrap_or_else(|| panic!("{mnemonic}: Invariant-kind body must fail"));
            match err {
                DialectError::VerifyFailed {
                    dialect,
                    op,
                    message,
                } => {
                    assert_eq!(dialect, "tla", "{mnemonic}: dialect tag");
                    assert_eq!(op, mnemonic, "{mnemonic}: parent mnemonic");
                    assert!(
                        message.contains(body_side),
                        "{mnemonic}: message must mention `{body_side}` side tag, got `{message}`"
                    );
                    assert!(
                        message.contains("Expression"),
                        "{mnemonic}: message must mention required kind, got `{message}`"
                    );
                }
                other => panic!("{mnemonic}: unexpected error: {other:?}"),
            }
        }
    }

    #[test]
    fn wave11_verify_rejects_cross_dialect_domain() {
        use crate::verif::{BfsKind, VerifBfsStep};
        for (mnemonic, _body_side, ctor) in wave11_ops() {
            let op = ctor(
                Box::new(TlaVarRef::new("v")),
                Box::new(VerifBfsStep {
                    kind: BfsKind::Expand,
                    action_id: 0,
                    ..Default::default()
                }),
                Box::new(TlaSetRef::new("P")),
            );
            let err = op
                .verify()
                .err()
                .unwrap_or_else(|| panic!("{mnemonic}: cross-dialect domain must fail"));
            match err {
                DialectError::VerifyFailed {
                    dialect,
                    op,
                    message,
                } => {
                    assert_eq!(dialect, "tla", "{mnemonic}: dialect tag");
                    assert_eq!(op, mnemonic, "{mnemonic}: parent mnemonic");
                    assert!(
                        message.contains("domain"),
                        "{mnemonic}: message must mention `domain` side tag, got `{message}`"
                    );
                    assert!(
                        message.contains("tla"),
                        "{mnemonic}: message must mention required dialect, got `{message}`"
                    );
                }
                other => panic!("{mnemonic}: unexpected error: {other:?}"),
            }
        }
    }

    #[test]
    fn wave11_verify_rejects_non_tla_var_ref_dialect() {
        // A `tla.var_ref`-lookalike from a different dialect must be
        // rejected by the dialect check before the op_name check. Using a
        // verif:: op here exercises the dialect-mismatch path in
        // `verify_quantifier_operand` specifically.
        use crate::verif::{BfsKind, VerifBfsStep};
        for (mnemonic, _body_side, ctor) in wave11_ops() {
            let op = ctor(
                Box::new(VerifBfsStep {
                    kind: BfsKind::Expand,
                    action_id: 0,
                    ..Default::default()
                }),
                Box::new(TlaSetRef::new("S")),
                Box::new(TlaSetRef::new("P")),
            );
            let err = op
                .verify()
                .err()
                .unwrap_or_else(|| panic!("{mnemonic}: cross-dialect var must fail"));
            match err {
                DialectError::VerifyFailed {
                    dialect,
                    op,
                    message,
                } => {
                    assert_eq!(dialect, "tla", "{mnemonic}: dialect tag");
                    assert_eq!(op, mnemonic, "{mnemonic}: parent mnemonic");
                    assert!(
                        message.contains("var"),
                        "{mnemonic}: message must mention `var` side tag, got `{message}`"
                    );
                    assert!(
                        message.contains("tla"),
                        "{mnemonic}: message must mention required dialect, got `{message}`"
                    );
                }
                other => panic!("{mnemonic}: unexpected error: {other:?}"),
            }
        }
    }

    #[test]
    fn wave11_verify_propagates_operand_failure() {
        // An empty-name `TlaVarRef` as the variable operand passes the
        // dialect + op_name checks but fails its own `verify()`. The parent
        // op must surface that inner failure unchanged (inner op reports
        // itself — "tla.var_ref" — not the parent mnemonic).
        for (mnemonic, _body_side, ctor) in wave11_ops() {
            let op = ctor(
                Box::new(TlaVarRef::new("")),
                Box::new(TlaSetRef::new("S")),
                Box::new(TlaSetRef::new("P")),
            );
            let err = op
                .verify()
                .err()
                .unwrap_or_else(|| panic!("{mnemonic}: empty var name must fail"));
            match err {
                DialectError::VerifyFailed { dialect, op, .. } => {
                    assert_eq!(dialect, "tla", "{mnemonic}: inner dialect tag");
                    assert_eq!(
                        op, "tla.var_ref",
                        "{mnemonic}: inner must surface its own mnemonic"
                    );
                }
                other => panic!("{mnemonic}: unexpected error: {other:?}"),
            }
        }
    }

    // --- Dialect registration pins all 5 new mnemonics (1 test) -------------

    #[test]
    fn tla_dialect_lists_wave11_ops() {
        let d = TlaDialect;
        let names = d.op_names();
        assert!(names.contains(&"tla.exists"));
        assert!(names.contains(&"tla.forall"));
        assert!(names.contains(&"tla.choose"));
        assert!(names.contains(&"tla.set_builder"));
        assert!(names.contains(&"tla.set_map"));
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3f tests (#4286) — TlaActionEval + TlaEnabled surface ops with
    // verified two-step lowering through verif.action_eval / verif.enabled_check
    // to the terminal LlvmLeaf variants.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3f_tla_action_eval_reports_dialect_and_mnemonic() {
        let op = TlaActionEval::new("Next", 3);
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.action_eval");
        assert_eq!(op.kind(), OpKind::StateTransform);
        assert_eq!(op.name, "Next");
        assert_eq!(op.action_id, 3);
        assert_eq!(op.source_slot, 0);
        assert_eq!(op.depth, 0);
        assert_eq!(op.worker_id, 0);
    }

    #[test]
    fn wave14_tl3f_tla_action_eval_rejects_empty_name() {
        let op = TlaActionEval::new("", 1);
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.action_eval");
                assert!(message.contains("name"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_tla_action_eval_rejects_zero_action_id() {
        let op = TlaActionEval::new("Next", 0);
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.action_eval");
                assert!(message.contains("action_id"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_tla_action_eval_new_on_source_preserves_fields() {
        let op = TlaActionEval::new_on_source("Next", 5, 42);
        assert_eq!(op.name, "Next");
        assert_eq!(op.action_id, 5);
        assert_eq!(op.source_slot, 42);
        assert_eq!(op.depth, 0);
        assert_eq!(op.worker_id, 0);
        op.verify().expect("valid action_eval must verify");
    }

    #[test]
    fn wave14_tl3f_tla_action_eval_new_at_depth_preserves_fields() {
        let op = TlaActionEval::new_at_depth("Next", 5, 42, 7, 3);
        assert_eq!(op.name, "Next");
        assert_eq!(op.action_id, 5);
        assert_eq!(op.source_slot, 42);
        assert_eq!(op.depth, 7);
        assert_eq!(op.worker_id, 3);
        op.verify()
            .expect("fully-specified action_eval must verify");
    }

    #[test]
    fn wave14_tl3f_tla_action_eval_lowering_threads_fields_to_leaf() {
        // Two-step lowering: tla.action_eval -> verif.action_eval ->
        // LlvmLeaf::ActionEval. All four numeric fields survive.
        let tla_op = TlaActionEval::new_at_depth("Send", 7, 13, 25, 2);
        let lowered = tla_op.lower().unwrap();
        let verif_op = match lowered {
            Lowered::Ops(mut ops) => {
                assert_eq!(ops.len(), 1);
                ops.pop().unwrap()
            }
            Lowered::Leaf(_) => panic!("expected verif ops, got leaf"),
        };
        assert_eq!(verif_op.op_name(), "verif.action_eval");
        match verif_op.lower().unwrap() {
            Lowered::Leaf(crate::LlvmLeaf::ActionEval {
                action_id,
                source_slot,
                depth,
                worker_id,
            }) => {
                assert_eq!(action_id, 7);
                assert_eq!(source_slot, 13);
                assert_eq!(depth, 25);
                assert_eq!(worker_id, 2);
            }
            other => panic!("expected ActionEval leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_tla_enabled_reports_dialect_and_mnemonic() {
        let op = TlaEnabled::new("Send", 3);
        assert_eq!(op.dialect(), "tla");
        assert_eq!(op.op_name(), "tla.enabled");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.name, "Send");
        assert_eq!(op.action_id, 3);
        assert_eq!(op.state_slot, 0);
        assert_eq!(op.depth, 0);
    }

    #[test]
    fn wave14_tl3f_tla_enabled_rejects_empty_name() {
        let op = TlaEnabled::new("", 1);
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.enabled");
                assert!(message.contains("name"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_tla_enabled_rejects_zero_action_id() {
        let op = TlaEnabled::new("Send", 0);
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "tla");
                assert_eq!(op, "tla.enabled");
                assert!(message.contains("action_id"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_tla_enabled_new_on_state_preserves_fields() {
        let op = TlaEnabled::new_on_state("Send", 5, 42);
        assert_eq!(op.name, "Send");
        assert_eq!(op.action_id, 5);
        assert_eq!(op.state_slot, 42);
        assert_eq!(op.depth, 0);
        op.verify().expect("valid enabled must verify");
    }

    #[test]
    fn wave14_tl3f_tla_enabled_new_at_depth_preserves_fields() {
        let op = TlaEnabled::new_at_depth("Send", 5, 42, 7);
        assert_eq!(op.name, "Send");
        assert_eq!(op.action_id, 5);
        assert_eq!(op.state_slot, 42);
        assert_eq!(op.depth, 7);
        op.verify().expect("fully-specified enabled must verify");
    }

    #[test]
    fn wave14_tl3f_tla_enabled_lowering_threads_fields_to_leaf() {
        // Two-step lowering: tla.enabled -> verif.enabled_check ->
        // LlvmLeaf::EnabledCheck. All three numeric fields survive.
        let tla_op = TlaEnabled::new_at_depth("Ack", 4, 88, 2);
        let lowered = tla_op.lower().unwrap();
        let verif_op = match lowered {
            Lowered::Ops(mut ops) => {
                assert_eq!(ops.len(), 1);
                ops.pop().unwrap()
            }
            Lowered::Leaf(_) => panic!("expected verif ops, got leaf"),
        };
        assert_eq!(verif_op.op_name(), "verif.enabled_check");
        match verif_op.lower().unwrap() {
            Lowered::Leaf(crate::LlvmLeaf::EnabledCheck {
                action_id,
                state_slot,
                depth,
            }) => {
                assert_eq!(action_id, 4);
                assert_eq!(state_slot, 88);
                assert_eq!(depth, 2);
            }
            other => panic!("expected EnabledCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_tla_dialect_lists_new_tl3f_ops() {
        let d = TlaDialect;
        let names = d.op_names();
        assert!(names.contains(&"tla.action_eval"));
        assert!(names.contains(&"tla.enabled"));
    }

    #[test]
    fn wave14_tl3f_tla_action_eval_and_enabled_are_send_and_sync() {
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(TlaActionEval::new("N", 1));
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(TlaEnabled::new("N", 1));
    }
}
