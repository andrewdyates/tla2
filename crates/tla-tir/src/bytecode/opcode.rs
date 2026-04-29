// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode instruction set for TLA+ evaluation.
//!
//! Register-based instruction set covering non-temporal TLA+ operations.
//! Each instruction is a fixed-size enum variant — no variable-length encoding.
//! This keeps dispatch simple and makes the bytecode suitable for Cranelift JIT
//! lowering (Phase B2).

pub use super::opcode_support::{
    BuiltinOp, ConstIdx, FieldIdx, JumpOffset, OpIdx, Register, VarIdx,
};

/// Bytecode instruction for the TLA+ VM.
///
/// Each variant is a single operation. The VM executes instructions linearly
/// unless a jump/branch redirects the program counter.
///
/// Register conventions:
/// - `rd`: destination register
/// - `r1`, `r2`: source registers
/// - `rs`: single source register
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
    // =================================================================
    // Value Loading
    // =================================================================
    /// Load an immediate i64 constant into a register.
    /// Covers the common case of small integer literals.
    LoadImm { rd: Register, value: i64 },

    /// Load a boolean constant.
    LoadBool { rd: Register, value: bool },

    /// Load a constant from the constant pool (for compound values, big
    /// integers, strings, etc.).
    LoadConst { rd: Register, idx: ConstIdx },

    /// Load a state variable by its pre-computed index.
    LoadVar { rd: Register, var_idx: VarIdx },

    /// Load a primed state variable (from the successor state).
    LoadPrime { rd: Register, var_idx: VarIdx },

    /// Store a value into the working successor state.
    StoreVar { var_idx: VarIdx, rs: Register },

    /// Copy a register value to another register.
    Move { rd: Register, rs: Register },

    // =================================================================
    // Integer Arithmetic (i64 fast path)
    // =================================================================
    /// rd = r1 + r2 (integer addition).
    AddInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 - r2 (integer subtraction).
    SubInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 * r2 (integer multiplication).
    MulInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 / r2 (real division — TLA+ `/` is real, but in model checking
    /// context usually integer. Produces an error if not exact.)
    DivInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 \div r2 (Euclidean integer division, TLC semantics).
    IntDiv {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 % r2 (Euclidean modulus, TLC semantics).
    ModInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = -rs (integer negation).
    NegInt { rd: Register, rs: Register },

    /// rd = r1 ^ r2 (integer exponentiation).
    PowInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    // =================================================================
    // Comparison
    // =================================================================
    /// rd = (r1 = r2), polymorphic equality.
    Eq {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = (r1 /= r2), polymorphic inequality.
    Neq {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = (r1 < r2), integer comparison.
    LtInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = (r1 <= r2), integer comparison.
    LeInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = (r1 > r2), integer comparison.
    GtInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = (r1 >= r2), integer comparison.
    GeInt {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    // =================================================================
    // Boolean Operations
    // =================================================================
    /// rd = r1 /\ r2 (conjunction). NOT short-circuit — use JumpFalse for
    /// short-circuit evaluation.
    And {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 \/ r2 (disjunction). NOT short-circuit.
    Or {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = ~rs (boolean negation).
    Not { rd: Register, rs: Register },

    /// rd = (r1 => r2) (logical implication).
    Implies {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = (r1 <=> r2) (logical equivalence).
    Equiv {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    // =================================================================
    // Control Flow
    // =================================================================
    /// Unconditional jump.
    Jump { offset: JumpOffset },

    /// Jump if register is TRUE.
    JumpTrue { rs: Register, offset: JumpOffset },

    /// Jump if register is FALSE.
    JumpFalse { rs: Register, offset: JumpOffset },

    /// Call a user-defined operator. `argc` arguments are in registers
    /// starting at `args_start`. Result goes to `rd`.
    Call {
        rd: Register,
        op_idx: OpIdx,
        args_start: Register,
        argc: u8,
    },

    /// Apply a runtime value as an operator/function.
    ///
    /// Used for higher-order `Apply` where the callee is not a statically
    /// resolved operator name. Closures use the full `argc` argument vector;
    /// ordinary function-like values accept exactly one argument.
    ValueApply {
        rd: Register,
        func: Register,
        args_start: Register,
        argc: u8,
    },

    /// Return from the current function, yielding the value in `rs`.
    Ret { rs: Register },

    // =================================================================
    // Set Operations
    // =================================================================
    /// Build a set from `count` consecutive registers starting at `start`.
    SetEnum {
        rd: Register,
        start: Register,
        count: u8,
    },

    /// rd = (r_elem \in r_set), set membership.
    SetIn {
        rd: Register,
        elem: Register,
        set: Register,
    },

    /// rd = r1 \union r2.
    SetUnion {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 \intersect r2.
    SetIntersect {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = r1 \ r2 (set difference).
    SetDiff {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = (r1 \subseteq r2).
    Subseteq {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// rd = SUBSET(rs) (powerset).
    Powerset { rd: Register, rs: Register },

    /// rd = UNION(rs) (big union / flatten).
    BigUnion { rd: Register, rs: Register },

    /// rd = KSubset(base, k) — k-element subsets of base set.
    /// Constructs a lazy KSubsetValue representing C(n,k) subsets without
    /// enumerating all 2^n subsets of the powerset. Part of #3907.
    KSubset {
        rd: Register,
        base: Register,
        k: Register,
    },

    /// rd = lo..hi (integer interval set).
    Range {
        rd: Register,
        lo: Register,
        hi: Register,
    },

    // =================================================================
    // Quantifiers
    //
    // Quantifier loops use a two-instruction pattern:
    //   QuantBegin: initialize iterator, jump to end if domain is empty
    //   QuantNext: advance iterator, jump back to body or fall through
    // =================================================================
    /// Begin a FORALL quantifier over the domain in `r_domain`.
    /// `r_binding` receives each element. If domain is empty, jumps to
    /// `loop_end` (offset from this instruction).
    ForallBegin {
        rd: Register,
        r_binding: Register,
        r_domain: Register,
        loop_end: JumpOffset,
    },

    /// Advance the FORALL iterator. If the body produced FALSE, short-circuit
    /// to the end. Otherwise, bind the next element and jump to `loop_begin`.
    ForallNext {
        rd: Register,
        r_binding: Register,
        r_body: Register,
        loop_begin: JumpOffset,
    },

    /// Begin an EXISTS quantifier (analogous to ForallBegin).
    ExistsBegin {
        rd: Register,
        r_binding: Register,
        r_domain: Register,
        loop_end: JumpOffset,
    },

    /// Advance the EXISTS iterator. If the body produced TRUE, short-circuit
    /// to the end. Otherwise, bind next element and jump to `loop_begin`.
    ExistsNext {
        rd: Register,
        r_binding: Register,
        r_body: Register,
        loop_begin: JumpOffset,
    },

    // =================================================================
    // Records / Functions / Tuples
    // =================================================================
    /// Build a record from `count` (field_id, value) pairs.
    /// Field IDs come from the constant pool, values from consecutive registers.
    RecordNew {
        rd: Register,
        fields_start: ConstIdx,
        values_start: Register,
        count: u8,
    },

    /// rd = rs.field (record field access by pre-interned field ID).
    RecordGet {
        rd: Register,
        rs: Register,
        field_idx: FieldIdx,
    },

    /// rd = rs[r_arg] (function application).
    FuncApply {
        rd: Register,
        func: Register,
        arg: Register,
    },

    /// rd = DOMAIN(rs).
    Domain { rd: Register, rs: Register },

    /// rd = [rs EXCEPT ![r_path] = r_val].
    /// Single-element EXCEPT (most common case).
    FuncExcept {
        rd: Register,
        func: Register,
        path: Register,
        val: Register,
    },

    /// Build a tuple from `count` consecutive registers starting at `start`.
    TupleNew {
        rd: Register,
        start: Register,
        count: u8,
    },

    /// rd = rs[idx] (tuple element access, 1-indexed per TLA+ convention).
    TupleGet {
        rd: Register,
        rs: Register,
        idx: u16,
    },

    /// Build a function `[x \in domain |-> body]`.
    /// `r_domain` has the domain set. For each element, bind to `r_binding`,
    /// evaluate body, collect into function.
    FuncDef {
        rd: Register,
        r_domain: Register,
        r_binding: Register,
    },

    /// Build a function set `[S -> T]`.
    FuncSet {
        rd: Register,
        domain: Register,
        range: Register,
    },

    /// Build a record set `[f1: S1, f2: S2, ...]`.
    RecordSet {
        rd: Register,
        fields_start: ConstIdx,
        values_start: Register,
        count: u8,
    },

    /// Build a cross product `S1 \X S2 \X ...`.
    Times {
        rd: Register,
        start: Register,
        count: u8,
    },

    // =================================================================
    // Sequences
    // =================================================================
    /// Build a sequence from `count` consecutive registers.
    SeqNew {
        rd: Register,
        start: Register,
        count: u8,
    },

    // =================================================================
    // String Operations
    // =================================================================
    /// rd = r1 \o r2 (string concatenation).
    StrConcat {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    // =================================================================
    // Special
    // =================================================================
    /// rd = IF cond THEN rs ELSE rd (conditional move).
    /// Used for simple IF-THEN-ELSE without control flow.
    CondMove {
        rd: Register,
        cond: Register,
        rs: Register,
    },

    /// UNCHANGED <<v1, v2, ...>>: compare primed vars equal unprimed.
    /// `start` and `count` refer to VarIdx entries in the constant pool.
    /// Writes `TRUE` to `rd` iff all listed vars match between state and next_state.
    Unchanged {
        rd: Register,
        start: ConstIdx,
        count: u8,
    },

    /// Begin a CHOOSE quantifier: iterate `r_domain`, evaluate predicate body,
    /// return first element where predicate is TRUE.
    /// If domain is empty, halts (TLA+ CHOOSE with no match is a runtime error).
    ChooseBegin {
        rd: Register,
        r_binding: Register,
        r_domain: Register,
        loop_end: JumpOffset,
    },

    /// Advance the CHOOSE iterator. If `r_body` is TRUE, set `rd = r_binding`
    /// and exit the loop. Otherwise, advance to next element. If domain is
    /// exhausted without finding a match, halts.
    ChooseNext {
        rd: Register,
        r_binding: Register,
        r_body: Register,
        loop_begin: JumpOffset,
    },

    /// Set comprehension: `{body : x \in S}`.
    /// Iterates over `r_domain`, binds to `r_binding`, evaluates body (in
    /// following instructions up to a SetBuilderEnd), collects into set.
    SetBuilderBegin {
        rd: Register,
        r_binding: Register,
        r_domain: Register,
        loop_end: JumpOffset,
    },

    /// Set filter: `{x \in S : P(x)}`.
    /// Iterates over `r_domain`, binds to `r_binding`, evaluates predicate
    /// body, collects elements where predicate is TRUE.
    SetFilterBegin {
        rd: Register,
        r_binding: Register,
        r_domain: Register,
        loop_end: JumpOffset,
    },

    /// Function definition body loop: for each domain element, evaluate body
    /// and collect (key, value) pair.
    FuncDefBegin {
        rd: Register,
        r_binding: Register,
        r_domain: Register,
        loop_end: JumpOffset,
    },

    /// End of a quantifier/builder/filter loop body. Advances the iterator
    /// and jumps back to the loop start if more elements remain.
    LoopNext {
        r_binding: Register,
        r_body: Register,
        loop_begin: JumpOffset,
    },

    /// Set VM prime mode: when enabled, `LoadVar` reads from next-state
    /// instead of current state. Used by the UNCHANGED general fallback to
    /// compile `expr = expr'` where `expr` may contain Call opcodes that
    /// jump to pre-compiled functions (which use LoadVar, not LoadPrime).
    SetPrimeMode { enable: bool },

    /// Build a closure value from a template, capturing runtime register values.
    ///
    /// `template_idx` points to the template `Value::Closure` in the constant
    /// pool. The next `capture_count` constant pool entries (starting at
    /// `template_idx + 1`) are `Value::Str` capture-name keys. The corresponding
    /// values come from consecutive registers starting at `captures_start`.
    /// The resulting closure's `env` maps each capture name to its register value.
    MakeClosure {
        rd: Register,
        template_idx: ConstIdx,
        captures_start: Register,
        capture_count: u8,
    },

    /// Call an external (non-compiled) operator by name, falling back to
    /// the TIR tree-walker at runtime.
    ///
    /// Used for INSTANCE-imported operators that cannot be pre-compiled
    /// into bytecode. `name_idx` points to a `Value::String` in the
    /// constant pool holding the operator name. `args_start`/`argc`
    /// carry arguments (zero for zero-arg operators).
    ///
    /// At execution time, the VM calls back into `EvalCtx::eval_op`
    /// (zero-arg) or `apply_user_op_with_values` (with args).
    CallExternal {
        rd: Register,
        name_idx: ConstIdx,
        args_start: Register,
        argc: u8,
    },

    /// rd = r1 \o r2 (sequence/string concatenation via the `\o` or `\circ` operator).
    ///
    /// Distinguished from `StrConcat` because `\o` is polymorphic: it concatenates
    /// sequences as well as strings. The VM dispatches based on operand types.
    /// Part of #3789: stdlib operator compilation.
    Concat {
        rd: Register,
        r1: Register,
        r2: Register,
    },

    /// Call a standard-library builtin operator by tag.
    ///
    /// Used for operators from EXTENDS modules (Sequences, FiniteSets, TLC)
    /// that have dedicated implementations in the VM. Arguments are in
    /// consecutive registers starting at `args_start`.
    /// Part of #3789: cross-module identifier resolution for stdlib operators.
    CallBuiltin {
        rd: Register,
        builtin: BuiltinOp,
        args_start: Register,
        argc: u8,
    },

    /// No operation (used for alignment / patching).
    Nop,

    /// Halt execution with an error.
    Halt,
}
