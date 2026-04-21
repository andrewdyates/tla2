// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates
// Core IR types for the BTOR2 format.
//
// Opcode list derived from btor2parser.h (btor2tools, Biere et al.).

use std::collections::HashMap;

/// Unique identifier for a BTOR2 line/node. Negative values denote negation.
pub type NodeId = i64;

/// Unique identifier for a BTOR2 sort definition.
pub type SortId = i64;

// ---------------------------------------------------------------------------
// Sorts
// ---------------------------------------------------------------------------

/// A BTOR2 sort: either a bitvector of fixed width or an array.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Btor2Sort {
    /// Fixed-width bitvector. Width is in bits (must be >= 1).
    BitVec(u32),
    /// Array with index sort and element sort.
    Array {
        index: Box<Btor2Sort>,
        element: Box<Btor2Sort>,
    },
}

// ---------------------------------------------------------------------------
// Nodes (opcodes)
// ---------------------------------------------------------------------------

/// A BTOR2 node, representing every opcode in the format.
///
/// Opcodes are grouped by category. Arguments (operand node ids) are stored
/// separately in [`Btor2Line::args`] to keep the enum small; only opcode-
/// specific payload lives here.
///
/// Reference: `enum Btor2Tag` in btor2parser.h.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Btor2Node {
    // -- Sorts ---------------------------------------------------------------
    /// `sort bitvec <width>`
    SortBitVec(u32),
    /// `sort array <index_sort_id> <element_sort_id>`
    SortArray(NodeId, NodeId),

    // -- Constants -----------------------------------------------------------
    /// Binary constant string, e.g. `const 1 0110`.
    Const(String),
    /// Decimal constant string, e.g. `constd 1 42`.
    ConstD(String),
    /// Hexadecimal constant string, e.g. `consth 1 2a`.
    ConstH(String),
    /// Zero constant (all bits 0).
    Zero,
    /// One constant (value 1, width from sort).
    One,
    /// Ones constant (all bits 1).
    Ones,

    // -- State ---------------------------------------------------------------
    /// `state <sort> [<symbol>]`
    State(SortId, Option<String>),
    /// `input <sort> [<symbol>]`
    Input(SortId, Option<String>),

    // -- Init / Next ---------------------------------------------------------
    /// `init <sort> <state> <value>`
    Init(SortId, NodeId, NodeId),
    /// `next <sort> <state> <next_value>`
    Next(SortId, NodeId, NodeId),

    // -- Properties ----------------------------------------------------------
    /// `bad <cond>` — safety property (negated: system is safe if bad is unreachable).
    Bad(NodeId),
    /// `constraint <cond>` — environment constraint.
    Constraint(NodeId),
    /// `fair <cond>` — fairness constraint for liveness.
    Fair(NodeId),
    /// `justice <n> <cond_1> ... <cond_n>` — justice (liveness) property.
    Justice(Vec<NodeId>),
    /// `output <value>` — observable output.
    Output(NodeId),

    // -- Unary bitvector ops -------------------------------------------------
    /// Bitwise NOT.
    Not,
    /// Arithmetic negation (two's complement).
    Neg,
    /// Increment by one.
    Inc,
    /// Decrement by one.
    Dec,
    /// Reduction AND (1-bit result: 1 iff all bits are 1).
    Redand,
    /// Reduction OR (1-bit result: 1 iff any bit is 1).
    Redor,
    /// Reduction XOR (1-bit result: parity).
    Redxor,

    // -- Binary bitvector ops ------------------------------------------------
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Unsigned division.
    UDiv,
    /// Signed division.
    SDiv,
    /// Unsigned remainder.
    URem,
    /// Signed remainder.
    SRem,
    /// Signed modulo.
    SMod,
    /// Bitwise AND.
    And,
    /// Bitwise OR.
    Or,
    /// Bitwise XOR.
    Xor,
    /// Bitwise NAND.
    Nand,
    /// Bitwise NOR.
    Nor,
    /// Bitwise XNOR.
    Xnor,
    /// Shift left logical.
    Sll,
    /// Shift right logical.
    Srl,
    /// Shift right arithmetic.
    Sra,
    /// Rotate left.
    Rol,
    /// Rotate right.
    Ror,
    /// Equality.
    Eq,
    /// Disequality.
    Neq,
    /// Unsigned greater than.
    Ugt,
    /// Unsigned greater than or equal.
    Ugte,
    /// Unsigned less than.
    Ult,
    /// Unsigned less than or equal.
    Ulte,
    /// Signed greater than.
    Sgt,
    /// Signed greater than or equal.
    Sgte,
    /// Signed less than.
    Slt,
    /// Signed less than or equal.
    Slte,
    /// Concatenation (result width = width(a) + width(b)).
    Concat,

    // -- Indexed ops ---------------------------------------------------------
    /// `slice <upper> <lower>` — extract bits [upper:lower].
    Slice(u32, u32),
    /// `uext <width>` — unsigned extension by `width` bits.
    Uext(u32),
    /// `sext <width>` — signed extension by `width` bits.
    Sext(u32),

    // -- Ternary ops ---------------------------------------------------------
    /// `ite <cond> <then> <else>` — if-then-else.
    Ite,
    /// `write <array> <index> <value>` — array store.
    Write,

    // -- Array ops -----------------------------------------------------------
    /// `read <array> <index>` — array select.
    Read,

    // -- Overflow detection --------------------------------------------------
    /// Signed addition overflow.
    Saddo,
    /// Signed division overflow.
    Sdivo,
    /// Signed multiplication overflow.
    Smulo,
    /// Signed subtraction overflow.
    Ssubo,
    /// Unsigned addition overflow.
    Uaddo,
    /// Unsigned multiplication overflow.
    Umulo,
    /// Unsigned subtraction overflow.
    Usubo,

    // -- Boolean (1-bit) ops -------------------------------------------------
    /// Iff (biconditional, 1-bit).
    Iff,
    /// Implies (1-bit).
    Implies,
}

// ---------------------------------------------------------------------------
// Line
// ---------------------------------------------------------------------------

/// A single BTOR2 line: one node definition with its id, sort, and arguments.
///
/// Arguments in `args` may be negative, indicating the bitwise negation of
/// the referenced node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Btor2Line {
    /// Positive node identifier (unique, >= 1).
    pub id: i64,
    /// Sort identifier for this node's result type.
    pub sort_id: i64,
    /// The opcode and any opcode-specific payload.
    pub node: Btor2Node,
    /// Operand node ids. Negative values denote negation of the referenced node.
    pub args: Vec<i64>,
}

// ---------------------------------------------------------------------------
// Program
// ---------------------------------------------------------------------------

/// A complete BTOR2 program: all lines plus pre-indexed metadata.
#[derive(Debug, Clone)]
pub struct Btor2Program {
    /// All lines in source order.
    pub lines: Vec<Btor2Line>,
    /// Resolved sort definitions, keyed by sort line id.
    pub sorts: HashMap<i64, Btor2Sort>,
    /// Number of `input` declarations.
    pub num_inputs: usize,
    /// Number of `state` declarations.
    pub num_states: usize,
    /// Line ids of `bad` properties.
    pub bad_properties: Vec<i64>,
    /// Line ids of `constraint` nodes.
    pub constraints: Vec<i64>,
    /// Line ids of `fair` nodes.
    pub fairness: Vec<i64>,
    /// Each inner vec holds the condition node ids for one `justice` property.
    pub justice: Vec<Vec<i64>>,
}
