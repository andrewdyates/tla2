// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode operand type aliases and opcode metadata helpers.
//!
//! Separated from `opcode.rs` to keep the ISA enum definition focused.
//! All aliases are re-exported through `opcode.rs` so existing import
//! paths (`super::opcode::{Register, ConstIdx, ...}`) remain stable.

use super::opcode::Opcode;

/// A register index (0-255).
pub type Register = u8;

/// Identifies a standard-library builtin operator for the `CallBuiltin` opcode.
///
/// These are operators from EXTENDS modules (Sequences, FiniteSets, TLC) that
/// have dedicated implementations in the VM rather than being compiled from TIR.
/// Part of #3789: cross-module identifier resolution for stdlib operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinOp {
    /// Len(seq) — sequence length.
    Len,
    /// Head(seq) — first element.
    Head,
    /// Tail(seq) — all elements except the first.
    Tail,
    /// Append(seq, elem) — append element to sequence.
    Append,
    /// SubSeq(seq, lo, hi) — subsequence extraction.
    SubSeq,
    /// Seq(set) — set of all finite sequences over a base set (from Sequences).
    /// Returns `Value::SeqSet(SeqSetValue::new(base))`.
    /// Part of #3967: unblock bytecode compilation for specs using Seq(S).
    Seq,
    /// Cardinality(set) — set cardinality (from FiniteSets).
    Cardinality,
    /// IsFiniteSet(set) — finite-set predicate (from FiniteSets).
    IsFiniteSet,
    /// FoldFunctionOnSet(+, 0, f, S) — sum f[x] for x in S (from Functions).
    FoldFunctionOnSetSum,
    /// ToString(val) — convert to string (from TLC).
    ToString,
}

/// An index into the constant pool.
pub type ConstIdx = u16;

/// An index into the state variable array.
pub type VarIdx = u16;

/// An index into the operator table.
pub type OpIdx = u16;

/// A field index for record/tuple access.
pub type FieldIdx = u16;

/// A signed jump offset in the instruction stream.
pub type JumpOffset = i32;

impl Opcode {
    /// Returns the destination register, if any.
    #[must_use]
    pub const fn dest_register(&self) -> Option<Register> {
        match self {
            Self::LoadImm { rd, .. }
            | Self::LoadBool { rd, .. }
            | Self::LoadConst { rd, .. }
            | Self::LoadVar { rd, .. }
            | Self::LoadPrime { rd, .. }
            | Self::Move { rd, .. }
            | Self::AddInt { rd, .. }
            | Self::SubInt { rd, .. }
            | Self::MulInt { rd, .. }
            | Self::DivInt { rd, .. }
            | Self::IntDiv { rd, .. }
            | Self::ModInt { rd, .. }
            | Self::NegInt { rd, .. }
            | Self::PowInt { rd, .. }
            | Self::Eq { rd, .. }
            | Self::Neq { rd, .. }
            | Self::LtInt { rd, .. }
            | Self::LeInt { rd, .. }
            | Self::GtInt { rd, .. }
            | Self::GeInt { rd, .. }
            | Self::And { rd, .. }
            | Self::Or { rd, .. }
            | Self::Not { rd, .. }
            | Self::Implies { rd, .. }
            | Self::Equiv { rd, .. }
            | Self::Call { rd, .. }
            | Self::ValueApply { rd, .. }
            | Self::SetEnum { rd, .. }
            | Self::SetIn { rd, .. }
            | Self::SetUnion { rd, .. }
            | Self::SetIntersect { rd, .. }
            | Self::SetDiff { rd, .. }
            | Self::Subseteq { rd, .. }
            | Self::Powerset { rd, .. }
            | Self::BigUnion { rd, .. }
            | Self::KSubset { rd, .. }
            | Self::Range { rd, .. }
            | Self::ForallBegin { rd, .. }
            | Self::ForallNext { rd, .. }
            | Self::ExistsBegin { rd, .. }
            | Self::ExistsNext { rd, .. }
            | Self::RecordNew { rd, .. }
            | Self::RecordGet { rd, .. }
            | Self::FuncApply { rd, .. }
            | Self::Domain { rd, .. }
            | Self::FuncExcept { rd, .. }
            | Self::TupleNew { rd, .. }
            | Self::TupleGet { rd, .. }
            | Self::FuncDef { rd, .. }
            | Self::FuncSet { rd, .. }
            | Self::RecordSet { rd, .. }
            | Self::Times { rd, .. }
            | Self::SeqNew { rd, .. }
            | Self::StrConcat { rd, .. }
            | Self::CondMove { rd, .. }
            | Self::ChooseBegin { rd, .. }
            | Self::ChooseNext { rd, .. }
            | Self::SetBuilderBegin { rd, .. }
            | Self::SetFilterBegin { rd, .. }
            | Self::FuncDefBegin { rd, .. }
            | Self::Unchanged { rd, .. }
            | Self::MakeClosure { rd, .. }
            | Self::CallExternal { rd, .. }
            | Self::Concat { rd, .. }
            | Self::CallBuiltin { rd, .. } => Some(*rd),

            Self::StoreVar { .. }
            | Self::Jump { .. }
            | Self::JumpTrue { .. }
            | Self::JumpFalse { .. }
            | Self::Ret { .. }
            | Self::LoopNext { .. }
            | Self::SetPrimeMode { .. }
            | Self::Nop
            | Self::Halt => None,
        }
    }

    /// Returns the binding register for loop opcodes that write to an
    /// iteration variable. Used by `BytecodeFunction::emit` to ensure
    /// `max_register` accounts for all written registers.
    #[must_use]
    pub const fn binding_register(&self) -> Option<Register> {
        match self {
            Self::ForallBegin { r_binding, .. }
            | Self::ExistsBegin { r_binding, .. }
            | Self::ChooseBegin { r_binding, .. }
            | Self::SetFilterBegin { r_binding, .. }
            | Self::SetBuilderBegin { r_binding, .. }
            | Self::FuncDefBegin { r_binding, .. } => Some(*r_binding),
            _ => None,
        }
    }

    /// Returns the highest source register referenced by this opcode.
    ///
    /// Defense-in-depth for #3802: ensures `max_register` accounts for ALL
    /// registers an opcode reads, not just destinations. Without this, a
    /// stale parent-scope binding register that leaks into a sub-function
    /// could reference a register beyond the allocated register file, causing
    /// an index-out-of-bounds panic at runtime.
    #[must_use]
    pub const fn max_source_register(&self) -> Option<Register> {
        match self {
            // Opcodes with no source registers
            Self::LoadImm { .. }
            | Self::LoadBool { .. }
            | Self::LoadConst { .. }
            | Self::LoadVar { .. }
            | Self::LoadPrime { .. }
            | Self::Jump { .. }
            | Self::SetPrimeMode { .. }
            | Self::Nop
            | Self::Halt
            | Self::Unchanged { .. } => None,

            // Single source register
            Self::StoreVar { rs, .. }
            | Self::Move { rs, .. }
            | Self::NegInt { rs, .. }
            | Self::Not { rs, .. }
            | Self::Powerset { rs, .. }
            | Self::BigUnion { rs, .. }
            | Self::Domain { rs, .. }
            | Self::RecordGet { rs, .. }
            | Self::Ret { rs } => Some(*rs),

            // Conditional branch source
            Self::JumpTrue { rs, .. } | Self::JumpFalse { rs, .. } => Some(*rs),

            // Two source registers — return the larger
            Self::AddInt { r1, r2, .. }
            | Self::SubInt { r1, r2, .. }
            | Self::MulInt { r1, r2, .. }
            | Self::DivInt { r1, r2, .. }
            | Self::IntDiv { r1, r2, .. }
            | Self::ModInt { r1, r2, .. }
            | Self::PowInt { r1, r2, .. }
            | Self::Eq { r1, r2, .. }
            | Self::Neq { r1, r2, .. }
            | Self::LtInt { r1, r2, .. }
            | Self::LeInt { r1, r2, .. }
            | Self::GtInt { r1, r2, .. }
            | Self::GeInt { r1, r2, .. }
            | Self::And { r1, r2, .. }
            | Self::Or { r1, r2, .. }
            | Self::Implies { r1, r2, .. }
            | Self::Equiv { r1, r2, .. }
            | Self::SetUnion { r1, r2, .. }
            | Self::SetIntersect { r1, r2, .. }
            | Self::SetDiff { r1, r2, .. }
            | Self::Subseteq { r1, r2, .. }
            | Self::StrConcat { r1, r2, .. }
            | Self::Concat { r1, r2, .. } => {
                if *r1 > *r2 {
                    Some(*r1)
                } else {
                    Some(*r2)
                }
            }

            // Range has lo, hi source registers
            Self::Range { lo, hi, .. } => {
                if *lo > *hi {
                    Some(*lo)
                } else {
                    Some(*hi)
                }
            }

            // KSubset has base, k source registers
            Self::KSubset { base, k, .. } => {
                if *base > *k {
                    Some(*base)
                } else {
                    Some(*k)
                }
            }

            // Set membership: elem, set sources
            Self::SetIn { elem, set, .. } => {
                if *elem > *set {
                    Some(*elem)
                } else {
                    Some(*set)
                }
            }

            // FuncApply: func, arg sources
            Self::FuncApply { func, arg, .. } => {
                if *func > *arg {
                    Some(*func)
                } else {
                    Some(*arg)
                }
            }

            // FuncSet: domain, range sources
            Self::FuncSet { domain, range, .. } => {
                if *domain > *range {
                    Some(*domain)
                } else {
                    Some(*range)
                }
            }

            // FuncExcept: func, path, val sources
            Self::FuncExcept {
                func, path, val, ..
            } => {
                let m = if *func > *path { *func } else { *path };
                if m > *val {
                    Some(m)
                } else {
                    Some(*val)
                }
            }

            // CondMove: cond, rs sources
            Self::CondMove { cond, rs, .. } => {
                if *cond > *rs {
                    Some(*cond)
                } else {
                    Some(*rs)
                }
            }

            // Aggregate opcodes with start+count — max source is start+count-1
            Self::SetEnum { start, count, .. }
            | Self::TupleNew { start, count, .. }
            | Self::SeqNew { start, count, .. }
            | Self::Times { start, count, .. } => {
                if *count == 0 {
                    None
                } else {
                    Some(*start + *count - 1)
                }
            }

            // RecordNew: values_start + count - 1
            Self::RecordNew {
                values_start,
                count,
                ..
            }
            | Self::RecordSet {
                values_start,
                count,
                ..
            } => {
                if *count == 0 {
                    None
                } else {
                    Some(*values_start + *count - 1)
                }
            }

            // TupleGet: just rs source
            Self::TupleGet { rs, .. } => Some(*rs),

            // FuncDef: r_domain, r_binding sources
            Self::FuncDef {
                r_domain,
                r_binding,
                ..
            } => {
                if *r_domain > *r_binding {
                    Some(*r_domain)
                } else {
                    Some(*r_binding)
                }
            }

            // Call: args_start + argc - 1
            Self::Call {
                args_start, argc, ..
            } => {
                if *argc == 0 {
                    None
                } else {
                    Some(*args_start + *argc - 1)
                }
            }

            // ValueApply: func, args_start + argc - 1
            Self::ValueApply {
                func,
                args_start,
                argc,
                ..
            } => {
                let max_arg = if *argc == 0 {
                    0
                } else {
                    *args_start + *argc - 1
                };
                if *func > max_arg {
                    Some(*func)
                } else {
                    Some(max_arg)
                }
            }

            // CallExternal: args_start + argc - 1
            Self::CallExternal {
                args_start, argc, ..
            } => {
                if *argc == 0 {
                    None
                } else {
                    Some(*args_start + *argc - 1)
                }
            }

            // CallBuiltin: args_start + argc - 1
            Self::CallBuiltin {
                args_start, argc, ..
            } => {
                if *argc == 0 {
                    None
                } else {
                    Some(*args_start + *argc - 1)
                }
            }

            // MakeClosure: captures_start + capture_count - 1
            Self::MakeClosure {
                captures_start,
                capture_count,
                ..
            } => {
                if *capture_count == 0 {
                    None
                } else {
                    Some(*captures_start + *capture_count - 1)
                }
            }

            // Quantifier Begin: r_binding, r_domain sources
            Self::ForallBegin {
                r_binding,
                r_domain,
                ..
            }
            | Self::ExistsBegin {
                r_binding,
                r_domain,
                ..
            }
            | Self::ChooseBegin {
                r_binding,
                r_domain,
                ..
            }
            | Self::SetFilterBegin {
                r_binding,
                r_domain,
                ..
            }
            | Self::SetBuilderBegin {
                r_binding,
                r_domain,
                ..
            }
            | Self::FuncDefBegin {
                r_binding,
                r_domain,
                ..
            } => {
                if *r_binding > *r_domain {
                    Some(*r_binding)
                } else {
                    Some(*r_domain)
                }
            }

            // Quantifier Next: r_binding, r_body sources
            Self::ForallNext {
                r_binding, r_body, ..
            }
            | Self::ExistsNext {
                r_binding, r_body, ..
            }
            | Self::ChooseNext {
                r_binding, r_body, ..
            } => {
                if *r_binding > *r_body {
                    Some(*r_binding)
                } else {
                    Some(*r_body)
                }
            }

            // LoopNext: r_binding, r_body sources
            Self::LoopNext {
                r_binding, r_body, ..
            } => {
                if *r_binding > *r_body {
                    Some(*r_binding)
                } else {
                    Some(*r_body)
                }
            }
        }
    }
}
