// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode-to-tMIR IR lowering.
//!
//! Mirrors the structure of `tla-llvm/src/lower.rs` but targets tmir types
//! instead of LLVM IR text. Each bytecode register is backed by an alloca;
//! the tMIR optimizer can promote these to SSA form later.
//!
//! This module is split across several files:
//! - `mod.rs` — public API, Ctx struct, register/block/state helpers, dispatch
//! - `arithmetic.rs` — overflow-checked arithmetic (Add, Sub, Mul, Neg, Div, Mod)
//! - `logic.rs` — comparison and boolean ops (Eq, And, Or, Not, Implies, etc.)
//! - `set_ops.rs` — set operations (SetEnum, SetIn, Union, Intersect, etc.)
//! - `sequences.rs` — sequences, tuples, records, cardinality, seq builtins
//! - `quantifiers.rs` — ForAll, Exists, Choose
//! - `functions.rs` — FuncApply, Domain, FuncExcept, FuncDef
//! - `constants.rs` — LoadConst, FuncSet, Unchanged
//! - `calls.rs` — inter-function Call
//! - `tests.rs` — all tests

mod arithmetic;
mod binding_frame;
mod calls;
mod constants;
mod functions;
mod logic;
mod quantifiers;
mod sequences;
mod set_ops;
#[cfg(test)]
mod tests;

use crate::TmirError;
use num_traits::ToPrimitive;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use tla_core::NameId;
use tla_jit_abi::{
    CompoundLayout, JitCallOut, JitRuntimeErrorKind, JitStatus, SetBitmaskElement,
    StateLayout as JitStateLayout, VarLayout,
};
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, ConstantPool, Opcode};
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::value::{BlockId, FuncId, ValueId};
use tmir::{Block, Constant, InstrNode, Module};

const STATUS_OFFSET: usize = std::mem::offset_of!(JitCallOut, status);
const VALUE_OFFSET: usize = std::mem::offset_of!(JitCallOut, value);
const ERR_KIND_OFFSET: usize = std::mem::offset_of!(JitCallOut, err_kind);
const ERR_SPAN_START_OFFSET: usize = std::mem::offset_of!(JitCallOut, err_span_start);
const ERR_SPAN_END_OFFSET: usize = std::mem::offset_of!(JitCallOut, err_span_end);
const ERR_FILE_ID_OFFSET: usize = std::mem::offset_of!(JitCallOut, err_file_id);
const MAX_LAZY_POWERSET_BASE_LEN: u32 = 64;
const MAX_CALLEE_ARG_SHAPE_FIXPOINT_STEPS: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LoweringMode {
    Invariant,
    NextState,
}

/// Lower a bytecode invariant function to a tmir::Module.
///
/// The generated function has the signature:
///   `fn(out: *mut JitCallOut, state: *const i64, state_len: u32) -> void`
pub fn lower_invariant(func: &BytecodeFunction, name: &str) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::Invariant, None, None)
}

/// Lower a bytecode invariant function to a tmir::Module, with constant pool.
///
/// Same as [`lower_invariant`] but accepts a [`ConstantPool`] for resolving
/// `LoadConst` opcodes.
pub fn lower_invariant_with_constants(
    func: &BytecodeFunction,
    name: &str,
    const_pool: &ConstantPool,
) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::Invariant, Some(const_pool), None)
}

/// Lower a bytecode invariant function to a tmir::Module, with constant pool
/// and checker-provided state-layout metadata.
pub fn lower_invariant_with_constants_and_layout(
    func: &BytecodeFunction,
    name: &str,
    const_pool: &ConstantPool,
    state_layout: &JitStateLayout,
) -> Result<Module, TmirError> {
    lower_function(
        func,
        name,
        LoweringMode::Invariant,
        Some(const_pool),
        Some(state_layout),
    )
}

/// Lower a bytecode next-state function to a tmir::Module.
///
/// The generated function has the signature:
///   `fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32) -> void`
pub fn lower_next_state(func: &BytecodeFunction, name: &str) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::NextState, None, None)
}

/// Lower a bytecode next-state function to a tmir::Module, with constant pool.
///
/// Same as [`lower_next_state`] but accepts a [`ConstantPool`] for resolving
/// `LoadConst` and `Unchanged` opcodes.
pub fn lower_next_state_with_constants(
    func: &BytecodeFunction,
    name: &str,
    const_pool: &ConstantPool,
) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::NextState, Some(const_pool), None)
}

/// Lower a bytecode next-state function to a tmir::Module, with constant pool
/// and checker-provided state-layout metadata.
pub fn lower_next_state_with_constants_and_layout(
    func: &BytecodeFunction,
    name: &str,
    const_pool: &ConstantPool,
    state_layout: &JitStateLayout,
) -> Result<Module, TmirError> {
    lower_function(
        func,
        name,
        LoweringMode::NextState,
        Some(const_pool),
        Some(state_layout),
    )
}

/// Lower a multi-function bytecode chunk to a tmir::Module.
///
/// The entrypoint function (at `entry_idx` in the chunk) is lowered with the
/// given mode (Invariant or NextState). All functions reachable via `Call`
/// opcodes are transitively lowered as callee functions that receive the
/// entrypoint context parameters, a hidden caller-owned fixed-width
/// record/sequence/function return buffer, then their user `i64` arguments.
///
/// This is the primary entry point for compiling real TLA+ specs where
/// operators call other operators.
pub fn lower_module_invariant(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
) -> Result<Module, TmirError> {
    lower_module(chunk, entry_idx, name, LoweringMode::Invariant, None)
}

/// Lower a multi-function bytecode chunk as an invariant with checker-provided
/// state-layout metadata.
pub fn lower_module_invariant_with_layout(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
    state_layout: &JitStateLayout,
) -> Result<Module, TmirError> {
    lower_module(
        chunk,
        entry_idx,
        name,
        LoweringMode::Invariant,
        Some(state_layout),
    )
}

/// Lower a multi-function bytecode chunk for next-state evaluation.
///
/// Same as [`lower_module_invariant`] but the entrypoint has the next-state
/// signature: `fn(out, state_in, state_out, state_len) -> void`.
pub fn lower_module_next_state(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
) -> Result<Module, TmirError> {
    lower_module(chunk, entry_idx, name, LoweringMode::NextState, None)
}

/// Lower a multi-function bytecode chunk for next-state evaluation with
/// checker-provided state-layout metadata.
pub fn lower_module_next_state_with_layout(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
    state_layout: &JitStateLayout,
) -> Result<Module, TmirError> {
    lower_module(
        chunk,
        entry_idx,
        name,
        LoweringMode::NextState,
        Some(state_layout),
    )
}

/// Lower a standalone entry function as an invariant, resolving callees from
/// `chunk`.
///
/// This is the entry point used by callers that hold a [`BytecodeFunction`]
/// that is NOT stored inside `chunk.functions` — for example the arity-0
/// specialized functions produced by
/// `tla_tir::bytecode::specialize_bytecode_function` for EXISTS-bound actions
/// (#4270). The entry function is lowered first, then every transitively
/// reachable callee is drained from `chunk` exactly as in
/// [`lower_module_invariant`]. The chunk's constant pool is also threaded
/// through so `LoadConst` / `Unchanged` compound constants resolve. (Part of
/// #4280 Gap C — avoids emitting `__func_N` unresolved symbols when the
/// entry function contains user-defined-operator `Call` opcodes.)
pub fn lower_entry_invariant_with_chunk(
    entry_func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
) -> Result<Module, TmirError> {
    lower_entry_with_chunk(entry_func, chunk, name, LoweringMode::Invariant, None)
}

/// Lower a standalone invariant entry function while resolving callees from
/// `chunk`, with checker-provided state-layout metadata.
pub fn lower_entry_invariant_with_chunk_and_layout(
    entry_func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
    state_layout: &JitStateLayout,
) -> Result<Module, TmirError> {
    lower_entry_with_chunk(
        entry_func,
        chunk,
        name,
        LoweringMode::Invariant,
        Some(state_layout),
    )
}

/// Lower a standalone entry function as a next-state action, resolving
/// callees from `chunk`.
///
/// Next-state counterpart of [`lower_entry_invariant_with_chunk`]. See that
/// function for full rationale. (Part of #4280 Gap C.)
pub fn lower_entry_next_state_with_chunk(
    entry_func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
) -> Result<Module, TmirError> {
    lower_entry_with_chunk(entry_func, chunk, name, LoweringMode::NextState, None)
}

/// Lower a standalone entry function as a next-state action, resolving
/// callees from `chunk`, with checker-provided state-layout metadata.
pub fn lower_entry_next_state_with_chunk_and_layout(
    entry_func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
    state_layout: &JitStateLayout,
) -> Result<Module, TmirError> {
    lower_entry_with_chunk(
        entry_func,
        chunk,
        name,
        LoweringMode::NextState,
        Some(state_layout),
    )
}

fn lower_module(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    module_name: &str,
    mode: LoweringMode,
    state_layout: Option<&JitStateLayout>,
) -> Result<Module, TmirError> {
    let entry_func = chunk.functions.get(entry_idx as usize).ok_or_else(|| {
        TmirError::Emission(format!(
            "entry function index {entry_idx} out of range (chunk has {} functions)",
            chunk.functions.len()
        ))
    })?;

    lower_entry_with_chunk(entry_func, chunk, module_name, mode, state_layout)
}

fn lower_entry_with_chunk(
    entry_func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    module_name: &str,
    mode: LoweringMode,
    state_layout: Option<&JitStateLayout>,
) -> Result<Module, TmirError> {
    // Thread the chunk's shared constant pool through lowering so callees
    // (as well as the entry function) can resolve `LoadConst` / `Unchanged`
    // compound constants. Prior code passed `None`, which forced every chunk
    // entry point onto the constant-pool-less path and regressed parity with
    // the single-function `lower_*_with_constants` variants. (Part of #4280.)
    let mut ctx = Ctx::new(
        entry_func,
        module_name,
        mode,
        Some(&chunk.constants),
        state_layout,
        Some(chunk),
    )?;
    ctx.callee_return_shapes = infer_chunk_return_shapes(chunk, state_layout);
    ctx.callee_arg_shapes = collect_reachable_callee_arg_shapes(entry_func, chunk, state_layout)?;

    // Lower the entrypoint body.
    ctx.lower_body(entry_func)?;

    // Iteratively lower callees until fixpoint. Each lowered callee may
    // reference further callees via Call opcodes.
    loop {
        let pending: Vec<u16> = ctx.pending_callees();
        if pending.is_empty() {
            break;
        }

        for op_idx in pending {
            let callee_func = chunk.functions.get(op_idx as usize).ok_or_else(|| {
                TmirError::Emission(format!(
                    "Call references function index {op_idx} but chunk has only {} functions",
                    chunk.functions.len()
                ))
            })?;

            ctx.lower_callee(callee_func, op_idx)?;
        }
    }

    Ok(ctx.finish())
}

fn lower_function<'cp>(
    func: &BytecodeFunction,
    func_name: &str,
    mode: LoweringMode,
    const_pool: Option<&'cp ConstantPool>,
    state_layout: Option<&JitStateLayout>,
) -> Result<Module, TmirError> {
    let mut ctx = Ctx::new(func, func_name, mode, const_pool, state_layout, None)?;
    ctx.lower_body(func)?;
    Ok(ctx.finish())
}

fn namespaced_callee_name(module_name: &str, op_idx: u16, raw_name: &str) -> String {
    format!(
        "__tmir_callee_m{}_o{op_idx}_n{}",
        symbol_component(module_name),
        symbol_component(raw_name)
    )
}

fn symbol_component(value: &str) -> String {
    use std::fmt::Write as _;

    let mut encoded = String::with_capacity(value.len() * 2 + 8);
    write!(&mut encoded, "{}x", value.len()).expect("writing to String cannot fail");
    for byte in value.as_bytes() {
        write!(&mut encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    encoded
}

/// State shared between a quantifier's Begin and Next opcodes.
///
/// The Begin opcode initializes the iterator (alloca for index, domain pointer,
/// domain length) and the header block. The Next opcode uses these to advance
/// the iterator and implement short-circuit logic.
struct QuantifierLoopState {
    /// Alloca holding the current iteration index (i64).
    idx_alloca: ValueId,
    /// tMIR block index for the loop header (bounds check + element load).
    header_block: usize,
    /// tMIR block index for the exit point (after the loop).
    exit_block: usize,
}

#[derive(Clone, Copy)]
struct FuncDefCaptureState {
    /// Block that branches into the FuncDef loop header. Capture backing
    /// allocas are inserted here so they execute once per FuncDef evaluation,
    /// not once per loop iteration.
    preheader_block: usize,
    /// Runtime domain length loaded by FuncDefBegin.
    domain_len: ValueId,
    /// Compile-time domain capacity when known.
    static_domain_capacity: Option<u32>,
}

enum LoopNextKind {
    FuncDef,
    SetFilter,
}

struct LoopNextState {
    rd: u8,
    kind: LoopNextKind,
    loop_state: QuantifierLoopState,
    funcdef_capture: Option<FuncDefCaptureState>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompactStateSlot {
    source_ptr: ValueId,
    offset: u32,
    provenance: CompactStateSlotProvenance,
    source_block: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompactStateSlotProvenance {
    RawCompactSlot,
    PointerBackedAggregate,
    RegisterBackedAggregate,
}

impl CompactStateSlot {
    fn raw(source_ptr: ValueId, offset: u32) -> Self {
        Self {
            source_ptr,
            offset,
            provenance: CompactStateSlotProvenance::RawCompactSlot,
            source_block: None,
        }
    }

    fn pointer_backed_in_block(source_ptr: ValueId, offset: u32, source_block: usize) -> Self {
        Self {
            source_ptr,
            offset,
            provenance: CompactStateSlotProvenance::PointerBackedAggregate,
            source_block: Some(source_block),
        }
    }

    fn pointer_backed(source_ptr: ValueId, offset: u32) -> Self {
        Self {
            source_ptr,
            offset,
            provenance: CompactStateSlotProvenance::PointerBackedAggregate,
            source_block: None,
        }
    }

    fn register_backed(source_ptr: ValueId, offset: u32) -> Self {
        Self {
            source_ptr,
            offset,
            provenance: CompactStateSlotProvenance::RegisterBackedAggregate,
            source_block: None,
        }
    }

    fn as_raw_slot(self) -> Self {
        Self::raw(self.source_ptr, self.offset)
    }

    fn is_raw_compact_slot(self) -> bool {
        self.provenance == CompactStateSlotProvenance::RawCompactSlot
    }

    fn requires_pointer_reload_in_block(self, block_idx: usize) -> bool {
        match self.provenance {
            CompactStateSlotProvenance::RawCompactSlot => false,
            CompactStateSlotProvenance::RegisterBackedAggregate => true,
            CompactStateSlotProvenance::PointerBackedAggregate => {
                self.source_block != Some(block_idx)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompactCopyResult {
    slots_written: u32,
    block_idx: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompactSequenceLenGuardResult {
    block_idx: usize,
    len_value: ValueId,
}

impl From<CompactSequenceLenGuardResult> for usize {
    fn from(result: CompactSequenceLenGuardResult) -> Self {
        result.block_idx
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompactMaterializationResult {
    slot: CompactStateSlot,
    block_idx: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ScalarShape {
    Int,
    Bool,
    String,
    ModelValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SymbolicDomain {
    Nat,
    Int,
    Real,
}

impl SymbolicDomain {
    fn from_model_value(name: &str) -> Option<Self> {
        match name {
            "Nat" => Some(SymbolicDomain::Nat),
            "Int" => Some(SymbolicDomain::Int),
            "Real" => Some(SymbolicDomain::Real),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AggregateShape {
    /// Value loaded from the state buffer when no checker layout metadata was
    /// supplied. Type-domain operators can refine this with their own shape.
    StateValue,
    Scalar(ScalarShape),
    ScalarIntDomain {
        universe_len: u32,
        universe: SetBitmaskUniverse,
    },
    SymbolicDomain(SymbolicDomain),
    Function {
        len: u32,
        domain_lo: Option<i64>,
        value: Option<Box<AggregateShape>>,
    },
    Record {
        fields: Vec<(NameId, Option<Box<AggregateShape>>)>,
    },
    RecordSet {
        fields: Vec<(NameId, AggregateShape)>,
    },
    Powerset {
        base: Box<AggregateShape>,
    },
    FunctionSet {
        domain: Box<AggregateShape>,
        range: Box<AggregateShape>,
    },
    SeqSet {
        base: Box<AggregateShape>,
    },
    Interval {
        lo: i64,
        hi: i64,
    },
    SetBitmask {
        universe_len: u32,
        universe: SetBitmaskUniverse,
    },
    ExactIntSet {
        values: Vec<i64>,
    },
    Set {
        len: u32,
        element: Option<Box<AggregateShape>>,
    },
    FiniteSet,
    BoundedSet {
        max_len: u32,
        element: Option<Box<AggregateShape>>,
    },
    Sequence {
        extent: SequenceExtent,
        element: Option<Box<AggregateShape>>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SequenceExtent {
    Exact(u32),
    Capacity(u32),
}

impl SequenceExtent {
    fn exact_count(self) -> Option<u32> {
        match self {
            SequenceExtent::Exact(len) => Some(len),
            SequenceExtent::Capacity(_) => None,
        }
    }

    fn capacity(self) -> u32 {
        match self {
            SequenceExtent::Exact(len) | SequenceExtent::Capacity(len) => len,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SetBitmaskUniverse {
    /// Bit `i` represents integer element `lo + i`.
    IntRange { lo: i64 },
    /// Explicit finite integer table in bit-index order.
    ExplicitInt(Vec<i64>),
    /// Exact non-integer or mixed element table in bit-index order.
    Exact(Vec<SetBitmaskElement>),
    /// The ABI metadata only preserved compact-set width, not the exact
    /// element universe. Lowering must not map bits to values from this shape.
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RecordSelectorMode {
    FieldName,
    Positional,
}

impl SetBitmaskUniverse {
    fn from_elements(elements: &[SetBitmaskElement]) -> Self {
        if let Some(lo) = contiguous_int_universe_lo(elements) {
            return SetBitmaskUniverse::IntRange { lo };
        }
        let mut values = Vec::with_capacity(elements.len());
        for element in elements {
            let SetBitmaskElement::Int(value) = element else {
                return SetBitmaskUniverse::Exact(elements.to_vec());
            };
            values.push(*value);
        }
        SetBitmaskUniverse::ExplicitInt(values)
    }
}

fn bounded_set_or_finite_with_element(
    max_len: u32,
    element: Option<Box<AggregateShape>>,
) -> AggregateShape {
    if max_len <= MAX_LAZY_POWERSET_BASE_LEN {
        AggregateShape::BoundedSet { max_len, element }
    } else {
        AggregateShape::FiniteSet
    }
}

fn interval_len_u32(lo: i64, hi: i64) -> Option<u32> {
    if hi < lo {
        return Some(0);
    }
    hi.checked_sub(lo)
        .and_then(|span| span.checked_add(1))
        .and_then(|len| u32::try_from(len).ok())
}

fn contiguous_int_universe_lo(elements: &[SetBitmaskElement]) -> Option<i64> {
    let first = match elements.first()? {
        SetBitmaskElement::Int(n) => *n,
        _ => return None,
    };
    for (idx, element) in elements.iter().enumerate() {
        let SetBitmaskElement::Int(n) = element else {
            return None;
        };
        if *n != first + idx as i64 {
            return None;
        }
    }
    Some(first)
}

impl AggregateShape {
    fn tracked_len(&self) -> Option<u32> {
        match self {
            AggregateShape::Function { len, .. } | AggregateShape::Set { len, .. } => Some(*len),
            AggregateShape::Sequence { extent, .. } => extent.exact_count(),
            AggregateShape::ExactIntSet { values } => u32::try_from(values.len()).ok(),
            AggregateShape::Interval { lo, hi } => interval_len_u32(*lo, *hi),
            AggregateShape::Record { .. }
            | AggregateShape::RecordSet { .. }
            | AggregateShape::Powerset { .. }
            | AggregateShape::FunctionSet { .. }
            | AggregateShape::SeqSet { .. }
            | AggregateShape::SetBitmask { .. }
            | AggregateShape::FiniteSet
            | AggregateShape::BoundedSet { .. }
            | AggregateShape::StateValue
            | AggregateShape::Scalar(_)
            | AggregateShape::ScalarIntDomain { .. }
            | AggregateShape::SymbolicDomain(_) => None,
        }
    }

    fn finite_set_len_bound(&self) -> Option<u32> {
        match self {
            AggregateShape::Set { len, .. }
            | AggregateShape::SetBitmask {
                universe_len: len, ..
            }
            | AggregateShape::BoundedSet { max_len: len, .. } => Some(*len),
            AggregateShape::ExactIntSet { values } => u32::try_from(values.len()).ok(),
            AggregateShape::Interval { lo, hi } => interval_len_u32(*lo, *hi),
            _ => None,
        }
    }

    fn finite_set_element_shape(&self) -> Option<AggregateShape> {
        match self {
            AggregateShape::Set {
                element: Some(element),
                ..
            }
            | AggregateShape::BoundedSet {
                element: Some(element),
                ..
            } => Some((**element).clone()),
            AggregateShape::ExactIntSet { .. } | AggregateShape::Interval { .. } => {
                Some(AggregateShape::Scalar(ScalarShape::Int))
            }
            AggregateShape::SetBitmask { .. } => scalar_int_domain_shape_from_domain(self),
            _ => None,
        }
    }

    fn is_numeric_scalar_shape(&self) -> bool {
        matches!(
            self,
            AggregateShape::Scalar(ScalarShape::Int) | AggregateShape::ScalarIntDomain { .. }
        )
    }

    fn scalar_int_domain_universe(&self) -> Option<(u32, SetBitmaskUniverse)> {
        match self {
            AggregateShape::ScalarIntDomain {
                universe_len,
                universe,
            } => Some((*universe_len, universe.clone())),
            _ => None,
        }
    }

    fn set_bitmask_universe(&self) -> Option<(u32, SetBitmaskUniverse)> {
        match self {
            AggregateShape::SetBitmask {
                universe_len,
                universe,
            } if !matches!(universe, SetBitmaskUniverse::Unknown) => {
                Some((*universe_len, universe.clone()))
            }
            _ => None,
        }
    }

    fn compatible_set_bitmask_universe(
        &self,
        universe_len: u32,
        universe: &SetBitmaskUniverse,
    ) -> bool {
        if matches!(universe, SetBitmaskUniverse::Unknown) {
            return false;
        }
        matches!(
            self,
            AggregateShape::SetBitmask {
                universe_len: len,
                universe: other,
            } if *len == universe_len
                && !matches!(other, SetBitmaskUniverse::Unknown)
                && other == universe
        )
    }

    fn matches_set_bitmask_base(&self, universe_len: u32, universe: &SetBitmaskUniverse) -> bool {
        match (self, universe) {
            (
                AggregateShape::Interval { lo, hi },
                SetBitmaskUniverse::IntRange { lo: universe_lo },
            ) if lo == universe_lo => interval_len_u32(*lo, *hi) == Some(universe_len),
            (AggregateShape::ExactIntSet { .. } | AggregateShape::Interval { .. }, _) => {
                set_bitmask_valid_mask(universe_len).is_some_and(|valid_mask| {
                    static_int_base_mask_for_set_bitmask_universe(self, universe_len, universe)
                        == Some(valid_mask)
                })
            }
            _ => self.compatible_set_bitmask_universe(universe_len, universe),
        }
    }

    fn is_finite_set_shape(&self) -> bool {
        matches!(
            self,
            AggregateShape::Set { .. }
                | AggregateShape::ExactIntSet { .. }
                | AggregateShape::SetBitmask { .. }
                | AggregateShape::FiniteSet
                | AggregateShape::BoundedSet { .. }
                | AggregateShape::Interval { .. }
        )
    }

    fn is_lazy_set_shape(&self) -> bool {
        matches!(
            self,
            AggregateShape::RecordSet { .. }
                | AggregateShape::Powerset { .. }
                | AggregateShape::FunctionSet { .. }
                | AggregateShape::SeqSet { .. }
                | AggregateShape::SymbolicDomain(_)
        )
    }

    fn is_powerset_of_compact_set_bitmask(&self) -> bool {
        matches!(
            self,
            AggregateShape::Powerset { base }
                if matches!(base.as_ref(), AggregateShape::SetBitmask { .. })
        )
    }

    fn validate_powerset_base(&self, context: &str) -> Result<(), TmirError> {
        if let AggregateShape::SetBitmask { universe, .. } = self {
            if *universe == SetBitmaskUniverse::Unknown {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask base requires exact universe metadata"
                )));
            }
        }
        if !self.is_finite_set_shape() {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: SUBSET base must be a tracked finite set or interval, got {self:?}"
            )));
        }
        let Some(len) = self.finite_set_len_bound() else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: SUBSET base cardinality bound is not statically known: {self:?}"
            )));
        };
        if len > MAX_LAZY_POWERSET_BASE_LEN {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: SUBSET base cardinality {len} exceeds tMIR lazy powerset limit of {MAX_LAZY_POWERSET_BASE_LEN}"
            )));
        }
        Ok(())
    }

    fn validate_function_set_range(&self, context: &str) -> Result<(), TmirError> {
        if let AggregateShape::SetBitmask { universe, .. } = self {
            if *universe == SetBitmaskUniverse::Unknown {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask range requires exact universe metadata"
                )));
            }
        }
        match self {
            AggregateShape::Set { .. }
            | AggregateShape::ExactIntSet { .. }
            | AggregateShape::SetBitmask { .. }
            | AggregateShape::FiniteSet
            | AggregateShape::BoundedSet { .. }
            | AggregateShape::Interval { .. } => {
                if matches!(self, AggregateShape::FiniteSet) {
                    return Ok(());
                }
                let Some(len) = self.finite_set_len_bound() else {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: function-set range cardinality bound is not statically known: {self:?}"
                    )));
                };
                if len > MAX_LAZY_POWERSET_BASE_LEN {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: function-set range cardinality {len} exceeds tMIR limit of {MAX_LAZY_POWERSET_BASE_LEN}"
                    )));
                }
                Ok(())
            }
            AggregateShape::SymbolicDomain(_) => Ok(()),
            AggregateShape::Powerset { base } => base.validate_powerset_base(context),
            AggregateShape::FunctionSet { domain, range } => {
                domain.validate_powerset_base(context)?;
                range.validate_function_set_range(context)
            }
            AggregateShape::RecordSet { .. } => Ok(()),
            AggregateShape::SeqSet { .. } => Ok(()),
            _ => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: function-set range must be a tracked finite set, interval, record domain, SUBSET domain, Seq domain, nested function set, or symbolic numeric domain, got {self:?}"
            ))),
        }
    }

    fn validate_seq_base(&self, context: &str) -> Result<(), TmirError> {
        if let AggregateShape::SetBitmask { universe, .. } = self {
            if *universe == SetBitmaskUniverse::Unknown {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask sequence base requires exact universe metadata"
                )));
            }
        }
        match self {
            AggregateShape::Set { .. }
            | AggregateShape::ExactIntSet { .. }
            | AggregateShape::SetBitmask { .. }
            | AggregateShape::BoundedSet { .. }
            | AggregateShape::FiniteSet
            | AggregateShape::Interval { .. }
            | AggregateShape::RecordSet { .. }
            | AggregateShape::SymbolicDomain(_)
            | AggregateShape::Powerset { .. }
            | AggregateShape::FunctionSet { .. }
            | AggregateShape::SeqSet { .. } => Ok(()),
            _ => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: base must be a set/domain shape, got {self:?}"
            ))),
        }
    }

    fn function_value_shape(&self) -> Option<AggregateShape> {
        match self {
            AggregateShape::Function {
                value: Some(value), ..
            } => Some((**value).clone()),
            _ => None,
        }
    }

    fn function_domain_shape(&self) -> Option<AggregateShape> {
        let AggregateShape::Function { len, domain_lo, .. } = self else {
            return None;
        };
        if let Some(lo) = domain_lo {
            if *len == 0 {
                return Some(AggregateShape::Interval {
                    lo: *lo,
                    hi: lo.checked_sub(1)?,
                });
            }
            let hi = lo.checked_add(i64::from(*len) - 1)?;
            Some(AggregateShape::Interval { lo: *lo, hi })
        } else {
            Some(AggregateShape::BoundedSet {
                max_len: *len,
                element: None,
            })
        }
    }

    fn compact_slot_count(&self) -> Option<u32> {
        match self {
            AggregateShape::Scalar(_)
            | AggregateShape::ScalarIntDomain { .. }
            | AggregateShape::SetBitmask { .. } => Some(1),
            AggregateShape::Function {
                len,
                value: Some(value),
                ..
            } => value.compact_slot_count()?.checked_mul(*len),
            AggregateShape::Record { fields } => {
                let mut total = 0_u32;
                for (_, shape) in fields {
                    let shape = shape.as_deref()?;
                    total = total.checked_add(shape.compact_slot_count()?)?;
                }
                Some(total)
            }
            AggregateShape::Sequence { extent, element } => {
                let capacity = extent.capacity();
                if capacity == 0 {
                    return Some(1);
                }
                element
                    .as_deref()?
                    .compact_slot_count()?
                    .checked_mul(capacity)?
                    .checked_add(1)
            }
            AggregateShape::RecordSet { fields } => u32::try_from(fields.len()).ok(),
            _ => None,
        }
    }

    fn materialized_return_slot_count(&self) -> Option<u32> {
        let len = match self {
            AggregateShape::Interval { lo, hi } => interval_len_u32(*lo, *hi)?,
            AggregateShape::ExactIntSet { values } => u32::try_from(values.len()).ok()?,
            AggregateShape::Set { len: 0, .. } => 0,
            AggregateShape::BoundedSet {
                max_len,
                element: Some(element),
            } if Self::is_materialized_return_scalar_element(element) => *max_len,
            _ => return None,
        };
        len.checked_add(1)
    }

    fn is_materialized_return_scalar_element(shape: &AggregateShape) -> bool {
        matches!(
            shape,
            AggregateShape::Scalar(_) | AggregateShape::ScalarIntDomain { .. }
        )
    }

    fn fixed_width_slot_count_for_shape_completion(&self) -> Option<u32> {
        self.compact_slot_count()
            .or_else(|| self.materialized_return_slot_count())
    }

    fn contains_unknown_set_bitmask(&self) -> bool {
        match self {
            AggregateShape::SetBitmask {
                universe: SetBitmaskUniverse::Unknown,
                ..
            } => true,
            AggregateShape::Function { value, .. } => value
                .as_deref()
                .is_some_and(AggregateShape::contains_unknown_set_bitmask),
            AggregateShape::Record { fields } => fields.iter().any(|(_, field)| {
                field
                    .as_deref()
                    .is_some_and(AggregateShape::contains_unknown_set_bitmask)
            }),
            AggregateShape::RecordSet { fields } => fields
                .iter()
                .any(|(_, field)| field.contains_unknown_set_bitmask()),
            AggregateShape::Powerset { base } | AggregateShape::SeqSet { base } => {
                base.contains_unknown_set_bitmask()
            }
            AggregateShape::FunctionSet { domain, range } => {
                domain.contains_unknown_set_bitmask() || range.contains_unknown_set_bitmask()
            }
            AggregateShape::Set { element, .. }
            | AggregateShape::BoundedSet { element, .. }
            | AggregateShape::Sequence { element, .. } => element
                .as_deref()
                .is_some_and(AggregateShape::contains_unknown_set_bitmask),
            AggregateShape::StateValue
            | AggregateShape::Scalar(_)
            | AggregateShape::ScalarIntDomain { .. }
            | AggregateShape::SymbolicDomain(_)
            | AggregateShape::Interval { .. }
            | AggregateShape::ExactIntSet { .. }
            | AggregateShape::SetBitmask { .. }
            | AggregateShape::FiniteSet => false,
        }
    }

    fn record_field(&self, field: NameId) -> Option<(u32, Option<AggregateShape>)> {
        let AggregateShape::Record { fields } = self else {
            return None;
        };
        fields.iter().enumerate().find_map(|(idx, (name, shape))| {
            if *name == field {
                Some((
                    u32::try_from(idx).expect("record field index must fit in u32"),
                    shape.as_deref().cloned(),
                ))
            } else {
                None
            }
        })
    }

    fn compact_record_field(&self, field: NameId) -> Option<(u32, Option<AggregateShape>)> {
        let AggregateShape::Record { fields } = self else {
            return None;
        };
        let mut offset = 0_u32;
        for (name, shape) in fields {
            let shape = shape.as_deref()?;
            if *name == field {
                return Some((offset, Some(shape.clone())));
            }
            offset = offset.checked_add(shape.compact_slot_count()?)?;
        }
        None
    }

    /// Resolve a record field from a scalar selector used by bytecode.
    ///
    /// Real next-state bytecode uses two encodings for record paths:
    /// - zero-based field indices in `FuncApply` / `FuncExcept` helper paths
    /// - interned `NameId` immediates in some constant-pool-driven paths
    ///
    /// Prefer the positional form when the selector is in-bounds; record
    /// labels themselves are symbolic, so a small integer selector is more
    /// likely to be a field index than a real field name id.
    fn record_field_from_scalar_key(
        &self,
        key: i64,
        mode: RecordSelectorMode,
    ) -> Option<(NameId, u32, Option<AggregateShape>)> {
        let AggregateShape::Record { fields } = self else {
            return None;
        };

        if mode == RecordSelectorMode::FieldName {
            let field = NameId(u32::try_from(key).ok()?);
            return self
                .record_field(field)
                .map(|(idx, shape)| (field, idx, shape));
        }

        if let Ok(idx) = usize::try_from(key) {
            if let Some((name, shape)) = fields.get(idx) {
                return Some((
                    *name,
                    u32::try_from(idx).expect("record field index must fit in u32"),
                    shape.as_deref().cloned(),
                ));
            }
        }

        let field = NameId(u32::try_from(key).ok()?);
        self.record_field(field)
            .map(|(idx, shape)| (field, idx, shape))
    }

    fn with_record_field_shape(
        &self,
        field: NameId,
        new_shape: Option<AggregateShape>,
    ) -> AggregateShape {
        match self {
            AggregateShape::Record { fields } => AggregateShape::Record {
                fields: fields
                    .iter()
                    .map(|(name, shape)| {
                        if *name == field {
                            (*name, new_shape.clone().map(Box::new))
                        } else {
                            (*name, shape.clone())
                        }
                    })
                    .collect(),
            },
            _ => self.clone(),
        }
    }

    fn record_from_record_set_domains(fields: &[(NameId, AggregateShape)]) -> AggregateShape {
        // Runtime records use the canonical NameId order; record-set domains are
        // stored in membership-check order, which may differ by cardinality.
        let mut record_fields: Vec<_> = fields
            .iter()
            .map(|(name, domain_shape)| {
                (
                    *name,
                    Self::record_value_shape_from_domain(domain_shape).map(Box::new),
                )
            })
            .collect();
        record_fields.sort_by_key(|(name, _)| *name);
        AggregateShape::Record {
            fields: record_fields,
        }
    }

    fn record_value_shape_from_domain(domain_shape: &AggregateShape) -> Option<AggregateShape> {
        if let Some(shape) = scalar_int_domain_shape_from_domain(domain_shape) {
            return Some(shape);
        }
        match domain_shape {
            AggregateShape::Interval { .. } | AggregateShape::SymbolicDomain(_) => {
                Some(AggregateShape::Scalar(ScalarShape::Int))
            }
            AggregateShape::Set {
                element: Some(element),
                ..
            } => Some((**element).clone()),
            _ => None,
        }
    }

    fn function_from_function_set_domains(
        domain_shape: &AggregateShape,
        range_shape: &AggregateShape,
    ) -> Result<AggregateShape, TmirError> {
        let len = domain_shape.tracked_len().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "function-set domain cardinality is not statically known: {domain_shape:?}"
            ))
        })?;
        Ok(AggregateShape::Function {
            len,
            domain_lo: dense_ordered_int_domain_lo(domain_shape, len),
            value: Self::function_value_shape_from_range(range_shape).map(Box::new),
        })
    }

    fn function_value_shape_from_range(range_shape: &AggregateShape) -> Option<AggregateShape> {
        if let Some(shape) = scalar_int_domain_shape_from_domain(range_shape) {
            return Some(shape);
        }
        match range_shape {
            AggregateShape::Interval { .. } | AggregateShape::SymbolicDomain(_) => {
                Some(AggregateShape::Scalar(ScalarShape::Int))
            }
            AggregateShape::RecordSet { fields } => {
                Some(Self::record_from_record_set_domains(fields))
            }
            AggregateShape::Powerset { base } => Some((**base).clone()),
            AggregateShape::FunctionSet { domain, range } => {
                Self::function_from_function_set_domains(domain, range).ok()
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FuncDefShapeFrame {
    rd: u8,
    r_binding: u8,
    function_shape: AggregateShape,
}

#[derive(Clone, Default, PartialEq, Eq)]
struct ShapeSummary {
    aggregate_shapes: HashMap<u8, AggregateShape>,
    const_scalar_values: HashMap<u8, i64>,
    funcdef_stack: Vec<FuncDefShapeFrame>,
    return_shape: Option<AggregateShape>,
    saw_return: bool,
}

impl ShapeSummary {
    fn set_shape(&mut self, reg: u8, shape: AggregateShape) {
        self.aggregate_shapes.insert(reg, shape);
    }

    fn clear_shape(&mut self, reg: u8) {
        self.aggregate_shapes.remove(&reg);
    }

    fn set_scalar(&mut self, reg: u8, value: i64, shape: AggregateShape) {
        self.const_scalar_values.insert(reg, value);
        self.set_shape(reg, shape);
    }

    fn clear_scalar(&mut self, reg: u8) {
        self.const_scalar_values.remove(&reg);
    }

    fn set_return_shape(&mut self, shape: Option<AggregateShape>) {
        if !self.saw_return {
            self.return_shape = shape;
            self.saw_return = true;
        } else if self.return_shape != shape {
            self.return_shape = None;
        }
    }
}

fn uniform_shape(shapes: &[Option<AggregateShape>]) -> Option<Box<AggregateShape>> {
    let first = shapes.first()?.as_ref()?;
    if shapes
        .iter()
        .all(|shape| shape.as_ref().is_some_and(|shape| shape == first))
    {
        Some(Box::new(first.clone()))
    } else {
        None
    }
}

fn call_result_summary_shape(raw: Option<AggregateShape>) -> Option<AggregateShape> {
    Ctx::compact_return_abi_shape(raw.clone()).or(raw)
}

fn sequence_head_shape(seq: Option<&AggregateShape>) -> Option<AggregateShape> {
    match seq {
        Some(AggregateShape::Sequence {
            element: Some(element),
            ..
        }) => Some((**element).clone()),
        _ => None,
    }
}

fn sequence_tail_shape(seq: Option<&AggregateShape>) -> Option<AggregateShape> {
    match seq {
        Some(AggregateShape::Sequence { extent, element }) => {
            let extent = match extent {
                SequenceExtent::Exact(len) => SequenceExtent::Exact(len.checked_sub(1)?),
                SequenceExtent::Capacity(capacity) => SequenceExtent::Capacity(*capacity),
            };
            let exact_count = extent.exact_count();
            Some(AggregateShape::Sequence {
                extent,
                element: if exact_count == Some(0) {
                    None
                } else {
                    element.clone()
                },
            })
        }
        _ => None,
    }
}

fn sequence_append_shape(
    seq: Option<&AggregateShape>,
    elem: Option<&AggregateShape>,
) -> Option<AggregateShape> {
    let Some(AggregateShape::Sequence { extent, element }) = seq else {
        return None;
    };
    let extent = match extent {
        SequenceExtent::Exact(len) => SequenceExtent::Exact(len.checked_add(1)?),
        SequenceExtent::Capacity(capacity) => SequenceExtent::Capacity(*capacity),
    };
    let result_element = match (element.as_deref(), elem) {
        (None, Some(elem)) if matches!(extent, SequenceExtent::Exact(1)) => {
            Some(Box::new(elem.clone()))
        }
        (Some(existing), None) => Some(Box::new(existing.clone())),
        (Some(existing), Some(appended)) => {
            merge_compatible_shapes(Some(existing), Some(appended)).map(Box::new)
        }
        _ => None,
    };
    Some(AggregateShape::Sequence {
        extent,
        element: result_element,
    })
}

fn record_get_field_name(constants: Option<&ConstantPool>, field_idx: u16) -> Option<NameId> {
    let pool = constants?;
    if usize::from(field_idx) >= pool.field_ids().len() {
        return None;
    }
    Some(NameId(pool.get_field_id(field_idx)))
}

fn record_get_shape(
    record: Option<&AggregateShape>,
    constants: Option<&ConstantPool>,
    field_idx: u16,
) -> Option<AggregateShape> {
    let Some(AggregateShape::Record { fields }) = record else {
        return None;
    };
    if let Some(field_name) = record_get_field_name(constants, field_idx) {
        return fields.iter().find_map(|(name, shape)| {
            (*name == field_name)
                .then(|| shape.as_deref().cloned())
                .flatten()
        });
    }
    fields
        .get(usize::from(field_idx))
        .and_then(|(_, shape)| shape.as_deref().cloned())
}

fn sequence_element_shape(seq: Option<&AggregateShape>) -> Option<AggregateShape> {
    match seq {
        Some(AggregateShape::Sequence {
            element: Some(element),
            ..
        }) => Some((**element).clone()),
        _ => None,
    }
}

fn int_value_i64(value: &tla_value::Value) -> Option<i64> {
    match value {
        tla_value::Value::SmallInt(n) => Some(*n),
        tla_value::Value::Int(n) => n.to_i64(),
        _ => None,
    }
}

fn dense_ordered_int_values_lo<'a, I>(values: I) -> Option<(i64, u32)>
where
    I: IntoIterator<Item = &'a tla_value::Value>,
{
    let mut iter = values.into_iter();
    let first = int_value_i64(iter.next()?)?;
    let mut len = 1_u32;
    for value in iter {
        let expected = first.checked_add(i64::from(len))?;
        if int_value_i64(value)? != expected {
            return None;
        }
        len = len.checked_add(1)?;
    }
    Some((first, len))
}

fn dense_ordered_i64_values_lo(values: &[i64]) -> Option<(i64, u32)> {
    let first = *values.first()?;
    for (idx, value) in values.iter().enumerate() {
        if *value != first.checked_add(i64::try_from(idx).ok()?)? {
            return None;
        }
    }
    Some((first, u32::try_from(values.len()).ok()?))
}

fn dense_ordered_int_domain_lo(domain: &AggregateShape, expected_len: u32) -> Option<i64> {
    let (lo, len) = match domain {
        AggregateShape::Interval { lo, hi } => (*lo, interval_len_u32(*lo, *hi)?),
        AggregateShape::ExactIntSet { values } => dense_ordered_i64_values_lo(values)?,
        _ => return None,
    };
    (len == expected_len).then_some(lo)
}

fn exact_int_domain_universe(domain: &AggregateShape) -> Option<(u32, SetBitmaskUniverse)> {
    let (universe_len, universe) = match domain {
        AggregateShape::Interval { lo, hi } => (
            interval_len_u32(*lo, *hi)?,
            SetBitmaskUniverse::IntRange { lo: *lo },
        ),
        AggregateShape::ExactIntSet { values } => {
            let len = u32::try_from(values.len()).ok()?;
            let universe = if let Some((lo, dense_len)) = dense_ordered_i64_values_lo(values) {
                if dense_len == len {
                    SetBitmaskUniverse::IntRange { lo }
                } else {
                    SetBitmaskUniverse::ExplicitInt(values.clone())
                }
            } else {
                SetBitmaskUniverse::ExplicitInt(values.clone())
            };
            (len, universe)
        }
        AggregateShape::SetBitmask {
            universe_len,
            universe,
        } if !matches!(
            universe,
            SetBitmaskUniverse::Exact(_) | SetBitmaskUniverse::Unknown
        ) =>
        {
            (*universe_len, universe.clone())
        }
        _ => return None,
    };
    set_bitmask_valid_mask(universe_len)?;
    Some((universe_len, universe))
}

fn scalar_int_domain_shape_from_domain(domain: &AggregateShape) -> Option<AggregateShape> {
    let (universe_len, universe) = exact_int_domain_universe(domain)?;
    Some(AggregateShape::ScalarIntDomain {
        universe_len,
        universe,
    })
}

fn binding_shape_from_domain(domain: &AggregateShape) -> Option<AggregateShape> {
    if let Some(shape) = scalar_int_domain_shape_from_domain(domain) {
        return Some(shape);
    }
    match domain {
        AggregateShape::SymbolicDomain(_) => Some(AggregateShape::Scalar(ScalarShape::Int)),
        AggregateShape::Set {
            element: Some(element),
            ..
        }
        | AggregateShape::BoundedSet {
            element: Some(element),
            ..
        } => Some((**element).clone()),
        _ => None,
    }
}

fn funcdef_contiguous_int_domain_lo(domain: &AggregateShape, len: u32) -> Option<i64> {
    dense_ordered_int_domain_lo(domain, len)
}

fn funcdef_function_shape_from_domain(domain: &AggregateShape) -> Option<AggregateShape> {
    let len = domain
        .tracked_len()
        .or_else(|| domain.finite_set_len_bound())?;
    Some(AggregateShape::Function {
        len,
        domain_lo: funcdef_contiguous_int_domain_lo(domain, len),
        value: None,
    })
}

fn funcdef_binding_shape_from_domain(domain: &AggregateShape) -> Option<AggregateShape> {
    binding_shape_from_domain(domain)
}

fn apply_funcdef_begin_shape_transfer(
    summary: &mut ShapeSummary,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
) {
    summary.clear_scalar(rd);
    summary.clear_scalar(r_binding);
    let Some(domain_shape) = summary.aggregate_shapes.get(&r_domain).cloned() else {
        summary.clear_shape(rd);
        summary.clear_shape(r_binding);
        return;
    };

    if let Some(binding_shape) = funcdef_binding_shape_from_domain(&domain_shape) {
        summary.set_shape(r_binding, binding_shape);
    } else {
        summary.clear_shape(r_binding);
    }

    if let Some(function_shape) = funcdef_function_shape_from_domain(&domain_shape) {
        summary.set_shape(rd, function_shape.clone());
        summary.funcdef_stack.push(FuncDefShapeFrame {
            rd,
            r_binding,
            function_shape,
        });
    } else {
        summary.clear_shape(rd);
    }
}

fn apply_binding_begin_shape_transfer(summary: &mut ShapeSummary, r_binding: u8, r_domain: u8) {
    summary.clear_scalar(r_binding);
    let Some(domain_shape) = summary.aggregate_shapes.get(&r_domain).cloned() else {
        summary.clear_shape(r_binding);
        return;
    };
    if let Some(binding_shape) = binding_shape_from_domain(&domain_shape) {
        summary.set_shape(r_binding, binding_shape);
    } else {
        summary.clear_shape(r_binding);
    }
}

fn apply_loop_next_shape_transfer(summary: &mut ShapeSummary, r_binding: u8, r_body: u8) {
    let Some(frame) = summary.funcdef_stack.last().cloned() else {
        return;
    };
    if frame.r_binding != r_binding {
        return;
    }
    summary.funcdef_stack.pop();

    let body_shape = summary.aggregate_shapes.get(&r_body).cloned();
    let mut function_shape = match summary.aggregate_shapes.get(&frame.rd).cloned() {
        Some(AggregateShape::Function { len, domain_lo, .. }) => AggregateShape::Function {
            len,
            domain_lo,
            value: None,
        },
        _ => frame.function_shape,
    };
    if let AggregateShape::Function { value, .. } = &mut function_shape {
        *value = body_shape.map(Box::new);
    }
    summary.clear_scalar(frame.rd);
    summary.set_shape(frame.rd, function_shape);
}

fn function_apply_shape_from_summary(
    summary: &ShapeSummary,
    func_reg: u8,
    arg_reg: u8,
) -> Option<AggregateShape> {
    if let Some(path_raw) = summary.const_scalar_values.get(&arg_reg).copied() {
        let selector_mode = record_selector_mode(summary.aggregate_shapes.get(&arg_reg));
        if let Some((_field_name, _field_idx, field_shape)) = summary
            .aggregate_shapes
            .get(&func_reg)
            .and_then(|shape| shape.record_field_from_scalar_key(path_raw, selector_mode))
        {
            return field_shape;
        }
    }

    match summary.aggregate_shapes.get(&func_reg)? {
        AggregateShape::Function {
            value: Some(value), ..
        } => Some((**value).clone()),
        AggregateShape::Sequence {
            element: Some(element),
            ..
        } => Some((**element).clone()),
        _ => None,
    }
}

fn function_except_shape_from_summary(
    summary: &ShapeSummary,
    func_reg: u8,
    path_reg: u8,
    val_reg: u8,
) -> Option<AggregateShape> {
    let func_shape = summary.aggregate_shapes.get(&func_reg)?.clone();
    if let Some(path_raw) = summary.const_scalar_values.get(&path_reg).copied() {
        let selector_mode = record_selector_mode(summary.aggregate_shapes.get(&path_reg));
        if let Some((field_name, _field_idx, _field_shape)) =
            func_shape.record_field_from_scalar_key(path_raw, selector_mode)
        {
            return Some(func_shape.with_record_field_shape(
                field_name,
                summary.aggregate_shapes.get(&val_reg).cloned(),
            ));
        }
    }
    Some(func_shape)
}

fn record_selector_mode(shape: Option<&AggregateShape>) -> RecordSelectorMode {
    match shape {
        Some(AggregateShape::Scalar(ScalarShape::String)) => RecordSelectorMode::FieldName,
        _ => RecordSelectorMode::Positional,
    }
}

fn merge_compatible_shapes(
    left: Option<&AggregateShape>,
    right: Option<&AggregateShape>,
) -> Option<AggregateShape> {
    let (Some(left), Some(right)) = (left, right) else {
        return None;
    };
    if left == right
        && !matches!(
            left,
            AggregateShape::SetBitmask {
                universe: SetBitmaskUniverse::Unknown,
                ..
            }
        )
    {
        return Some(left.clone());
    }

    match (left, right) {
        (AggregateShape::Scalar(left), AggregateShape::Scalar(right)) if left == right => {
            Some(AggregateShape::Scalar(left.clone()))
        }
        (
            AggregateShape::ScalarIntDomain {
                universe_len: left_len,
                universe: left_universe,
            },
            AggregateShape::ScalarIntDomain {
                universe_len: right_len,
                universe: right_universe,
            },
        ) if left_len == right_len && left_universe == right_universe => {
            Some(AggregateShape::ScalarIntDomain {
                universe_len: *left_len,
                universe: left_universe.clone(),
            })
        }
        (AggregateShape::Scalar(ScalarShape::Int), AggregateShape::ScalarIntDomain { .. })
        | (AggregateShape::ScalarIntDomain { .. }, AggregateShape::Scalar(ScalarShape::Int)) => {
            Some(AggregateShape::Scalar(ScalarShape::Int))
        }
        (
            AggregateShape::SetBitmask {
                universe_len: left_len,
                universe: left_universe,
            },
            AggregateShape::SetBitmask {
                universe_len: right_len,
                universe: right_universe,
            },
        ) if left_len == right_len
            && !matches!(left_universe, SetBitmaskUniverse::Unknown)
            && left_universe == right_universe =>
        {
            Some(left.clone())
        }
        (AggregateShape::SetBitmask { .. }, _) | (_, AggregateShape::SetBitmask { .. }) => None,
        (
            AggregateShape::ExactIntSet { values: left },
            AggregateShape::ExactIntSet { values: right },
        ) => {
            let max_len = left.len().max(right.len());
            let Ok(max_len) = u32::try_from(max_len) else {
                return Some(AggregateShape::FiniteSet);
            };
            if left.len() == right.len() {
                Some(AggregateShape::Set {
                    len: max_len,
                    element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                })
            } else {
                Some(bounded_set_or_finite_with_element(
                    max_len,
                    Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                ))
            }
        }
        (left, right) if left.is_finite_set_shape() && right.is_finite_set_shape() => {
            match (left.finite_set_len_bound(), right.finite_set_len_bound()) {
                (Some(left_bound), Some(right_bound)) => Some(bounded_set_or_finite_with_element(
                    left_bound.max(right_bound),
                    merge_finite_set_element_shape(left, right),
                )),
                _ => Some(AggregateShape::FiniteSet),
            }
        }
        (
            AggregateShape::Function {
                len: left_len,
                value: left_value,
                domain_lo: left_domain_lo,
            },
            AggregateShape::Function {
                len: right_len,
                value: right_value,
                domain_lo: right_domain_lo,
            },
        ) if left_len == right_len && left_domain_lo == right_domain_lo => {
            Some(AggregateShape::Function {
                len: *left_len,
                domain_lo: *left_domain_lo,
                value: merge_compatible_shapes(left_value.as_deref(), right_value.as_deref())
                    .map(Box::new),
            })
        }
        (
            AggregateShape::Sequence {
                extent: left_extent,
                element: left_element,
            },
            AggregateShape::Sequence {
                extent: right_extent,
                element: right_element,
            },
        ) if left_extent == right_extent => Some(AggregateShape::Sequence {
            extent: *left_extent,
            element: merge_compatible_shapes(left_element.as_deref(), right_element.as_deref())
                .map(Box::new),
        }),
        (AggregateShape::Record { fields: left }, AggregateShape::Record { fields: right })
            if left.len() == right.len()
                && left.iter().all(|(left_name, _)| {
                    right.iter().any(|(right_name, _)| right_name == left_name)
                }) =>
        {
            Some(AggregateShape::Record {
                fields: left
                    .iter()
                    .map(|(name, left_shape)| {
                        let (_, right_shape) = right
                            .iter()
                            .find(|(right_name, _)| right_name == name)
                            .expect("record merge guard should ensure matching field names");
                        (
                            *name,
                            merge_compatible_shapes(left_shape.as_deref(), right_shape.as_deref())
                                .map(Box::new),
                        )
                    })
                    .collect(),
            })
        }
        _ => None,
    }
}

fn cond_move_result_shape(
    shapes: &HashMap<u8, AggregateShape>,
    const_scalars: &HashMap<u8, i64>,
    rd: u8,
    cond: u8,
    rs: u8,
) -> Option<AggregateShape> {
    if let Some(cond_value) = const_scalars.get(&cond) {
        return if *cond_value != 0 {
            shapes.get(&rs).cloned()
        } else {
            shapes.get(&rd).cloned()
        };
    }
    merge_compatible_shapes(shapes.get(&rd), shapes.get(&rs))
}

fn merge_callee_arg_shapes(
    map: &mut HashMap<u16, Vec<Option<AggregateShape>>>,
    op_idx: u16,
    callee_name: &str,
    incoming: Vec<Option<AggregateShape>>,
) -> Result<bool, TmirError> {
    use std::collections::hash_map::Entry;

    match map.entry(op_idx) {
        Entry::Vacant(entry) => {
            entry.insert(incoming);
            Ok(true)
        }
        Entry::Occupied(mut entry) => {
            let existing = entry.get_mut();
            let merged = if existing.len() != incoming.len() {
                for (idx, shape) in existing.iter().enumerate() {
                    if contains_compact_set_bitmask(shape.as_ref()) {
                        return Err(incompatible_compact_setbitmask_callee_arg_error(
                            op_idx,
                            callee_name,
                            idx,
                            shape.as_ref(),
                            None,
                        ));
                    }
                    if contains_compact_record_or_sequence_arg(shape.as_ref()) {
                        return Err(incompatible_compact_aggregate_callee_arg_error(
                            op_idx,
                            callee_name,
                            idx,
                            shape.as_ref(),
                            None,
                        ));
                    }
                }
                for (idx, shape) in incoming.iter().enumerate() {
                    if contains_compact_set_bitmask(shape.as_ref()) {
                        return Err(incompatible_compact_setbitmask_callee_arg_error(
                            op_idx,
                            callee_name,
                            idx,
                            None,
                            shape.as_ref(),
                        ));
                    }
                    if contains_compact_record_or_sequence_arg(shape.as_ref()) {
                        return Err(incompatible_compact_aggregate_callee_arg_error(
                            op_idx,
                            callee_name,
                            idx,
                            None,
                            shape.as_ref(),
                        ));
                    }
                }
                vec![None; incoming.len()]
            } else {
                let mut merged = Vec::with_capacity(incoming.len());
                for (idx, (current, incoming)) in existing.iter().zip(incoming.iter()).enumerate() {
                    let shape = merge_compatible_shapes(current.as_ref(), incoming.as_ref());
                    if !compact_set_bitmask_merge_preserved(
                        current.as_ref(),
                        incoming.as_ref(),
                        shape.as_ref(),
                    ) {
                        return Err(incompatible_compact_setbitmask_callee_arg_error(
                            op_idx,
                            callee_name,
                            idx,
                            current.as_ref(),
                            incoming.as_ref(),
                        ));
                    }
                    if !compact_record_sequence_arg_merge_preserved(
                        current.as_ref(),
                        incoming.as_ref(),
                        shape.as_ref(),
                    ) {
                        return Err(incompatible_compact_aggregate_callee_arg_error(
                            op_idx,
                            callee_name,
                            idx,
                            current.as_ref(),
                            incoming.as_ref(),
                        ));
                    }
                    merged.push(shape);
                }
                merged
            };
            if *existing == merged {
                Ok(false)
            } else {
                *existing = merged;
                Ok(true)
            }
        }
    }
}

fn contains_compact_record_or_sequence_arg(shape: Option<&AggregateShape>) -> bool {
    let Some(shape) = shape else {
        return false;
    };
    if matches!(
        shape,
        AggregateShape::Record { .. } | AggregateShape::Sequence { .. }
    ) && Ctx::compact_return_abi_shape(Some(shape.clone())).is_some()
    {
        return true;
    }
    match shape {
        AggregateShape::Function { value, .. } => {
            contains_compact_record_or_sequence_arg(value.as_deref())
        }
        AggregateShape::Record { fields } => fields
            .iter()
            .any(|(_, field)| contains_compact_record_or_sequence_arg(field.as_deref())),
        AggregateShape::RecordSet { fields } => fields
            .iter()
            .any(|(_, field)| contains_compact_record_or_sequence_arg(Some(field))),
        AggregateShape::Powerset { base } | AggregateShape::SeqSet { base } => {
            contains_compact_record_or_sequence_arg(Some(base.as_ref()))
        }
        AggregateShape::FunctionSet { domain, range } => {
            contains_compact_record_or_sequence_arg(Some(domain.as_ref()))
                || contains_compact_record_or_sequence_arg(Some(range.as_ref()))
        }
        AggregateShape::Set { element, .. }
        | AggregateShape::BoundedSet { element, .. }
        | AggregateShape::Sequence { element, .. } => {
            contains_compact_record_or_sequence_arg(element.as_deref())
        }
        AggregateShape::StateValue
        | AggregateShape::Scalar(_)
        | AggregateShape::ScalarIntDomain { .. }
        | AggregateShape::SetBitmask { .. }
        | AggregateShape::SymbolicDomain(_)
        | AggregateShape::Interval { .. }
        | AggregateShape::ExactIntSet { .. }
        | AggregateShape::FiniteSet => false,
    }
}

fn contains_compact_set_bitmask(shape: Option<&AggregateShape>) -> bool {
    let Some(shape) = shape else {
        return false;
    };
    match shape {
        AggregateShape::SetBitmask { .. } => true,
        AggregateShape::Function { value, .. } => contains_compact_set_bitmask(value.as_deref()),
        AggregateShape::Record { fields } => fields
            .iter()
            .any(|(_, field)| contains_compact_set_bitmask(field.as_deref())),
        AggregateShape::RecordSet { fields } => fields
            .iter()
            .any(|(_, field)| contains_compact_set_bitmask(Some(field))),
        AggregateShape::Powerset { base } | AggregateShape::SeqSet { base } => {
            contains_compact_set_bitmask(Some(base.as_ref()))
        }
        AggregateShape::FunctionSet { domain, range } => {
            contains_compact_set_bitmask(Some(domain.as_ref()))
                || contains_compact_set_bitmask(Some(range.as_ref()))
        }
        AggregateShape::Set { element, .. }
        | AggregateShape::BoundedSet { element, .. }
        | AggregateShape::Sequence { element, .. } => {
            contains_compact_set_bitmask(element.as_deref())
        }
        AggregateShape::StateValue
        | AggregateShape::Scalar(_)
        | AggregateShape::ScalarIntDomain { .. }
        | AggregateShape::SymbolicDomain(_)
        | AggregateShape::Interval { .. }
        | AggregateShape::ExactIntSet { .. }
        | AggregateShape::FiniteSet => false,
    }
}

fn compact_record_sequence_arg_merge_preserved(
    left: Option<&AggregateShape>,
    right: Option<&AggregateShape>,
    merged: Option<&AggregateShape>,
) -> bool {
    let left_has_compact = contains_compact_record_or_sequence_arg(left);
    let right_has_compact = contains_compact_record_or_sequence_arg(right);
    if !left_has_compact && !right_has_compact {
        return true;
    }

    let left_abi = left_has_compact
        .then(|| left.and_then(|shape| Ctx::compact_return_abi_shape(Some(shape.clone()))))
        .flatten();
    let right_abi = right_has_compact
        .then(|| right.and_then(|shape| Ctx::compact_return_abi_shape(Some(shape.clone()))))
        .flatten();
    if (left_has_compact && left_abi.is_none()) || (right_has_compact && right_abi.is_none()) {
        return false;
    }

    let Some(merged_abi) =
        merged.and_then(|shape| Ctx::compact_return_abi_shape(Some(shape.clone())))
    else {
        return false;
    };
    if let Some(left_abi) = left_abi.as_ref() {
        if !Ctx::same_compact_physical_layout(left_abi, &merged_abi) {
            return false;
        }
    }
    if let Some(right_abi) = right_abi.as_ref() {
        if !Ctx::same_compact_physical_layout(right_abi, &merged_abi) {
            return false;
        }
    }
    true
}

fn compact_set_bitmask_merge_preserved(
    left: Option<&AggregateShape>,
    right: Option<&AggregateShape>,
    merged: Option<&AggregateShape>,
) -> bool {
    if !contains_compact_set_bitmask(left) && !contains_compact_set_bitmask(right) {
        return true;
    }

    match (left, right, merged) {
        (
            Some(AggregateShape::SetBitmask { .. }),
            Some(AggregateShape::SetBitmask { .. }),
            Some(AggregateShape::SetBitmask { .. }),
        ) => true,
        (
            Some(AggregateShape::Function {
                value: left_value, ..
            }),
            Some(AggregateShape::Function {
                value: right_value, ..
            }),
            Some(AggregateShape::Function {
                value: merged_value,
                ..
            }),
        ) => compact_set_bitmask_merge_preserved(
            left_value.as_deref(),
            right_value.as_deref(),
            merged_value.as_deref(),
        ),
        (
            Some(AggregateShape::Sequence {
                element: left_element,
                ..
            }),
            Some(AggregateShape::Sequence {
                element: right_element,
                ..
            }),
            Some(AggregateShape::Sequence {
                element: merged_element,
                ..
            }),
        ) => compact_set_bitmask_merge_preserved(
            left_element.as_deref(),
            right_element.as_deref(),
            merged_element.as_deref(),
        ),
        (
            Some(AggregateShape::Set {
                element: left_element,
                ..
            }),
            Some(AggregateShape::Set {
                element: right_element,
                ..
            }),
            Some(AggregateShape::Set {
                element: merged_element,
                ..
            }),
        ) => compact_set_bitmask_merge_preserved(
            left_element.as_deref(),
            right_element.as_deref(),
            merged_element.as_deref(),
        ),
        (
            Some(AggregateShape::ExactIntSet {
                values: left_values,
            }),
            Some(AggregateShape::ExactIntSet {
                values: right_values,
            }),
            Some(AggregateShape::ExactIntSet {
                values: merged_values,
            }),
        ) if left_values == right_values && left_values == merged_values => true,
        (
            Some(AggregateShape::Record { fields: left }),
            Some(AggregateShape::Record { fields: right }),
            Some(AggregateShape::Record { fields: merged }),
        ) if left.len() == right.len()
            && left.len() == merged.len()
            && left.iter().zip(right.iter()).zip(merged.iter()).all(
                |(((left_name, _), (right_name, _)), (merged_name, _))| {
                    left_name == right_name && left_name == merged_name
                },
            ) =>
        {
            left.iter().zip(right.iter()).zip(merged.iter()).all(
                |(((_, left_shape), (_, right_shape)), (_, merged_shape))| {
                    compact_set_bitmask_merge_preserved(
                        left_shape.as_deref(),
                        right_shape.as_deref(),
                        merged_shape.as_deref(),
                    )
                },
            )
        }
        (
            Some(AggregateShape::RecordSet { fields: left }),
            Some(AggregateShape::RecordSet { fields: right }),
            Some(AggregateShape::RecordSet { fields: merged }),
        ) if left.len() == right.len()
            && left.len() == merged.len()
            && left.iter().zip(right.iter()).zip(merged.iter()).all(
                |(((left_name, _), (right_name, _)), (merged_name, _))| {
                    left_name == right_name && left_name == merged_name
                },
            ) =>
        {
            left.iter().zip(right.iter()).zip(merged.iter()).all(
                |(((_, left_shape), (_, right_shape)), (_, merged_shape))| {
                    compact_set_bitmask_merge_preserved(
                        Some(left_shape),
                        Some(right_shape),
                        Some(merged_shape),
                    )
                },
            )
        }
        (
            Some(AggregateShape::Powerset { base: left_base }),
            Some(AggregateShape::Powerset { base: right_base }),
            Some(AggregateShape::Powerset { base: merged_base }),
        )
        | (
            Some(AggregateShape::SeqSet { base: left_base }),
            Some(AggregateShape::SeqSet { base: right_base }),
            Some(AggregateShape::SeqSet { base: merged_base }),
        ) => compact_set_bitmask_merge_preserved(
            Some(left_base.as_ref()),
            Some(right_base.as_ref()),
            Some(merged_base.as_ref()),
        ),
        (
            Some(AggregateShape::FunctionSet {
                domain: left_domain,
                range: left_range,
            }),
            Some(AggregateShape::FunctionSet {
                domain: right_domain,
                range: right_range,
            }),
            Some(AggregateShape::FunctionSet {
                domain: merged_domain,
                range: merged_range,
            }),
        ) => {
            compact_set_bitmask_merge_preserved(
                Some(left_domain.as_ref()),
                Some(right_domain.as_ref()),
                Some(merged_domain.as_ref()),
            ) && compact_set_bitmask_merge_preserved(
                Some(left_range.as_ref()),
                Some(right_range.as_ref()),
                Some(merged_range.as_ref()),
            )
        }
        _ => false,
    }
}

fn incompatible_compact_setbitmask_callee_arg_error(
    op_idx: u16,
    callee_name: &str,
    arg_idx: usize,
    current: Option<&AggregateShape>,
    incoming: Option<&AggregateShape>,
) -> TmirError {
    TmirError::UnsupportedOpcode(format!(
        "Call arg shape collection for callee {op_idx} ({callee_name}) argument {arg_idx}: incompatible compact SetBitmask callsite shapes: existing={current:?}, incoming={incoming:?}"
    ))
}

fn incompatible_compact_aggregate_callee_arg_error(
    op_idx: u16,
    callee_name: &str,
    arg_idx: usize,
    current: Option<&AggregateShape>,
    incoming: Option<&AggregateShape>,
) -> TmirError {
    TmirError::UnsupportedOpcode(format!(
        "Call arg shape collection for callee {op_idx} ({callee_name}) argument {arg_idx}: incompatible compact aggregate callsite shapes: existing={current:?}, incoming={incoming:?}"
    ))
}

fn interval_convertible_to_set_bitmask(
    lo: i64,
    hi: i64,
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> bool {
    if hi < lo {
        return true;
    }
    let Some(count) = hi.checked_sub(lo).and_then(|span| span.checked_add(1)) else {
        return false;
    };
    if count > i64::from(universe_len) {
        return false;
    }

    match universe {
        SetBitmaskUniverse::IntRange { lo: universe_lo } => {
            let Some(universe_hi) =
                universe_lo.checked_add(i64::from(universe_len).saturating_sub(1))
            else {
                return false;
            };
            lo >= *universe_lo && hi <= universe_hi
        }
        SetBitmaskUniverse::ExplicitInt(values) => {
            (lo..=hi).all(|elem| values.iter().any(|value| *value == elem))
        }
        SetBitmaskUniverse::Exact(_) | SetBitmaskUniverse::Unknown => false,
    }
}

fn set_bitmask_valid_mask(universe_len: u32) -> Option<i64> {
    match universe_len {
        0 => Some(0),
        1..=62 => Some((1_i64 << universe_len) - 1),
        63 => Some(i64::MAX),
        _ => None,
    }
}

fn shape_convertible_to_set_bitmask_operand(
    shape: &AggregateShape,
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> bool {
    match shape {
        AggregateShape::SetBitmask { .. } => {
            shape.compatible_set_bitmask_universe(universe_len, universe)
        }
        AggregateShape::ExactIntSet { values } => values
            .iter()
            .all(|value| int_value_in_set_bitmask_universe(*value, universe_len, universe)),
        AggregateShape::Set { len, .. } => *len == 0,
        AggregateShape::Interval { lo, hi } => {
            interval_convertible_to_set_bitmask(*lo, *hi, universe_len, universe)
        }
        _ => false,
    }
}

fn int_value_in_set_bitmask_universe(
    value: i64,
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> bool {
    set_bitmask_int_value_index(value, universe_len, universe).is_some()
}

fn set_bitmask_int_value_index(
    value: i64,
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> Option<u32> {
    match universe {
        SetBitmaskUniverse::IntRange { lo } => value
            .checked_sub(*lo)
            .filter(|idx| *idx >= 0 && *idx < i64::from(universe_len))
            .and_then(|idx| u32::try_from(idx).ok()),
        SetBitmaskUniverse::ExplicitInt(values) => values
            .iter()
            .position(|elem| *elem == value)
            .filter(|idx| *idx < usize::try_from(universe_len).unwrap_or(usize::MAX))
            .and_then(|idx| u32::try_from(idx).ok()),
        SetBitmaskUniverse::Exact(_) | SetBitmaskUniverse::Unknown => None,
    }
}

fn set_bitmask_universe_accepts_integer_values(universe: &SetBitmaskUniverse) -> bool {
    matches!(
        universe,
        SetBitmaskUniverse::IntRange { .. } | SetBitmaskUniverse::ExplicitInt(_)
    )
}

fn exact_int_set_mask_for_set_bitmask_universe(
    values: &[i64],
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> Option<i64> {
    let mut mask = 0_i64;
    for value in values {
        let bit_idx = set_bitmask_int_value_index(*value, universe_len, universe)?;
        mask |= 1_i64 << bit_idx;
    }
    Some(mask)
}

fn exact_int_set_partial_mask_for_set_bitmask_universe(
    values: &[i64],
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> Option<i64> {
    if values.is_empty() {
        return Some(0);
    }
    if set_bitmask_valid_mask(universe_len).is_none()
        || !set_bitmask_universe_accepts_integer_values(universe)
    {
        return None;
    }

    let mut mask = 0_i64;
    for value in values {
        if let Some(bit_idx) = set_bitmask_int_value_index(*value, universe_len, universe) {
            mask |= 1_i64 << bit_idx;
        }
    }
    Some(mask)
}

fn interval_mask_for_set_bitmask_universe(
    lo: i64,
    hi: i64,
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> Option<i64> {
    if hi < lo {
        return Some(0);
    }
    if set_bitmask_valid_mask(universe_len).is_none()
        || !set_bitmask_universe_accepts_integer_values(universe)
    {
        return None;
    }

    let mut mask = 0_i64;
    match universe {
        SetBitmaskUniverse::IntRange { lo: universe_lo } => {
            for bit_idx in 0..universe_len {
                let value = universe_lo.checked_add(i64::from(bit_idx))?;
                if value >= lo && value <= hi {
                    mask |= 1_i64 << bit_idx;
                }
            }
        }
        SetBitmaskUniverse::ExplicitInt(values) => {
            for bit_idx in 0..universe_len {
                let value = *values.get(usize::try_from(bit_idx).ok()?)?;
                if value >= lo && value <= hi {
                    mask |= 1_i64 << bit_idx;
                }
            }
        }
        SetBitmaskUniverse::Exact(_) | SetBitmaskUniverse::Unknown => return None,
    }
    Some(mask)
}

fn static_int_base_mask_for_set_bitmask_universe(
    shape: &AggregateShape,
    universe_len: u32,
    universe: &SetBitmaskUniverse,
) -> Option<i64> {
    match shape {
        AggregateShape::ExactIntSet { values } => {
            exact_int_set_partial_mask_for_set_bitmask_universe(values, universe_len, universe)
        }
        AggregateShape::Interval { lo, hi } => {
            interval_mask_for_set_bitmask_universe(*lo, *hi, universe_len, universe)
        }
        AggregateShape::Set { len: 0, .. } => Some(0),
        _ => None,
    }
}

fn set_bitmask_shape_from_convertible_operand_pair(
    left: &AggregateShape,
    right: &AggregateShape,
) -> Option<AggregateShape> {
    let (universe_len, universe) = left
        .set_bitmask_universe()
        .or_else(|| right.set_bitmask_universe())?;
    if shape_convertible_to_set_bitmask_operand(left, universe_len, &universe)
        && shape_convertible_to_set_bitmask_operand(right, universe_len, &universe)
    {
        Some(AggregateShape::SetBitmask {
            universe_len,
            universe,
        })
    } else {
        None
    }
}

fn set_bitmask_shape_from_intersect_operand_pair(
    left: &AggregateShape,
    right: &AggregateShape,
) -> Option<AggregateShape> {
    if let Some(shape) = set_bitmask_shape_from_convertible_operand_pair(left, right) {
        return Some(shape);
    }
    let (universe_len, universe) = left
        .set_bitmask_universe()
        .or_else(|| right.set_bitmask_universe())?;
    if !set_bitmask_universe_accepts_integer_values(&universe) {
        return None;
    }
    let exact_intersect_operand = |shape: &AggregateShape| match shape {
        AggregateShape::SetBitmask { .. } => {
            shape.compatible_set_bitmask_universe(universe_len, &universe)
        }
        AggregateShape::ExactIntSet { .. } | AggregateShape::Interval { .. } => true,
        _ => false,
    };
    if exact_intersect_operand(left) && exact_intersect_operand(right) {
        Some(AggregateShape::SetBitmask {
            universe_len,
            universe,
        })
    } else {
        None
    }
}

fn merge_finite_set_element_shape(
    left: &AggregateShape,
    right: &AggregateShape,
) -> Option<Box<AggregateShape>> {
    let left = left.finite_set_element_shape();
    let right = right.finite_set_element_shape();
    merge_compatible_shapes(left.as_ref(), right.as_ref()).map(Box::new)
}

fn finite_set_union_shape(
    left: Option<&AggregateShape>,
    right: Option<&AggregateShape>,
) -> Option<AggregateShape> {
    let (Some(left), Some(right)) = (left, right) else {
        return None;
    };
    if let Some(shape) = set_bitmask_shape_from_convertible_operand_pair(left, right) {
        return Some(shape);
    }
    if matches!(left, AggregateShape::SetBitmask { .. })
        || matches!(right, AggregateShape::SetBitmask { .. })
    {
        return None;
    }
    if !left.is_finite_set_shape() || !right.is_finite_set_shape() {
        return None;
    }
    Some(
        left.finite_set_len_bound()
            .zip(right.finite_set_len_bound())
            .and_then(|(left, right)| left.checked_add(right))
            .map_or(AggregateShape::FiniteSet, |max_len| {
                bounded_set_or_finite_with_element(
                    max_len,
                    merge_finite_set_element_shape(left, right),
                )
            }),
    )
}

fn finite_set_intersect_shape(
    left: Option<&AggregateShape>,
    right: Option<&AggregateShape>,
) -> Option<AggregateShape> {
    let (Some(left), Some(right)) = (left, right) else {
        return None;
    };
    if let Some(shape) = set_bitmask_shape_from_intersect_operand_pair(left, right) {
        return Some(shape);
    }
    if matches!(left, AggregateShape::SetBitmask { .. })
        || matches!(right, AggregateShape::SetBitmask { .. })
    {
        return None;
    }
    if !left.is_finite_set_shape() || !right.is_finite_set_shape() {
        return None;
    }
    Some(
        left.finite_set_len_bound()
            .zip(right.finite_set_len_bound())
            .map(|(left, right)| left.min(right))
            .map_or(AggregateShape::FiniteSet, |max_len| {
                bounded_set_or_finite_with_element(
                    max_len,
                    merge_finite_set_element_shape(left, right),
                )
            }),
    )
}

fn can_lower_small_setdiff_rhs_as_int_mask_shape(shape: &AggregateShape) -> bool {
    match shape {
        AggregateShape::ExactIntSet { .. } | AggregateShape::Interval { .. } => true,
        AggregateShape::Set { len: 0, .. } => true,
        AggregateShape::Set { .. } => false,
        _ => false,
    }
}

fn small_interval_setdiff_shape(
    source: &AggregateShape,
    subtract: &AggregateShape,
) -> Option<AggregateShape> {
    let AggregateShape::Interval { lo, hi } = source else {
        return None;
    };
    if !can_lower_small_setdiff_rhs_as_int_mask_shape(subtract) {
        return None;
    }
    let universe_len = if hi < lo {
        0
    } else {
        let len = hi.checked_sub(*lo)?.checked_add(1)?;
        let len = u32::try_from(len).ok()?;
        if len > 63 {
            return None;
        }
        len
    };
    Some(AggregateShape::SetBitmask {
        universe_len,
        universe: SetBitmaskUniverse::IntRange { lo: *lo },
    })
}

fn finite_set_diff_shape(
    source: Option<&AggregateShape>,
    subtract: Option<&AggregateShape>,
) -> Option<AggregateShape> {
    let source = source?;
    if let Some(subtract) = subtract {
        if let Some(shape) = set_bitmask_shape_from_convertible_operand_pair(source, subtract) {
            return Some(shape);
        }
        if matches!(source, AggregateShape::SetBitmask { .. })
            || matches!(subtract, AggregateShape::SetBitmask { .. })
        {
            return None;
        }
        if let Some(shape) = small_interval_setdiff_shape(source, subtract) {
            return Some(shape);
        }
    } else if matches!(source, AggregateShape::SetBitmask { .. }) {
        return source
            .set_bitmask_universe()
            .map(|(universe_len, universe)| AggregateShape::SetBitmask {
                universe_len,
                universe,
            });
    }
    if !source.is_finite_set_shape() {
        return None;
    }
    Some(
        source
            .finite_set_len_bound()
            .map_or(AggregateShape::FiniteSet, |max_len| {
                bounded_set_or_finite_with_element(
                    max_len,
                    source.finite_set_element_shape().map(Box::new),
                )
            }),
    )
}

fn tracked_shape_from_compound_layout(layout: &CompoundLayout) -> Option<AggregateShape> {
    match layout {
        CompoundLayout::Function {
            pair_count: Some(n),
            value_layout,
            domain_lo,
            ..
        } => Some(AggregateShape::Function {
            len: u32::try_from(*n).ok()?,
            domain_lo: *domain_lo,
            value: tracked_shape_from_compound_layout(value_layout).map(Box::new),
        }),
        CompoundLayout::Record { fields } => Some(AggregateShape::Record {
            fields: fields
                .iter()
                .map(|(name, layout)| {
                    (
                        *name,
                        tracked_shape_from_compound_layout(layout).map(Box::new),
                    )
                })
                .collect(),
        }),
        CompoundLayout::Set {
            element_count: Some(n),
            ..
        } => Some(AggregateShape::SetBitmask {
            universe_len: u32::try_from(*n).ok()?,
            universe: SetBitmaskUniverse::Unknown,
        }),
        CompoundLayout::SetBitmask { universe } => Some(AggregateShape::SetBitmask {
            universe_len: u32::try_from(universe.len()).ok()?,
            universe: SetBitmaskUniverse::from_elements(universe),
        }),
        CompoundLayout::Sequence {
            element_layout,
            element_count: Some(n),
        } => Some(AggregateShape::Sequence {
            extent: SequenceExtent::Capacity(u32::try_from(*n).ok()?),
            element: tracked_shape_from_compound_layout(element_layout).map(Box::new),
        }),
        CompoundLayout::Int => Some(AggregateShape::Scalar(ScalarShape::Int)),
        CompoundLayout::Bool => Some(AggregateShape::Scalar(ScalarShape::Bool)),
        CompoundLayout::String => Some(AggregateShape::Scalar(ScalarShape::String)),
        _ => None,
    }
}

fn tracked_shape_from_var_layout(var_layout: &VarLayout) -> Option<AggregateShape> {
    match var_layout {
        VarLayout::ScalarInt => Some(AggregateShape::Scalar(ScalarShape::Int)),
        VarLayout::ScalarBool => Some(AggregateShape::Scalar(ScalarShape::Bool)),
        VarLayout::Compound(layout) => tracked_shape_from_compound_layout(layout),
        _ => None,
    }
}

fn tracked_shape_from_state_layout(
    state_layout: Option<&JitStateLayout>,
    var_idx: u16,
) -> Option<AggregateShape> {
    state_layout
        .and_then(|layout| layout.var_layout(usize::from(var_idx)))
        .and_then(tracked_shape_from_var_layout)
}

fn set_enum_element_shape(
    summary: &ShapeSummary,
    start: u8,
    count: u8,
) -> Option<Box<AggregateShape>> {
    let element_shapes: Vec<_> = (0..count)
        .filter_map(|i| start.checked_add(i))
        .map(|reg| summary.aggregate_shapes.get(&reg).cloned())
        .collect();
    if element_shapes.len() == usize::from(count) {
        uniform_shape(&element_shapes)
    } else {
        None
    }
}

fn exact_int_set_values_from_summary(
    summary: &ShapeSummary,
    start: u8,
    count: u8,
) -> Option<Vec<i64>> {
    let mut values = Vec::with_capacity(usize::from(count));
    for i in 0..count {
        let reg = start.checked_add(i)?;
        if !summary
            .aggregate_shapes
            .get(&reg)
            .is_some_and(AggregateShape::is_numeric_scalar_shape)
        {
            return None;
        }
        values.push(*summary.const_scalar_values.get(&reg)?);
    }
    Some(values)
}

fn set_enum_shape(summary: &ShapeSummary, start: u8, count: u8) -> AggregateShape {
    if let Some(values) = exact_int_set_values_from_summary(summary, start, count) {
        return AggregateShape::ExactIntSet { values };
    }
    if let Some((universe_len, universe)) =
        set_enum_scalar_int_domain_universe_from_summary(summary, start, count)
    {
        return AggregateShape::SetBitmask {
            universe_len,
            universe,
        };
    }
    AggregateShape::Set {
        len: u32::from(count),
        element: set_enum_element_shape(summary, start, count),
    }
}

fn set_enum_scalar_int_domain_universe_from_summary(
    summary: &ShapeSummary,
    start: u8,
    count: u8,
) -> Option<(u32, SetBitmaskUniverse)> {
    if count == 0 {
        return None;
    }
    let mut result: Option<(u32, SetBitmaskUniverse)> = None;
    for i in 0..count {
        let reg = start.checked_add(i)?;
        let current = summary
            .aggregate_shapes
            .get(&reg)
            .and_then(AggregateShape::scalar_int_domain_universe)?;
        if result.as_ref().is_some_and(|existing| existing != &current) {
            return None;
        }
        result = Some(current);
    }
    result
}

fn const_shape_and_scalar(value: &tla_value::Value) -> (Option<AggregateShape>, Option<i64>) {
    match value {
        tla_value::Value::SmallInt(n) => (Some(AggregateShape::Scalar(ScalarShape::Int)), Some(*n)),
        tla_value::Value::Int(n) => (Some(AggregateShape::Scalar(ScalarShape::Int)), n.to_i64()),
        tla_value::Value::Bool(b) => (
            Some(AggregateShape::Scalar(ScalarShape::Bool)),
            Some(i64::from(*b)),
        ),
        tla_value::Value::String(s) => (
            Some(AggregateShape::Scalar(ScalarShape::String)),
            Some(i64::from(tla_core::intern_name(s).0)),
        ),
        tla_value::Value::ModelValue(name) => {
            let shape = SymbolicDomain::from_model_value(name.as_ref())
                .map(AggregateShape::SymbolicDomain)
                .unwrap_or(AggregateShape::Scalar(ScalarShape::ModelValue));
            (
                Some(shape),
                Some(i64::from(tla_core::intern_name(name.as_ref()).0)),
            )
        }
        tla_value::Value::Interval(iv) => {
            let (Some(lo), Some(hi)) = (iv.low().to_i64(), iv.high().to_i64()) else {
                return (None, None);
            };
            (Some(AggregateShape::Interval { lo, hi }), None)
        }
        tla_value::Value::Set(set) => {
            let Ok(len) = u32::try_from(set.len()) else {
                return (None, None);
            };
            if let Some(values) = set
                .iter()
                .map(|value| match value {
                    tla_value::Value::SmallInt(n) => Some(*n),
                    tla_value::Value::Int(n) => n.to_i64(),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
            {
                return (Some(AggregateShape::ExactIntSet { values }), None);
            }
            let element_shapes: Vec<_> = set
                .iter()
                .map(|value| const_shape_and_scalar(value).0)
                .collect();
            (
                Some(AggregateShape::Set {
                    len,
                    element: uniform_shape(&element_shapes),
                }),
                None,
            )
        }
        tla_value::Value::Seq(seq) => {
            let Ok(len) = u32::try_from(seq.len()) else {
                return (None, None);
            };
            let element_shapes: Vec<_> = seq
                .iter()
                .map(|value| const_shape_and_scalar(value).0)
                .collect();
            (
                Some(AggregateShape::Sequence {
                    extent: SequenceExtent::Exact(len),
                    element: uniform_shape(&element_shapes),
                }),
                None,
            )
        }
        tla_value::Value::Tuple(tuple) => {
            let Ok(len) = u32::try_from(tuple.len()) else {
                return (None, None);
            };
            let element_shapes: Vec<_> = tuple
                .iter()
                .map(|value| const_shape_and_scalar(value).0)
                .collect();
            (
                Some(AggregateShape::Sequence {
                    extent: SequenceExtent::Exact(len),
                    element: uniform_shape(&element_shapes),
                }),
                None,
            )
        }
        tla_value::Value::SeqSet(seq_set) => {
            let (Some(base), _) = const_shape_and_scalar(seq_set.base()) else {
                return (None, None);
            };
            (
                Some(AggregateShape::SeqSet {
                    base: Box::new(base),
                }),
                None,
            )
        }
        tla_value::Value::Record(rec) => {
            let fields = rec
                .iter()
                .map(|(field, value)| {
                    let (shape, _) = const_shape_and_scalar(value);
                    (field, shape.map(Box::new))
                })
                .collect();
            (Some(AggregateShape::Record { fields }), None)
        }
        tla_value::Value::RecordSet(record_set) => {
            let mut fields = Vec::with_capacity(record_set.fields_len());
            for (field_name, field_set) in record_set.fields_check_order_iter() {
                let (Some(shape), _) = const_shape_and_scalar(field_set) else {
                    return (None, None);
                };
                fields.push((tla_core::intern_name(field_name), shape));
            }
            (Some(AggregateShape::RecordSet { fields }), None)
        }
        tla_value::Value::Func(func) => {
            let entries: Vec<_> = func.iter().collect();
            let Ok(len) = u32::try_from(entries.len()) else {
                return (None, None);
            };
            let domain_lo = dense_ordered_int_values_lo(entries.iter().map(|(key, _)| *key))
                .and_then(|(lo, domain_len)| (domain_len == len).then_some(lo));
            let mut value_shapes = Vec::with_capacity(entries.len());
            for (_, value) in entries {
                value_shapes.push(const_shape_and_scalar(value).0);
            }
            (
                Some(AggregateShape::Function {
                    len,
                    domain_lo,
                    value: uniform_shape(&value_shapes),
                }),
                None,
            )
        }
        tla_value::Value::IntFunc(func) => {
            let Ok(len) = u32::try_from(func.len()) else {
                return (None, None);
            };
            let mut value_shapes = Vec::with_capacity(func.len());
            for value in func.values() {
                value_shapes.push(const_shape_and_scalar(value).0);
            }
            (
                Some(AggregateShape::Function {
                    len,
                    domain_lo: Some(func.as_ref().min()),
                    value: uniform_shape(&value_shapes),
                }),
                None,
            )
        }
        _ => (None, None),
    }
}

fn infer_chunk_return_shapes(
    chunk: &BytecodeChunk,
    state_layout: Option<&JitStateLayout>,
) -> HashMap<u16, Option<AggregateShape>> {
    let mut cache = HashMap::new();
    let mut visiting = HashSet::new();
    for idx in 0..chunk.functions.len() {
        let Ok(op_idx) = u16::try_from(idx) else {
            continue;
        };
        let _ = infer_callee_return_shape(chunk, op_idx, state_layout, &mut cache, &mut visiting);
    }
    cache
}

fn infer_callee_return_shape(
    chunk: &BytecodeChunk,
    op_idx: u16,
    state_layout: Option<&JitStateLayout>,
    cache: &mut HashMap<u16, Option<AggregateShape>>,
    visiting: &mut HashSet<u16>,
) -> Option<AggregateShape> {
    if let Some(shape) = cache.get(&op_idx) {
        return shape.clone();
    }
    if !visiting.insert(op_idx) {
        cache.insert(op_idx, None);
        return None;
    }

    let shape = chunk
        .functions
        .get(usize::from(op_idx))
        .and_then(|func| infer_function_return_shape(func, chunk, state_layout, cache, visiting));
    visiting.remove(&op_idx);
    cache.insert(op_idx, shape.clone());
    shape
}

fn infer_function_return_shape(
    func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    state_layout: Option<&JitStateLayout>,
    cache: &mut HashMap<u16, Option<AggregateShape>>,
    visiting: &mut HashSet<u16>,
) -> Option<AggregateShape> {
    infer_function_return_shape_with_params(func, chunk, state_layout, cache, visiting, &[])
}

fn infer_callee_return_shape_for_args(
    chunk: &BytecodeChunk,
    op_idx: u16,
    arg_shapes: &[Option<AggregateShape>],
    state_layout: Option<&JitStateLayout>,
) -> Option<AggregateShape> {
    let mut cache = HashMap::new();
    let mut visiting = HashSet::new();
    infer_callee_return_shape_with_args(
        chunk,
        op_idx,
        arg_shapes,
        state_layout,
        &mut cache,
        &mut visiting,
    )
}

fn infer_callee_return_shape_with_args(
    chunk: &BytecodeChunk,
    op_idx: u16,
    arg_shapes: &[Option<AggregateShape>],
    state_layout: Option<&JitStateLayout>,
    cache: &mut HashMap<u16, Option<AggregateShape>>,
    visiting: &mut HashSet<u16>,
) -> Option<AggregateShape> {
    if arg_shapes.is_empty() {
        return infer_callee_return_shape(chunk, op_idx, state_layout, cache, visiting);
    }
    if !visiting.insert(op_idx) {
        return None;
    }
    let shape = chunk.functions.get(usize::from(op_idx)).and_then(|func| {
        infer_function_return_shape_with_params(
            func,
            chunk,
            state_layout,
            cache,
            visiting,
            arg_shapes,
        )
    });
    visiting.remove(&op_idx);
    shape
}

fn seed_shape_summary(
    func: &BytecodeFunction,
    param_shapes: &[Option<AggregateShape>],
) -> ShapeSummary {
    let mut summary = ShapeSummary::default();
    for (idx, shape) in param_shapes
        .iter()
        .take(usize::from(func.arity))
        .enumerate()
    {
        let Ok(reg) = u8::try_from(idx) else {
            break;
        };
        if let Some(shape) = shape.clone() {
            summary.set_shape(reg, shape);
        }
    }
    summary
}

fn uses_branch_return_shape_inference(func: &BytecodeFunction) -> bool {
    func.instructions.iter().any(|opcode| {
        matches!(
            opcode,
            Opcode::Jump { .. }
                | Opcode::JumpTrue { .. }
                | Opcode::JumpFalse { .. }
                | Opcode::SetFilterBegin { .. }
                | Opcode::LoopNext { .. }
        )
    })
}

fn has_unmodeled_shape_inference_loop(func: &BytecodeFunction) -> bool {
    func.instructions.iter().any(|opcode| {
        matches!(
            opcode,
            Opcode::ForallBegin { .. }
                | Opcode::ForallNext { .. }
                | Opcode::ExistsBegin { .. }
                | Opcode::ExistsNext { .. }
                | Opcode::ChooseBegin { .. }
                | Opcode::ChooseNext { .. }
                | Opcode::SetBuilderBegin { .. }
                | Opcode::Halt
        )
    })
}

fn merge_shape_facts(left: &ShapeSummary, right: &ShapeSummary) -> ShapeSummary {
    let mut aggregate_shapes = HashMap::new();
    for (reg, left_shape) in &left.aggregate_shapes {
        let Some(right_shape) = right.aggregate_shapes.get(reg) else {
            continue;
        };
        if let Some(shape) = merge_compatible_shapes(Some(left_shape), Some(right_shape)) {
            aggregate_shapes.insert(*reg, shape);
        }
    }

    let mut const_scalar_values = HashMap::new();
    for (reg, left_value) in &left.const_scalar_values {
        if right
            .const_scalar_values
            .get(reg)
            .is_some_and(|right_value| right_value == left_value)
        {
            const_scalar_values.insert(*reg, *left_value);
        }
    }

    ShapeSummary {
        aggregate_shapes,
        const_scalar_values,
        funcdef_stack: if left.funcdef_stack == right.funcdef_stack {
            left.funcdef_stack.clone()
        } else {
            Vec::new()
        },
        return_shape: None,
        saw_return: false,
    }
}

fn push_shape_fact(
    facts: &mut [Option<ShapeSummary>],
    worklist: &mut VecDeque<usize>,
    pc: usize,
    incoming: ShapeSummary,
) -> Option<()> {
    let slot = facts.get_mut(pc)?;
    let changed = match slot {
        Some(existing) => {
            let merged = merge_shape_facts(existing, &incoming);
            if *existing == merged {
                false
            } else {
                *existing = merged;
                true
            }
        }
        None => {
            *slot = Some(incoming);
            true
        }
    };
    if changed {
        worklist.push_back(pc);
    }
    Some(())
}

fn shape_forward_target(pc: usize, offset: i32, len: usize) -> Option<usize> {
    let target = resolve_target(pc, offset).ok()?;
    (target < len).then_some(target)
}

fn apply_shape_transfer(
    summary: &mut ShapeSummary,
    opcode: Opcode,
    chunk: &BytecodeChunk,
    state_layout: Option<&JitStateLayout>,
    cache: &mut HashMap<u16, Option<AggregateShape>>,
    visiting: &mut HashSet<u16>,
) -> Option<()> {
    match opcode {
        Opcode::LoadImm { rd, value } => {
            summary.set_scalar(rd, value, AggregateShape::Scalar(ScalarShape::Int));
        }
        Opcode::LoadBool { rd, value } => {
            summary.set_scalar(
                rd,
                i64::from(value),
                AggregateShape::Scalar(ScalarShape::Bool),
            );
        }
        Opcode::LoadConst { rd, idx } => {
            let value = chunk.constants.get_value(idx);
            let (shape, scalar) = const_shape_and_scalar(value);
            if let Some(shape) = shape {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
            if let Some(scalar) = scalar {
                summary.const_scalar_values.insert(rd, scalar);
            } else {
                summary.clear_scalar(rd);
            }
        }
        Opcode::LoadVar { rd, var_idx } | Opcode::LoadPrime { rd, var_idx } => {
            summary.clear_scalar(rd);
            if let Some(shape) = tracked_shape_from_state_layout(state_layout, var_idx) {
                summary.set_shape(rd, shape);
            } else {
                summary.set_shape(rd, AggregateShape::StateValue);
            }
        }
        Opcode::Move { rd, rs } => {
            if let Some(shape) = summary.aggregate_shapes.get(&rs).cloned() {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
            if let Some(value) = summary.const_scalar_values.get(&rs).copied() {
                summary.const_scalar_values.insert(rd, value);
            } else {
                summary.clear_scalar(rd);
            }
        }
        Opcode::SetEnum { rd, start, count } => {
            summary.clear_scalar(rd);
            summary.set_shape(rd, set_enum_shape(summary, start, count));
        }
        Opcode::Range { rd, lo, hi } => {
            summary.clear_scalar(rd);
            match (
                summary.const_scalar_values.get(&lo).copied(),
                summary.const_scalar_values.get(&hi).copied(),
            ) {
                (Some(lo), Some(hi)) => {
                    summary.set_shape(rd, AggregateShape::Interval { lo, hi });
                }
                _ => summary.set_shape(rd, AggregateShape::FiniteSet),
            }
        }
        Opcode::SetUnion { rd, r1, r2 } => {
            summary.clear_scalar(rd);
            let shape = finite_set_union_shape(
                summary.aggregate_shapes.get(&r1),
                summary.aggregate_shapes.get(&r2),
            );
            if let Some(shape) = shape {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::SetIntersect { rd, r1, r2 } => {
            summary.clear_scalar(rd);
            let shape = finite_set_intersect_shape(
                summary.aggregate_shapes.get(&r1),
                summary.aggregate_shapes.get(&r2),
            );
            if let Some(shape) = shape {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::SetDiff { rd, r1, r2 } => {
            summary.clear_scalar(rd);
            let shape = finite_set_diff_shape(
                summary.aggregate_shapes.get(&r1),
                summary.aggregate_shapes.get(&r2),
            );
            if let Some(shape) = shape {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::ForallBegin {
            rd,
            r_binding,
            r_domain,
            ..
        }
        | Opcode::ExistsBegin {
            rd,
            r_binding,
            r_domain,
            ..
        }
        | Opcode::ChooseBegin {
            rd,
            r_binding,
            r_domain,
            ..
        } => {
            summary.clear_scalar(rd);
            summary.clear_shape(rd);
            apply_binding_begin_shape_transfer(summary, r_binding, r_domain);
        }
        Opcode::SetFilterBegin {
            rd,
            r_binding,
            r_domain,
            ..
        } => {
            summary.clear_scalar(rd);
            apply_binding_begin_shape_transfer(summary, r_binding, r_domain);
            match summary.aggregate_shapes.get(&r_domain) {
                Some(domain) if domain.is_finite_set_shape() => {
                    if let Some(max_len) = domain.finite_set_len_bound() {
                        summary.set_shape(
                            rd,
                            AggregateShape::BoundedSet {
                                max_len,
                                element: binding_shape_from_domain(domain).map(Box::new),
                            },
                        );
                    } else {
                        summary.set_shape(rd, AggregateShape::FiniteSet);
                    }
                }
                _ => summary.clear_shape(rd),
            }
        }
        Opcode::Powerset { rd, rs } => {
            summary.clear_scalar(rd);
            if let Some(base) = summary.aggregate_shapes.get(&rs).cloned() {
                summary.set_shape(
                    rd,
                    AggregateShape::Powerset {
                        base: Box::new(base),
                    },
                );
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::FuncSet { rd, domain, range } => {
            summary.clear_scalar(rd);
            match (
                summary.aggregate_shapes.get(&domain).cloned(),
                summary.aggregate_shapes.get(&range).cloned(),
            ) {
                (Some(domain), Some(range)) => summary.set_shape(
                    rd,
                    AggregateShape::FunctionSet {
                        domain: Box::new(domain),
                        range: Box::new(range),
                    },
                ),
                _ => summary.clear_shape(rd),
            }
        }
        Opcode::RecordNew {
            rd,
            fields_start,
            values_start,
            count,
        } => {
            summary.clear_scalar(rd);
            let mut fields = Vec::with_capacity(usize::from(count));
            let mut tracked = true;
            for i in 0..count {
                let Some(field_idx) = fields_start.checked_add(u16::from(i)) else {
                    tracked = false;
                    break;
                };
                if usize::from(field_idx) >= chunk.constants.value_count() {
                    tracked = false;
                    break;
                }
                let field_name = match chunk.constants.get_value(field_idx) {
                    tla_value::Value::String(name) => tla_core::intern_name(name),
                    _ => {
                        tracked = false;
                        break;
                    }
                };
                fields.push((
                    field_name,
                    summary
                        .aggregate_shapes
                        .get(&(values_start + i))
                        .cloned()
                        .map(Box::new),
                ));
            }
            if tracked {
                summary.set_shape(rd, AggregateShape::Record { fields });
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::SeqNew { rd, start, count } | Opcode::TupleNew { rd, start, count } => {
            summary.clear_scalar(rd);
            let mut element_shapes = Vec::with_capacity(usize::from(count));
            let mut tracked = true;
            for i in 0..count {
                let Some(reg) = start.checked_add(i) else {
                    tracked = false;
                    break;
                };
                element_shapes.push(summary.aggregate_shapes.get(&reg).cloned());
            }
            if tracked {
                summary.set_shape(
                    rd,
                    AggregateShape::Sequence {
                        extent: SequenceExtent::Exact(u32::from(count)),
                        element: uniform_shape(&element_shapes),
                    },
                );
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::RecordSet {
            rd,
            fields_start,
            values_start,
            count,
        } => {
            summary.clear_scalar(rd);
            let mut fields = Vec::with_capacity(usize::from(count));
            let mut tracked = true;
            for i in 0..count {
                let Some(field_idx) = fields_start.checked_add(u16::from(i)) else {
                    tracked = false;
                    break;
                };
                if usize::from(field_idx) >= chunk.constants.value_count() {
                    tracked = false;
                    break;
                }
                let field_name = match chunk.constants.get_value(field_idx) {
                    tla_value::Value::String(name) => tla_core::intern_name(name),
                    _ => {
                        tracked = false;
                        break;
                    }
                };
                let Some(domain_shape) = summary.aggregate_shapes.get(&(values_start + i)).cloned()
                else {
                    tracked = false;
                    break;
                };
                fields.push((field_name, domain_shape));
            }
            if tracked {
                summary.set_shape(rd, AggregateShape::RecordSet { fields });
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::RecordGet { rd, rs, field_idx } => {
            summary.clear_scalar(rd);
            if let Some(shape) = record_get_shape(
                summary.aggregate_shapes.get(&rs),
                Some(&chunk.constants),
                field_idx,
            ) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::TupleGet { rd, rs, .. } => {
            summary.clear_scalar(rd);
            if let Some(shape) = sequence_element_shape(summary.aggregate_shapes.get(&rs)) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::FuncApply { rd, func, arg } => {
            summary.clear_scalar(rd);
            if let Some(shape) = function_apply_shape_from_summary(summary, func, arg) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::FuncExcept {
            rd,
            func,
            path,
            val,
        } => {
            summary.clear_scalar(rd);
            if let Some(shape) = function_except_shape_from_summary(summary, func, path, val) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::FuncDefBegin {
            rd,
            r_binding,
            r_domain,
            ..
        } => {
            apply_funcdef_begin_shape_transfer(summary, rd, r_binding, r_domain);
        }
        Opcode::LoopNext {
            r_binding, r_body, ..
        } => {
            apply_loop_next_shape_transfer(summary, r_binding, r_body);
        }
        Opcode::Domain { rd, rs } => {
            summary.clear_scalar(rd);
            if let Some(len) = summary
                .aggregate_shapes
                .get(&rs)
                .and_then(AggregateShape::tracked_len)
            {
                summary.set_shape(rd, AggregateShape::Set { len, element: None });
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::CondMove { rd, cond, rs } => {
            summary.clear_scalar(rd);
            if let Some(shape) = cond_move_result_shape(
                &summary.aggregate_shapes,
                &summary.const_scalar_values,
                rd,
                cond,
                rs,
            ) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::CallBuiltin {
            rd,
            builtin: tla_tir::bytecode::BuiltinOp::Seq,
            args_start,
            argc: 1,
        } => {
            summary.clear_scalar(rd);
            if let Some(base) = summary.aggregate_shapes.get(&args_start).cloned() {
                summary.set_shape(
                    rd,
                    AggregateShape::SeqSet {
                        base: Box::new(base),
                    },
                );
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::CallBuiltin {
            rd,
            builtin: tla_tir::bytecode::BuiltinOp::Head,
            args_start,
            argc: 1,
        } => {
            summary.clear_scalar(rd);
            if let Some(shape) = sequence_head_shape(summary.aggregate_shapes.get(&args_start)) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::CallBuiltin {
            rd,
            builtin: tla_tir::bytecode::BuiltinOp::Tail,
            args_start,
            argc: 1,
        } => {
            summary.clear_scalar(rd);
            if let Some(shape) = sequence_tail_shape(summary.aggregate_shapes.get(&args_start)) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::CallBuiltin {
            rd,
            builtin: tla_tir::bytecode::BuiltinOp::Append,
            args_start,
            argc: 2,
        } => {
            summary.clear_scalar(rd);
            let elem_reg = args_start.checked_add(1);
            let shape = elem_reg.and_then(|elem_reg| {
                sequence_append_shape(
                    summary.aggregate_shapes.get(&args_start),
                    summary.aggregate_shapes.get(&elem_reg),
                )
            });
            if let Some(shape) = shape {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        Opcode::Call {
            rd,
            op_idx,
            args_start,
            argc,
        } => {
            summary.clear_scalar(rd);
            let raw_shape = if argc == 0 {
                infer_callee_return_shape(chunk, op_idx, state_layout, cache, visiting)
            } else {
                let mut arg_shapes = Vec::with_capacity(usize::from(argc));
                for i in 0..argc {
                    let Some(reg) = args_start.checked_add(i) else {
                        arg_shapes.clear();
                        break;
                    };
                    arg_shapes.push(summary.aggregate_shapes.get(&reg).cloned());
                }
                if arg_shapes.len() == usize::from(argc) {
                    infer_callee_return_shape_with_args(
                        chunk,
                        op_idx,
                        &arg_shapes,
                        state_layout,
                        cache,
                        visiting,
                    )
                } else {
                    None
                }
            };
            if let Some(shape) = call_result_summary_shape(raw_shape) {
                summary.set_shape(rd, shape);
            } else {
                summary.clear_shape(rd);
            }
        }
        _ => {
            if let Some(rd) = opcode.dest_register() {
                summary.clear_scalar(rd);
                summary.clear_shape(rd);
            }
        }
    }
    Some(())
}

fn infer_function_return_shape_with_params(
    func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    state_layout: Option<&JitStateLayout>,
    cache: &mut HashMap<u16, Option<AggregateShape>>,
    visiting: &mut HashSet<u16>,
    param_shapes: &[Option<AggregateShape>],
) -> Option<AggregateShape> {
    if has_unmodeled_shape_inference_loop(func) {
        return None;
    }
    if uses_branch_return_shape_inference(func) {
        return infer_function_return_shape_cfg(
            func,
            chunk,
            state_layout,
            cache,
            visiting,
            param_shapes,
        );
    }

    let mut summary = ShapeSummary::default();
    for (idx, shape) in param_shapes
        .iter()
        .take(usize::from(func.arity))
        .enumerate()
    {
        let Ok(reg) = u8::try_from(idx) else {
            break;
        };
        if let Some(shape) = shape.clone() {
            summary.set_shape(reg, shape);
        }
    }
    for opcode in &func.instructions {
        match *opcode {
            Opcode::LoadImm { rd, value } => {
                summary.set_scalar(rd, value, AggregateShape::Scalar(ScalarShape::Int));
            }
            Opcode::LoadBool { rd, value } => {
                summary.set_scalar(
                    rd,
                    i64::from(value),
                    AggregateShape::Scalar(ScalarShape::Bool),
                );
            }
            Opcode::LoadConst { rd, idx } => {
                let value = chunk.constants.get_value(idx);
                let (shape, scalar) = const_shape_and_scalar(value);
                if let Some(shape) = shape {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
                if let Some(scalar) = scalar {
                    summary.const_scalar_values.insert(rd, scalar);
                } else {
                    summary.clear_scalar(rd);
                }
            }
            Opcode::LoadVar { rd, var_idx } | Opcode::LoadPrime { rd, var_idx } => {
                summary.clear_scalar(rd);
                if let Some(shape) = tracked_shape_from_state_layout(state_layout, var_idx) {
                    summary.set_shape(rd, shape);
                } else {
                    summary.set_shape(rd, AggregateShape::StateValue);
                }
            }
            Opcode::Move { rd, rs } => {
                if let Some(shape) = summary.aggregate_shapes.get(&rs).cloned() {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
                if let Some(value) = summary.const_scalar_values.get(&rs).copied() {
                    summary.const_scalar_values.insert(rd, value);
                } else {
                    summary.clear_scalar(rd);
                }
            }
            Opcode::SetEnum { rd, start, count } => {
                summary.clear_scalar(rd);
                summary.set_shape(rd, set_enum_shape(&summary, start, count));
            }
            Opcode::Range { rd, lo, hi } => {
                summary.clear_scalar(rd);
                match (
                    summary.const_scalar_values.get(&lo).copied(),
                    summary.const_scalar_values.get(&hi).copied(),
                ) {
                    (Some(lo), Some(hi)) => {
                        summary.set_shape(rd, AggregateShape::Interval { lo, hi });
                    }
                    _ => summary.set_shape(rd, AggregateShape::FiniteSet),
                }
            }
            Opcode::SetUnion { rd, r1, r2 } => {
                summary.clear_scalar(rd);
                let shape = finite_set_union_shape(
                    summary.aggregate_shapes.get(&r1),
                    summary.aggregate_shapes.get(&r2),
                );
                if let Some(shape) = shape {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::SetIntersect { rd, r1, r2 } => {
                summary.clear_scalar(rd);
                let shape = finite_set_intersect_shape(
                    summary.aggregate_shapes.get(&r1),
                    summary.aggregate_shapes.get(&r2),
                );
                if let Some(shape) = shape {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::SetDiff { rd, r1, r2 } => {
                summary.clear_scalar(rd);
                let shape = finite_set_diff_shape(
                    summary.aggregate_shapes.get(&r1),
                    summary.aggregate_shapes.get(&r2),
                );
                if let Some(shape) = shape {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::SetFilterBegin { rd, r_domain, .. } => {
                summary.clear_scalar(rd);
                match summary.aggregate_shapes.get(&r_domain) {
                    Some(domain) if domain.is_finite_set_shape() => {
                        if let Some(max_len) = domain.finite_set_len_bound() {
                            summary.set_shape(
                                rd,
                                AggregateShape::BoundedSet {
                                    max_len,
                                    element: binding_shape_from_domain(domain).map(Box::new),
                                },
                            );
                        } else {
                            summary.set_shape(rd, AggregateShape::FiniteSet);
                        }
                    }
                    _ => summary.clear_shape(rd),
                }
            }
            Opcode::Powerset { rd, rs } => {
                summary.clear_scalar(rd);
                if let Some(base) = summary.aggregate_shapes.get(&rs).cloned() {
                    summary.set_shape(
                        rd,
                        AggregateShape::Powerset {
                            base: Box::new(base),
                        },
                    );
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::FuncSet { rd, domain, range } => {
                summary.clear_scalar(rd);
                match (
                    summary.aggregate_shapes.get(&domain).cloned(),
                    summary.aggregate_shapes.get(&range).cloned(),
                ) {
                    (Some(domain), Some(range)) => summary.set_shape(
                        rd,
                        AggregateShape::FunctionSet {
                            domain: Box::new(domain),
                            range: Box::new(range),
                        },
                    ),
                    _ => summary.clear_shape(rd),
                }
            }
            Opcode::RecordNew {
                rd,
                fields_start,
                values_start,
                count,
            } => {
                summary.clear_scalar(rd);
                let mut fields = Vec::with_capacity(usize::from(count));
                let mut tracked = true;
                for i in 0..count {
                    let Some(field_idx) = fields_start.checked_add(u16::from(i)) else {
                        tracked = false;
                        break;
                    };
                    if usize::from(field_idx) >= chunk.constants.value_count() {
                        tracked = false;
                        break;
                    }
                    let field_name = match chunk.constants.get_value(field_idx) {
                        tla_value::Value::String(name) => tla_core::intern_name(name),
                        _ => {
                            tracked = false;
                            break;
                        }
                    };
                    fields.push((
                        field_name,
                        summary
                            .aggregate_shapes
                            .get(&(values_start + i))
                            .cloned()
                            .map(Box::new),
                    ));
                }
                if tracked {
                    summary.set_shape(rd, AggregateShape::Record { fields });
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::SeqNew { rd, start, count } | Opcode::TupleNew { rd, start, count } => {
                summary.clear_scalar(rd);
                let mut element_shapes = Vec::with_capacity(usize::from(count));
                let mut tracked = true;
                for i in 0..count {
                    let Some(reg) = start.checked_add(i) else {
                        tracked = false;
                        break;
                    };
                    element_shapes.push(summary.aggregate_shapes.get(&reg).cloned());
                }
                if tracked {
                    summary.set_shape(
                        rd,
                        AggregateShape::Sequence {
                            extent: SequenceExtent::Exact(u32::from(count)),
                            element: uniform_shape(&element_shapes),
                        },
                    );
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::RecordSet {
                rd,
                fields_start,
                values_start,
                count,
            } => {
                summary.clear_scalar(rd);
                let mut fields = Vec::with_capacity(usize::from(count));
                let mut tracked = true;
                for i in 0..count {
                    let Some(field_idx) = fields_start.checked_add(u16::from(i)) else {
                        tracked = false;
                        break;
                    };
                    if usize::from(field_idx) >= chunk.constants.value_count() {
                        tracked = false;
                        break;
                    }
                    let field_name = match chunk.constants.get_value(field_idx) {
                        tla_value::Value::String(name) => tla_core::intern_name(name),
                        _ => {
                            tracked = false;
                            break;
                        }
                    };
                    let Some(domain_shape) =
                        summary.aggregate_shapes.get(&(values_start + i)).cloned()
                    else {
                        tracked = false;
                        break;
                    };
                    fields.push((field_name, domain_shape));
                }
                if tracked {
                    summary.set_shape(rd, AggregateShape::RecordSet { fields });
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::RecordGet { rd, rs, field_idx } => {
                summary.clear_scalar(rd);
                if let Some(shape) = record_get_shape(
                    summary.aggregate_shapes.get(&rs),
                    Some(&chunk.constants),
                    field_idx,
                ) {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::TupleGet { rd, rs, .. } => {
                summary.clear_scalar(rd);
                if let Some(shape) = sequence_element_shape(summary.aggregate_shapes.get(&rs)) {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::FuncApply { rd, func, arg } => {
                summary.clear_scalar(rd);
                if let Some(shape) = function_apply_shape_from_summary(&summary, func, arg) {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::FuncExcept {
                rd,
                func,
                path,
                val,
            } => {
                summary.clear_scalar(rd);
                if let Some(shape) = function_except_shape_from_summary(&summary, func, path, val) {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::FuncDefBegin {
                rd,
                r_binding,
                r_domain,
                ..
            } => {
                apply_funcdef_begin_shape_transfer(&mut summary, rd, r_binding, r_domain);
            }
            Opcode::LoopNext {
                r_binding, r_body, ..
            } => {
                apply_loop_next_shape_transfer(&mut summary, r_binding, r_body);
            }
            Opcode::Domain { rd, rs } => {
                summary.clear_scalar(rd);
                if let Some(len) = summary
                    .aggregate_shapes
                    .get(&rs)
                    .and_then(AggregateShape::tracked_len)
                {
                    summary.set_shape(rd, AggregateShape::Set { len, element: None });
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::CondMove { rd, cond, rs } => {
                summary.clear_scalar(rd);
                if let Some(shape) = cond_move_result_shape(
                    &summary.aggregate_shapes,
                    &summary.const_scalar_values,
                    rd,
                    cond,
                    rs,
                ) {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::CallBuiltin {
                rd,
                builtin: tla_tir::bytecode::BuiltinOp::Seq,
                args_start,
                argc: 1,
            } => {
                summary.clear_scalar(rd);
                if let Some(base) = summary.aggregate_shapes.get(&args_start).cloned() {
                    summary.set_shape(
                        rd,
                        AggregateShape::SeqSet {
                            base: Box::new(base),
                        },
                    );
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::CallBuiltin {
                rd,
                builtin: tla_tir::bytecode::BuiltinOp::Head,
                args_start,
                argc: 1,
            } => {
                summary.clear_scalar(rd);
                if let Some(shape) = sequence_head_shape(summary.aggregate_shapes.get(&args_start))
                {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::CallBuiltin {
                rd,
                builtin: tla_tir::bytecode::BuiltinOp::Tail,
                args_start,
                argc: 1,
            } => {
                summary.clear_scalar(rd);
                if let Some(shape) = sequence_tail_shape(summary.aggregate_shapes.get(&args_start))
                {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::CallBuiltin {
                rd,
                builtin: tla_tir::bytecode::BuiltinOp::Append,
                args_start,
                argc: 2,
            } => {
                summary.clear_scalar(rd);
                let elem_reg = args_start.checked_add(1);
                let shape = elem_reg.and_then(|elem_reg| {
                    sequence_append_shape(
                        summary.aggregate_shapes.get(&args_start),
                        summary.aggregate_shapes.get(&elem_reg),
                    )
                });
                if let Some(shape) = shape {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::Call {
                rd,
                op_idx,
                args_start,
                argc,
            } => {
                summary.clear_scalar(rd);
                let raw_shape = if argc == 0 {
                    infer_callee_return_shape(chunk, op_idx, state_layout, cache, visiting)
                } else {
                    let mut arg_shapes = Vec::with_capacity(usize::from(argc));
                    for i in 0..argc {
                        let Some(reg) = args_start.checked_add(i) else {
                            arg_shapes.clear();
                            break;
                        };
                        arg_shapes.push(summary.aggregate_shapes.get(&reg).cloned());
                    }
                    if arg_shapes.len() == usize::from(argc) {
                        infer_callee_return_shape_with_args(
                            chunk,
                            op_idx,
                            &arg_shapes,
                            state_layout,
                            cache,
                            visiting,
                        )
                    } else {
                        None
                    }
                };
                if let Some(shape) = call_result_summary_shape(raw_shape) {
                    summary.set_shape(rd, shape);
                } else {
                    summary.clear_shape(rd);
                }
            }
            Opcode::Ret { rs } => {
                summary.set_return_shape(summary.aggregate_shapes.get(&rs).cloned());
            }
            _ => {
                if let Some(rd) = opcode.dest_register() {
                    summary.clear_scalar(rd);
                    summary.clear_shape(rd);
                }
            }
        }
    }
    summary.return_shape
}

fn infer_function_return_shape_cfg(
    func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    state_layout: Option<&JitStateLayout>,
    cache: &mut HashMap<u16, Option<AggregateShape>>,
    visiting: &mut HashSet<u16>,
    param_shapes: &[Option<AggregateShape>],
) -> Option<AggregateShape> {
    if func.instructions.is_empty() {
        return None;
    }

    let len = func.instructions.len();
    let mut facts = vec![None; len];
    let mut worklist = VecDeque::new();
    facts[0] = Some(seed_shape_summary(func, param_shapes));
    worklist.push_back(0);

    let mut saw_return = false;
    let mut return_shape = None;

    while let Some(pc) = worklist.pop_front() {
        let Some(summary) = facts.get(pc).and_then(Clone::clone) else {
            continue;
        };
        let opcode = func.instructions[pc];
        match opcode {
            Opcode::Ret { rs } => {
                merge_return_shape(
                    &mut saw_return,
                    &mut return_shape,
                    summary.aggregate_shapes.get(&rs).cloned(),
                );
            }
            Opcode::Jump { offset } => {
                let target = shape_forward_target(pc, offset, len)?;
                push_shape_fact(&mut facts, &mut worklist, target, summary)?;
            }
            Opcode::JumpTrue { offset, .. } | Opcode::JumpFalse { offset, .. } => {
                let target = shape_forward_target(pc, offset, len)?;
                push_shape_fact(&mut facts, &mut worklist, target, summary.clone())?;
                let fallthrough = pc.checked_add(1)?;
                if fallthrough < len {
                    push_shape_fact(&mut facts, &mut worklist, fallthrough, summary)?;
                }
            }
            _ => {
                let mut next = summary;
                apply_shape_transfer(&mut next, opcode, chunk, state_layout, cache, visiting)?;
                let fallthrough = pc.checked_add(1)?;
                if fallthrough < len {
                    push_shape_fact(&mut facts, &mut worklist, fallthrough, next)?;
                }
            }
        }
    }

    saw_return.then_some(return_shape).flatten()
}

fn merge_return_shape(
    saw_return: &mut bool,
    current: &mut Option<AggregateShape>,
    incoming: Option<AggregateShape>,
) {
    if !*saw_return {
        *current = incoming;
        *saw_return = true;
    } else {
        *current = merge_compatible_shapes(current.as_ref(), incoming.as_ref());
    }
}

fn collect_reachable_callee_arg_shapes(
    entry_func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    state_layout: Option<&JitStateLayout>,
) -> Result<HashMap<u16, Vec<Option<AggregateShape>>>, TmirError> {
    let mut callee_arg_shapes = HashMap::new();
    let mut pending = VecDeque::new();

    for op_idx in collect_callee_arg_shapes_for_function(
        entry_func,
        chunk,
        state_layout,
        &[],
        &mut callee_arg_shapes,
    )? {
        pending.push_back(op_idx);
    }

    let mut steps = 0_usize;
    while let Some(op_idx) = pending.pop_front() {
        steps = steps.checked_add(1).ok_or_else(|| {
            TmirError::Emission("callee arg shape fixed point step counter overflowed".to_owned())
        })?;
        if steps > MAX_CALLEE_ARG_SHAPE_FIXPOINT_STEPS {
            return Err(TmirError::Emission(format!(
                "callee arg shape fixed point exceeded {MAX_CALLEE_ARG_SHAPE_FIXPOINT_STEPS} steps"
            )));
        }
        let callee_func = chunk.functions.get(usize::from(op_idx)).ok_or_else(|| {
            TmirError::Emission(format!(
                "Call references function index {op_idx} but chunk has only {} functions",
                chunk.functions.len()
            ))
        })?;
        let arg_shapes = callee_arg_shapes.get(&op_idx).cloned().unwrap_or_default();
        for changed_op_idx in collect_callee_arg_shapes_for_function(
            callee_func,
            chunk,
            state_layout,
            &arg_shapes,
            &mut callee_arg_shapes,
        )? {
            pending.push_back(changed_op_idx);
        }
    }

    Ok(callee_arg_shapes)
}

fn collect_callee_arg_shapes_for_function(
    func: &BytecodeFunction,
    chunk: &BytecodeChunk,
    state_layout: Option<&JitStateLayout>,
    param_shapes: &[Option<AggregateShape>],
    callee_arg_shapes: &mut HashMap<u16, Vec<Option<AggregateShape>>>,
) -> Result<Vec<u16>, TmirError> {
    if func.instructions.is_empty() {
        return Ok(Vec::new());
    }

    let len = func.instructions.len();
    let mut facts = vec![None; len];
    let mut worklist = VecDeque::new();
    facts[0] = Some(seed_shape_summary(func, param_shapes));
    worklist.push_back(0);

    let mut changed_callees = Vec::new();
    let mut cache = HashMap::new();
    let mut visiting = HashSet::new();

    while let Some(pc) = worklist.pop_front() {
        let Some(summary) = facts.get(pc).and_then(Clone::clone) else {
            continue;
        };
        let opcode = func.instructions[pc];
        match opcode {
            Opcode::Ret { .. } => {}
            Opcode::Jump { offset } => {
                let target = resolve_target(pc, offset).map_err(|err| {
                    TmirError::Emission(format!(
                        "Call arg shape collection failed to resolve Jump at pc {pc}: {err}"
                    ))
                })?;
                if target < len {
                    push_shape_fact(&mut facts, &mut worklist, target, summary);
                }
            }
            Opcode::JumpTrue { offset, .. } | Opcode::JumpFalse { offset, .. } => {
                let target = resolve_target(pc, offset).map_err(|err| {
                    TmirError::Emission(format!(
                        "Call arg shape collection failed to resolve branch at pc {pc}: {err}"
                    ))
                })?;
                if target < len {
                    push_shape_fact(&mut facts, &mut worklist, target, summary.clone());
                }
                let fallthrough = pc.checked_add(1).ok_or_else(|| {
                    TmirError::Emission(format!(
                        "Call arg shape collection fallthrough overflow at pc {pc}"
                    ))
                })?;
                if fallthrough < len {
                    push_shape_fact(&mut facts, &mut worklist, fallthrough, summary);
                }
            }
            _ => {
                let mut next = summary;
                if let Opcode::Call {
                    op_idx,
                    args_start,
                    argc,
                    ..
                } = opcode
                {
                    let callee = chunk.functions.get(usize::from(op_idx)).ok_or_else(|| {
                        TmirError::Emission(format!(
                            "Call references function index {op_idx} but chunk has only {} functions",
                            chunk.functions.len()
                        ))
                    })?;
                    if argc != callee.arity {
                        return Err(TmirError::Emission(format!(
                            "Call arg shape collection arity mismatch at pc {pc}: callee {op_idx} expects {} args but call passes {argc}",
                            callee.arity
                        )));
                    }
                    let mut arg_shapes = Vec::with_capacity(usize::from(argc));
                    for i in 0..argc {
                        let reg = args_start.checked_add(i).ok_or_else(|| {
                            TmirError::Emission(format!(
                                "Call arg shape collection register overflow at pc {pc}: args_start={args_start} + i={i}"
                            ))
                        })?;
                        arg_shapes.push(next.aggregate_shapes.get(&reg).cloned());
                    }
                    if merge_callee_arg_shapes(callee_arg_shapes, op_idx, &callee.name, arg_shapes)?
                    {
                        changed_callees.push(op_idx);
                    }
                }

                if apply_shape_transfer(
                    &mut next,
                    opcode,
                    chunk,
                    state_layout,
                    &mut cache,
                    &mut visiting,
                )
                .is_some()
                {
                    let fallthrough = pc.checked_add(1).ok_or_else(|| {
                        TmirError::Emission(format!(
                            "Call arg shape collection fallthrough overflow at pc {pc}"
                        ))
                    })?;
                    if fallthrough < len {
                        push_shape_fact(&mut facts, &mut worklist, fallthrough, next);
                    }
                }
            }
        }
    }

    Ok(changed_callees)
}

/// Lowering context that builds tMIR directly.
///
/// Strategy: allocate one `alloca i64` per bytecode register. Opcodes
/// load from / store to these allocas. This is identical to the approach
/// in tla-llvm and produces correct code; mem2reg in the tMIR optimizer
/// converts to true SSA.
struct Ctx<'cp> {
    module: Module,
    mode: LoweringMode,
    instruction_len: usize,

    /// One alloca ValueId per bytecode register.
    register_file: Vec<ValueId>,
    /// Map from bytecode PC to tMIR block index (into the function's blocks vec).
    block_map: HashMap<usize, usize>,
    /// The function index in module.functions.
    func_idx: usize,

    /// Whether this Ctx is lowering a callee function (not the entrypoint).
    /// Scalar callees return i64 directly; fixed-width compact
    /// record/sequence/function callees copy into `callee_return_ptr` and
    /// return that encoded pointer.
    is_callee: bool,

    /// Entry context parameter ValueIds. Callees receive these for shared
    /// callout/status handling and native callout context forwarding.
    out_ptr: ValueId,
    state_in_ptr: ValueId,
    state_out_ptr: Option<ValueId>,
    /// Caller-owned fixed-width aggregate return buffer for helper callees.
    callee_return_ptr: Option<ValueId>,
    /// Compact return-buffer ABI shape selected for the active helper callee.
    callee_return_abi_shape: Option<AggregateShape>,
    /// Fixed compact return layouts required by lowered callsites.
    callee_expected_return_abi_shapes: HashMap<u16, AggregateShape>,
    /// Compact return layouts used by callees that have already been lowered.
    callee_lowered_return_abi_shapes: HashMap<u16, Option<AggregateShape>>,
    /// Registers whose function value is physically stored as the generic
    /// flat pair-list layout built by FuncDefBegin/LoopNext.
    flat_funcdef_pair_list_regs: HashSet<u8>,

    /// Next SSA value ID (monotonically increasing across all functions in the module).
    next_value: u32,
    /// Counter for auxiliary blocks (per-function, reset for each callee).
    next_aux_block: u32,

    /// Map from TIR OpIdx to tMIR FuncId for already-lowered callees.
    callee_map: HashMap<u16, FuncId>,
    /// TIR OpIdx values referenced by Call but not yet lowered.
    pending_callee_indices: Vec<u16>,
    /// Static aggregate result shape for bytecode callees in the source chunk.
    callee_return_shapes: HashMap<u16, Option<AggregateShape>>,
    /// Merged aggregate-shape metadata observed for callee formal parameters.
    callee_arg_shapes: HashMap<u16, Vec<Option<AggregateShape>>>,

    /// Active quantifier loops, keyed by destination register (`rd`).
    /// Populated by `*Begin` opcodes, consumed by `*Next` opcodes.
    quantifier_loops: HashMap<u8, QuantifierLoopState>,

    /// Stack of active builder-style loops. LoopNext does not carry `rd`
    /// or the Begin opcode kind, so we use one stack to match it to the
    /// innermost active SetFilter/FuncDef loop.
    loop_next_stack: Vec<LoopNextState>,

    /// Optional constant pool for resolving `LoadConst` and `Unchanged` opcodes.
    const_pool: Option<&'cp ConstantPool>,

    /// Source chunk for call-site-sensitive helper return-shape inference.
    source_chunk: Option<&'cp BytecodeChunk>,

    /// Optional checker-provided state layout used only for compile-time
    /// shape recovery of loaded state variables.
    state_layout: Option<JitStateLayout>,

    /// Registers loaded directly from a compact flat-state buffer, keyed by
    /// bytecode register and valued with the source pointer plus base i64 slot.
    compact_state_slots: HashMap<u8, CompactStateSlot>,

    /// Aggregate-shape metadata for registers that hold fixed-cardinality
    /// compound values. Used to preserve function/set cardinality through
    /// `LoadVar`, `Move`, and nested `FuncApply`.
    aggregate_shapes: HashMap<u8, AggregateShape>,

    /// Compile-time-known domain sizes, keyed by the bytecode register that
    /// currently holds the set aggregate. Populated by `SetEnum { count }`
    /// and `Range { lo, hi }` when `lo`/`hi` are themselves compile-time
    /// known constants. Consumed by quantifier `*Begin` lowering to emit
    /// `annotations::bounded_loop_with_n(n)` on the loop header CondBr.
    ///
    /// Invalidated whenever a register is overwritten by a non-tracked
    /// opcode (Move/Load*/arithmetic/set ops that do not re-populate).
    /// The `invalidate_reg_size` helper centralizes the removal; callers
    /// that write to a register must call it unless they explicitly know
    /// the new value's domain size.
    const_set_sizes: HashMap<u8, u32>,

    /// Known-constant i64 values, keyed by register. Populated by `LoadImm`
    /// and (transitively) arithmetic when all inputs are known. Used by
    /// `Range` to recover a compile-time bound when `lo`/`hi` are constants.
    const_scalar_values: HashMap<u8, i64>,

    /// Set to true if any lowered instruction can emit a runtime error
    /// (Halt, division-by-zero, overflow, CHOOSE-exhausted, etc.). When
    /// false at `finish()` time, the entrypoint function receives a
    /// `ProofAnnotation::NoPanic`.
    ///
    /// This is an over-approximation: we flip to `true` whenever the
    /// generic runtime-error emitter is invoked AND whenever any
    /// potentially-trapping opcode is lowered (checked arithmetic,
    /// checked division). False-positives (marking a function as able
    /// to panic when it actually cannot) are safe; the alternative
    /// (marking a panicking function as NoPanic) would be unsound.
    encountered_runtime_error: bool,

    /// Set to true when any quantifier-style loop was lowered with an
    /// unknown domain size. At `finish()` time, a function without any
    /// unknown-bound loops receives `ProofAnnotation::Terminates`.
    has_unbounded_loop: bool,
}

impl<'cp> Ctx<'cp> {
    fn new(
        bytecode_func: &BytecodeFunction,
        func_name: &str,
        mode: LoweringMode,
        const_pool: Option<&'cp ConstantPool>,
        state_layout: Option<&JitStateLayout>,
        source_chunk: Option<&'cp BytecodeChunk>,
    ) -> Result<Self, TmirError> {
        if bytecode_func.instructions.is_empty() {
            return Err(TmirError::NotEligible {
                reason: "empty bytecode function".to_owned(),
            });
        }

        if bytecode_func.arity != 0 {
            return Err(TmirError::NotEligible {
                reason: format!(
                    "tMIR lowering requires arity 0 entrypoints, got arity {}",
                    bytecode_func.arity
                ),
            });
        }

        let block_targets = collect_block_targets(&bytecode_func.instructions)?;

        let mut module = Module::new(func_name);

        // Define the function type.
        let func_ty = match mode {
            LoweringMode::Invariant => tmir::ty::FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr, Ty::I32],
                returns: vec![],
                is_vararg: false,
            },
            LoweringMode::NextState => tmir::ty::FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::I32],
                returns: vec![],
                is_vararg: false,
            },
        };
        let ft_id = module.add_func_type(func_ty);

        // Allocate parameter value IDs.
        let mut next_value: u32 = 0;
        let mut alloc_val = || {
            let v = ValueId::new(next_value);
            next_value += 1;
            v
        };

        let out_ptr = alloc_val();
        let state_in_ptr = alloc_val();
        let state_out_ptr = if mode == LoweringMode::NextState {
            Some(alloc_val())
        } else {
            None
        };
        let _state_len = alloc_val(); // state_len parameter (unused but part of signature)

        // Create entry block with parameter bindings.
        let entry_block_id = BlockId::new(0);
        let mut entry_params = vec![(out_ptr, Ty::Ptr), (state_in_ptr, Ty::Ptr)];
        if let Some(sop) = state_out_ptr {
            entry_params.push((sop, Ty::Ptr));
        }
        entry_params.push((_state_len, Ty::I32));

        let mut entry_block = Block::new(entry_block_id);
        entry_block.params = entry_params;

        // Create blocks for all bytecode branch targets.
        // Block 0 = entry, then one block per branch target PC.
        let mut blocks = vec![entry_block];
        let mut block_map = HashMap::new();
        block_map.insert(0_usize, 0_usize); // PC 0 -> block index 0

        let mut next_block_idx = 1_u32;
        for &target_pc in block_targets.iter() {
            if target_pc == 0 {
                continue;
            }
            let block_id = BlockId::new(next_block_idx);
            let block = Block::new(block_id);
            let idx = blocks.len();
            blocks.push(block);
            block_map.insert(target_pc, idx);
            next_block_idx += 1;
        }

        // Allocate register file: one alloca i64 per bytecode register.
        let mut register_file = Vec::new();
        let mut alloca_insts = Vec::new();
        for _reg in 0..=bytecode_func.max_register {
            let alloca_val = ValueId::new(next_value);
            next_value += 1;
            register_file.push(alloca_val);
            alloca_insts.push(
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(alloca_val),
            );
        }

        // Prepend alloca instructions to the entry block.
        let entry = &mut blocks[0];
        // Insert allocas at the beginning of the entry block body.
        for inst in alloca_insts.into_iter().rev() {
            entry.body.insert(0, inst);
        }

        // Build the function.
        let func = tmir::Function::new(
            tmir::value::FuncId::new(0),
            func_name,
            ft_id,
            entry_block_id,
        );
        // We'll set the blocks later.
        module.functions.push(tmir::Function { blocks, ..func });

        Ok(Self {
            module,
            mode,
            instruction_len: bytecode_func.instructions.len(),
            register_file,
            block_map,
            func_idx: 0,
            is_callee: false,
            out_ptr,
            state_in_ptr,
            state_out_ptr,
            callee_return_ptr: None,
            callee_return_abi_shape: None,
            callee_expected_return_abi_shapes: HashMap::new(),
            callee_lowered_return_abi_shapes: HashMap::new(),
            flat_funcdef_pair_list_regs: HashSet::new(),
            next_value,
            next_aux_block: next_block_idx,
            callee_map: HashMap::new(),
            pending_callee_indices: Vec::new(),
            callee_return_shapes: HashMap::new(),
            callee_arg_shapes: HashMap::new(),
            quantifier_loops: HashMap::new(),
            loop_next_stack: Vec::new(),
            const_pool,
            source_chunk,
            state_layout: state_layout.cloned(),
            compact_state_slots: HashMap::new(),
            aggregate_shapes: HashMap::new(),
            const_set_sizes: HashMap::new(),
            const_scalar_values: HashMap::new(),
            encountered_runtime_error: false,
            has_unbounded_loop: false,
        })
    }

    fn finish(mut self) -> Module {
        self.annotate_entry_function();
        self.module
    }

    /// Attach function-level proof annotations to the entrypoint function
    /// based on observations collected during lowering.
    ///
    /// The entrypoint (`FuncId(0)`, at `module.functions[0]`) is the only
    /// function we have global visibility into — callees are lowered
    /// iteratively and may carry their own annotations in a future pass.
    ///
    /// Annotations emitted:
    /// - `Pure`: Invariant entrypoints with no atomic/volatile/fence
    ///   instructions and no global mutation. Next-state/action ABI
    ///   entrypoints write through caller-provided output buffers, which is
    ///   stronger than LLVM2's current `Pure` proof contract allows.
    /// - `Deterministic`: Always true for our lowering (the tree-walking
    ///   interpreter oracle produces deterministic output given the same
    ///   state; tMIR lowering preserves this).
    /// - `Terminates`: No unbounded loops observed.
    /// - `NoPanic`: No runtime-error-emitting opcodes were lowered.
    fn annotate_entry_function(&mut self) {
        // Only annotate the entrypoint — FuncId(0). Callee annotations are
        // left for a future pass that can do interprocedural analysis.
        if self.module.functions.is_empty() {
            return;
        }

        let has_side_effects = self.function_has_side_effects(0);
        let func = &mut self.module.functions[0];

        if self.mode == LoweringMode::Invariant && !has_side_effects {
            push_unique_proof(&mut func.proofs, tmir::proof::ProofAnnotation::Pure);
        }

        // Deterministic: tMIR lowering is a deterministic translation of
        // deterministic bytecode. Always set.
        push_unique_proof(
            &mut func.proofs,
            tmir::proof::ProofAnnotation::Deterministic,
        );

        if !self.has_unbounded_loop {
            push_unique_proof(&mut func.proofs, tmir::proof::ProofAnnotation::Terminates);
        }

        if !self.encountered_runtime_error {
            push_unique_proof(&mut func.proofs, tmir::proof::ProofAnnotation::NoPanic);
        }
    }

    /// Return true if any instruction in `func_idx` is a concurrency /
    /// side-effecting operation that would disqualify the `Pure` annotation.
    ///
    /// Entrypoint `Store`s to `out_ptr` / `state_out_ptr` are the function's
    /// output contract and are not generic side effects for the rest of the
    /// proof lattice. Next-state entrypoints are still withheld from `Pure`
    /// separately because LLVM2's current `Pure` proof is too strong for
    /// caller-visible output-buffer writes.
    fn function_has_side_effects(&self, func_idx: usize) -> bool {
        let func = &self.module.functions[func_idx];
        for block in &func.blocks {
            for node in &block.body {
                match node.inst {
                    // Concurrency primitives are side effects.
                    Inst::AtomicRMW { .. } | Inst::CmpXchg { .. } | Inst::Fence { .. } => {
                        return true;
                    }
                    // Volatile stores are side effects even in entrypoints.
                    Inst::Store { volatile: true, .. } => return true,
                    Inst::Load { volatile: true, .. } => return true,
                    _ => {}
                }
            }
        }
        false
    }

    /// Add the header-CondBr `Custom(BOUNDED_LOOP_N)` annotation for a
    /// freshly-built quantifier/funcdef loop header, if the domain size is
    /// compile-time known.
    ///
    /// Returns whether an annotation was emitted (so callers can update
    /// `has_unbounded_loop` accordingly).
    ///
    /// This must be called AFTER the `CondBr` at the end of the header
    /// block has been emitted. It mutates that terminator's `proofs` vec.
    pub(super) fn annotate_loop_bound(&mut self, header_block: usize, r_domain: u8) -> bool {
        let n = if let Some(&n) = self.const_set_sizes.get(&r_domain) {
            n
        } else if let Some(AggregateShape::SetBitmask { universe_len, .. }) =
            self.aggregate_shapes.get(&r_domain)
        {
            *universe_len
        } else {
            return false;
        };

        let tag = crate::annotations::bounded_loop_with_n(n);
        let proof = tmir::proof::ProofAnnotation::Custom(tag);

        // The header's terminator is the last node in `header_block.body`.
        let func = &mut self.module.functions[self.func_idx];
        if let Some(last) = func.blocks[header_block].body.last_mut() {
            push_unique_proof(&mut last.proofs, proof);
        }
        true
    }

    /// Add the `Custom(PARALLEL_MAP)` annotation on a FuncDef loop header.
    /// Call site: after the header CondBr has been emitted.
    pub(super) fn annotate_parallel_map(&mut self, header_block: usize) {
        let proof = tmir::proof::ProofAnnotation::Custom(crate::annotations::PARALLEL_MAP);
        let func = &mut self.module.functions[self.func_idx];
        if let Some(last) = func.blocks[header_block].body.last_mut() {
            push_unique_proof(&mut last.proofs, proof);
        }
    }

    /// Record a known-constant set size for a destination register.
    pub(super) fn record_set_size(&mut self, rd: u8, size: u32) {
        self.const_set_sizes.insert(rd, size);
    }

    /// Record a known-constant scalar value for a destination register.
    pub(super) fn record_scalar(&mut self, rd: u8, value: i64) {
        self.compact_state_slots.remove(&rd);
        self.flat_funcdef_pair_list_regs.remove(&rd);
        self.const_scalar_values.insert(rd, value);
    }

    pub(super) fn mark_flat_funcdef_pair_list(&mut self, reg: u8) {
        self.compact_state_slots.remove(&reg);
        self.flat_funcdef_pair_list_regs.insert(reg);
    }

    pub(super) fn clear_flat_funcdef_pair_list(&mut self, reg: u8) {
        self.flat_funcdef_pair_list_regs.remove(&reg);
    }

    pub(super) fn is_flat_funcdef_pair_list(&self, reg: u8) -> bool {
        self.flat_funcdef_pair_list_regs.contains(&reg)
    }

    /// Look up the known scalar value held in a register, if any.
    pub(super) fn scalar_of(&self, reg: u8) -> Option<i64> {
        self.const_scalar_values.get(&reg).copied()
    }

    pub(super) fn scalar_record_selector_mode(&self, reg: u8) -> RecordSelectorMode {
        record_selector_mode(self.aggregate_shapes.get(&reg))
    }

    pub(super) fn finite_set_len_bound_of(&self, reg: u8) -> Option<u32> {
        self.aggregate_shapes
            .get(&reg)
            .and_then(AggregateShape::finite_set_len_bound)
    }

    pub(super) fn reject_compact_set_bitmask_powerset_iteration(
        &self,
        reg: u8,
        opcode_label: &str,
    ) -> Result<(), TmirError> {
        if self
            .aggregate_shapes
            .get(&reg)
            .is_some_and(AggregateShape::is_powerset_of_compact_set_bitmask)
        {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{opcode_label}: lazy SUBSET over compact SetBitmask cannot be iterated until submask iteration is implemented"
            )));
        }
        Ok(())
    }

    pub(super) fn call_arg_shapes(
        &self,
        args_start: u8,
        argc: u8,
    ) -> Result<Vec<Option<AggregateShape>>, TmirError> {
        let mut arg_shapes = Vec::with_capacity(usize::from(argc));
        for i in 0..argc {
            let reg = args_start.checked_add(i).ok_or_else(|| {
                TmirError::Emission(format!(
                    "Call argument register overflow: args_start={args_start} + i={i}"
                ))
            })?;
            arg_shapes.push(self.aggregate_shapes.get(&reg).cloned());
        }
        Ok(arg_shapes)
    }

    fn seed_callee_arg_shapes(&mut self, op_idx: u16, arity: usize) {
        let Some(arg_shapes) = self.callee_arg_shapes.get(&op_idx).cloned() else {
            return;
        };
        for (idx, shape) in arg_shapes.into_iter().take(arity).enumerate() {
            let Some(shape) = shape else {
                continue;
            };
            let Ok(reg) = u8::try_from(idx) else {
                break;
            };
            let shape = if matches!(
                &shape,
                AggregateShape::Record { .. } | AggregateShape::Sequence { .. }
            ) {
                Self::compact_return_abi_shape(Some(shape.clone())).unwrap_or(shape)
            } else {
                shape
            };
            if let Some(len) = shape.tracked_len().or_else(|| shape.finite_set_len_bound()) {
                self.const_set_sizes.insert(reg, len);
            } else {
                self.const_set_sizes.remove(&reg);
            }
            if matches!(shape, AggregateShape::Function { .. }) {
                self.mark_flat_funcdef_pair_list(reg);
            } else {
                self.clear_flat_funcdef_pair_list(reg);
            }
            if matches!(
                shape,
                AggregateShape::Record { .. } | AggregateShape::Sequence { .. }
            ) && shape.compact_slot_count().is_some()
            {
                if let Some(&reg_slot) = self.register_file.get(idx) {
                    self.compact_state_slots
                        .insert(reg, CompactStateSlot::register_backed(reg_slot, 0));
                }
            } else {
                self.compact_state_slots.remove(&reg);
            }
            self.aggregate_shapes.insert(reg, shape);
        }
    }

    pub(super) fn inferred_callee_return_shape_for_lowered_args(
        &self,
        op_idx: u16,
        arity: usize,
    ) -> Option<AggregateShape> {
        let Some(chunk) = self.source_chunk else {
            return None;
        };
        if let Some(arg_shapes) = self.callee_arg_shapes.get(&op_idx) {
            if arg_shapes.is_empty() {
                self.callee_return_shapes.get(&op_idx).cloned().flatten()
            } else {
                infer_callee_return_shape_for_args(
                    chunk,
                    op_idx,
                    arg_shapes,
                    self.state_layout.as_ref(),
                )
            }
        } else if arity == 0 {
            self.callee_return_shapes.get(&op_idx).cloned().flatten()
        } else {
            None
        }
    }

    /// Invalidate any tracked compile-time information for a register
    /// that has just been overwritten. Called automatically by the move
    /// dispatch; other opcodes may call this if they don't themselves
    /// repopulate tracking state.
    pub(super) fn invalidate_reg_tracking(&mut self, reg: u8) {
        self.aggregate_shapes.remove(&reg);
        self.compact_state_slots.remove(&reg);
        self.flat_funcdef_pair_list_regs.remove(&reg);
        self.const_set_sizes.remove(&reg);
        self.const_scalar_values.remove(&reg);
    }

    pub(super) fn record_aggregate_shape(&mut self, reg: u8, shape: Option<AggregateShape>) {
        self.compact_state_slots.remove(&reg);
        self.flat_funcdef_pair_list_regs.remove(&reg);
        self.const_set_sizes.remove(&reg);
        self.const_scalar_values.remove(&reg);
        if let Some(shape) = shape {
            self.aggregate_shapes.insert(reg, shape);
        } else {
            self.aggregate_shapes.remove(&reg);
        }
    }

    fn uniform_register_shapes(&self, start: u8, count: u8) -> Option<Box<AggregateShape>> {
        let first = self.aggregate_shapes.get(&start)?;
        for i in 0..count {
            let reg = start.checked_add(i)?;
            if self.aggregate_shapes.get(&reg) != Some(first) {
                return None;
            }
        }
        Some(Box::new(first.clone()))
    }

    fn exact_int_set_values_from_registers(&self, start: u8, count: u8) -> Option<Vec<i64>> {
        let mut values = Vec::with_capacity(usize::from(count));
        for i in 0..count {
            let reg = start.checked_add(i)?;
            if !self
                .aggregate_shapes
                .get(&reg)
                .is_some_and(AggregateShape::is_numeric_scalar_shape)
            {
                return None;
            }
            values.push(*self.const_scalar_values.get(&reg)?);
        }
        Some(values)
    }

    pub(super) fn set_enum_scalar_int_domain_universe_from_registers(
        &self,
        start: u8,
        count: u8,
    ) -> Option<(u32, SetBitmaskUniverse)> {
        if count == 0 {
            return None;
        }
        let mut result: Option<(u32, SetBitmaskUniverse)> = None;
        for i in 0..count {
            let reg = start.checked_add(i)?;
            let current = self
                .aggregate_shapes
                .get(&reg)
                .and_then(AggregateShape::scalar_int_domain_universe)?;
            if result.as_ref().is_some_and(|existing| existing != &current) {
                return None;
            }
            result = Some(current);
        }
        result
    }

    fn set_enum_shape_from_registers(&self, start: u8, count: u8) -> AggregateShape {
        if let Some(values) = self.exact_int_set_values_from_registers(start, count) {
            return AggregateShape::ExactIntSet { values };
        }
        if let Some((universe_len, universe)) =
            self.set_enum_scalar_int_domain_universe_from_registers(start, count)
        {
            return AggregateShape::SetBitmask {
                universe_len,
                universe,
            };
        }
        AggregateShape::Set {
            len: u32::from(count),
            element: self.uniform_register_shapes(start, count),
        }
    }

    fn tracked_shape_from_compound_layout(layout: &CompoundLayout) -> Option<AggregateShape> {
        match layout {
            CompoundLayout::Function {
                pair_count: Some(n),
                value_layout,
                domain_lo,
                ..
            } => Some(AggregateShape::Function {
                len: u32::try_from(*n).ok()?,
                domain_lo: *domain_lo,
                value: Self::tracked_shape_from_compound_layout(value_layout).map(Box::new),
            }),
            CompoundLayout::Record { fields } => Some(AggregateShape::Record {
                fields: fields
                    .iter()
                    .map(|(name, layout)| {
                        (
                            *name,
                            Self::tracked_shape_from_compound_layout(layout).map(Box::new),
                        )
                    })
                    .collect(),
            }),
            CompoundLayout::Set {
                element_count: Some(n),
                ..
            } => Some(AggregateShape::SetBitmask {
                universe_len: u32::try_from(*n).ok()?,
                universe: SetBitmaskUniverse::Unknown,
            }),
            CompoundLayout::SetBitmask { universe } => Some(AggregateShape::SetBitmask {
                universe_len: u32::try_from(universe.len()).ok()?,
                universe: SetBitmaskUniverse::from_elements(universe),
            }),
            CompoundLayout::Sequence {
                element_layout,
                element_count: Some(n),
            } => Some(AggregateShape::Sequence {
                extent: SequenceExtent::Capacity(u32::try_from(*n).ok()?),
                element: Self::tracked_shape_from_compound_layout(element_layout).map(Box::new),
            }),
            CompoundLayout::Int => Some(AggregateShape::Scalar(ScalarShape::Int)),
            CompoundLayout::Bool => Some(AggregateShape::Scalar(ScalarShape::Bool)),
            CompoundLayout::String => Some(AggregateShape::Scalar(ScalarShape::String)),
            _ => None,
        }
    }

    fn compact_var_slot_count(var_layout: &VarLayout) -> Option<usize> {
        Some(var_layout.compact_slot_count())
    }

    fn compact_state_slot_offset(&self, var_idx: u16) -> Option<u32> {
        self.compact_state_slot_offset_checked(var_idx, "compact state slot offset")
            .ok()
            .flatten()
    }

    fn compact_state_slot_offset_checked(
        &self,
        var_idx: u16,
        context: &str,
    ) -> Result<Option<u32>, TmirError> {
        let Some(layout) = self.state_layout.as_ref() else {
            return Ok(None);
        };
        let target = usize::from(var_idx);
        if target >= layout.var_count() {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: state layout has {} vars but var_idx {var_idx} was requested",
                layout.var_count()
            )));
        }
        let mut offset = 0_usize;
        for idx in 0..target {
            let var_layout = layout.var_layout(idx).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "{context}: missing state layout entry for var_idx {idx}"
                ))
            })?;
            offset = offset
                .checked_add(Self::compact_var_slot_count(var_layout).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: no compact slot count for state var_idx {idx}"
                    ))
                })?)
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: compact offset overflow before var_idx {var_idx}"
                    ))
                })?;
        }
        u32::try_from(offset).map(Some).map_err(|_| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: compact offset {offset} for var_idx {var_idx} does not fit in u32"
            ))
        })
    }

    fn compact_state_slot_count_for_var_checked(
        &self,
        var_idx: u16,
        context: &str,
    ) -> Result<Option<u32>, TmirError> {
        let Some(layout) = self.state_layout.as_ref() else {
            return Ok(None);
        };
        let var_layout = layout.var_layout(usize::from(var_idx)).ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: state layout has {} vars but var_idx {var_idx} was requested",
                layout.var_count()
            ))
        })?;
        let count = Self::compact_var_slot_count(var_layout).ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: no compact slot count for state var_idx {var_idx}"
            ))
        })?;
        u32::try_from(count).map(Some).map_err(|_| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: compact slot count {count} for var_idx {var_idx} does not fit in u32"
            ))
        })
    }

    fn compact_state_slot_offset_or_legacy(
        &self,
        var_idx: u16,
        context: &str,
    ) -> Result<u32, TmirError> {
        Ok(self
            .compact_state_slot_offset_checked(var_idx, context)?
            .unwrap_or_else(|| u32::from(var_idx)))
    }

    fn compact_state_slot_count_or_legacy(
        &self,
        var_idx: u16,
        context: &str,
    ) -> Result<u32, TmirError> {
        Ok(self
            .compact_state_slot_count_for_var_checked(var_idx, context)?
            .unwrap_or(1))
    }

    fn compact_state_shape_for_var(&self, var_idx: u16) -> Option<AggregateShape> {
        let layout = self.state_layout.as_ref()?;
        match layout.var_layout(usize::from(var_idx))? {
            VarLayout::ScalarInt => Some(AggregateShape::Scalar(ScalarShape::Int)),
            VarLayout::ScalarBool => Some(AggregateShape::Scalar(ScalarShape::Bool)),
            VarLayout::Compound(layout) => Self::tracked_shape_from_compound_layout(layout),
            _ => None,
        }
    }

    fn is_single_slot_flat_aggregate_value(shape: &AggregateShape) -> bool {
        matches!(
            shape,
            AggregateShape::Scalar(_)
                | AggregateShape::ScalarIntDomain { .. }
                | AggregateShape::SetBitmask { .. }
        )
    }

    fn is_compact_compound_aggregate(shape: &AggregateShape) -> bool {
        matches!(
            shape,
            AggregateShape::Record { .. }
                | AggregateShape::Sequence { .. }
                | AggregateShape::Function { .. }
                | AggregateShape::RecordSet { .. }
        )
    }

    fn is_caller_owned_return_aggregate(shape: &AggregateShape) -> bool {
        Self::is_compact_compound_aggregate(shape)
            || shape.materialized_return_slot_count().is_some()
    }

    fn is_known_pointer_backed_return_shape(shape: &AggregateShape) -> bool {
        matches!(
            shape,
            AggregateShape::Function { .. }
                | AggregateShape::Record { .. }
                | AggregateShape::RecordSet { .. }
                | AggregateShape::Powerset { .. }
                | AggregateShape::FunctionSet { .. }
                | AggregateShape::SeqSet { .. }
                | AggregateShape::Interval { .. }
                | AggregateShape::ExactIntSet { .. }
                | AggregateShape::Set { .. }
                | AggregateShape::FiniteSet
                | AggregateShape::BoundedSet { .. }
                | AggregateShape::Sequence { .. }
        )
    }

    fn caller_owned_return_slot_count(shape: &AggregateShape) -> Option<u32> {
        if Self::is_compact_compound_aggregate(shape) {
            shape.compact_slot_count()
        } else {
            shape.materialized_return_slot_count()
        }
    }

    fn record_set_domain_return_slot_compatible(shape: &AggregateShape) -> bool {
        matches!(
            shape,
            AggregateShape::Interval { .. }
                | AggregateShape::SymbolicDomain(_)
                | AggregateShape::Scalar(_)
                | AggregateShape::ScalarIntDomain { .. }
                | AggregateShape::SetBitmask { .. }
        )
    }

    fn record_set_return_abi_compatible(shape: &AggregateShape) -> bool {
        let AggregateShape::RecordSet { fields } = shape else {
            return false;
        };
        fields
            .iter()
            .all(|(_, field_domain)| Self::record_set_domain_return_slot_compatible(field_domain))
    }

    fn copy_record_set_return_domain_slot(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        source_slot: u32,
        source_shape: &AggregateShape,
        dest_shape: &AggregateShape,
        dest_ptr: ValueId,
        dest_slot: u32,
        context: &str,
    ) -> Result<(), TmirError> {
        if source_shape != dest_shape
            || !Self::record_set_domain_return_slot_compatible(source_shape)
        {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context} requires slot-compatible RecordSet field domains, got {source_shape:?} -> {dest_shape:?}"
            )));
        }
        let value = match source_shape {
            // Interval and symbolic domains carry their semantics in the
            // tracked shape. The register slot may contain a callee-local
            // materialized domain pointer, so never copy that payload across
            // a helper return boundary.
            AggregateShape::Interval { .. } | AggregateShape::SymbolicDomain(_) => {
                self.emit_i64_const(block_idx, 0)
            }
            AggregateShape::Scalar(_)
            | AggregateShape::ScalarIntDomain { .. }
            | AggregateShape::SetBitmask { .. } => {
                self.load_at_offset(block_idx, source_ptr, source_slot)
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context} cannot return pointer-backed RecordSet field domain {other:?}"
                )));
            }
        };
        self.store_at_offset(block_idx, dest_ptr, dest_slot, value);
        Ok(())
    }

    fn same_compact_physical_layout(source: &AggregateShape, dest: &AggregateShape) -> bool {
        if source == dest {
            return true;
        }
        if Self::is_single_slot_flat_aggregate_value(source)
            && Self::is_single_slot_flat_aggregate_value(dest)
        {
            return Self::compatible_flat_aggregate_value(source, dest);
        }

        match (source, dest) {
            (
                AggregateShape::Record { fields: source },
                AggregateShape::Record { fields: dest },
            ) => {
                source.len() == dest.len()
                    && source.iter().zip(dest).all(
                        |((source_name, source_shape), (dest_name, dest_shape))| {
                            source_name == dest_name
                                && match (source_shape.as_deref(), dest_shape.as_deref()) {
                                    (Some(source_shape), Some(dest_shape)) => {
                                        Self::same_compact_physical_layout(source_shape, dest_shape)
                                    }
                                    (None, None) => true,
                                    _ => false,
                                }
                        },
                    )
            }
            (
                AggregateShape::Sequence {
                    extent: source_extent,
                    element: source_element,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) => {
                source_extent == dest_extent
                    && match (source_element.as_deref(), dest_element.as_deref()) {
                        (Some(source_element), Some(dest_element)) => {
                            Self::same_compact_physical_layout(source_element, dest_element)
                        }
                        (None, None) => true,
                        _ => false,
                    }
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: source_domain_lo,
                    value: source_value,
                },
                AggregateShape::Function {
                    len: dest_len,
                    domain_lo: dest_domain_lo,
                    value: dest_value,
                },
            ) => {
                source_len == dest_len
                    && source_domain_lo == dest_domain_lo
                    && match (source_value.as_deref(), dest_value.as_deref()) {
                        (Some(source_value), Some(dest_value)) => {
                            Self::same_compact_physical_layout(source_value, dest_value)
                        }
                        (None, None) => true,
                        _ => false,
                    }
            }
            (
                AggregateShape::RecordSet { fields: source },
                AggregateShape::RecordSet { fields: dest },
            ) => {
                source.len() == dest.len()
                    && dest.iter().all(|(dest_name, dest_shape)| {
                        source
                            .iter()
                            .find(|(source_name, _)| source_name == dest_name)
                            .is_some_and(|(_, source_shape)| source_shape == dest_shape)
                    })
            }
            _ => false,
        }
    }

    fn canonical_compact_abi_shape(shape: AggregateShape) -> AggregateShape {
        match shape {
            AggregateShape::Record { mut fields } => {
                for (_, field_shape) in &mut fields {
                    if let Some(shape) = field_shape.take() {
                        *field_shape = Some(Box::new(Self::canonical_compact_abi_shape(*shape)));
                    }
                }
                fields.sort_by_key(|(name, _)| *name);
                AggregateShape::Record { fields }
            }
            AggregateShape::Sequence { extent, element } => AggregateShape::Sequence {
                extent,
                element: element.map(|shape| Box::new(Self::canonical_compact_abi_shape(*shape))),
            },
            AggregateShape::Function {
                len,
                domain_lo,
                value,
            } => AggregateShape::Function {
                len,
                domain_lo,
                value: value.map(|shape| Box::new(Self::canonical_compact_abi_shape(*shape))),
            },
            AggregateShape::RecordSet { mut fields } => {
                fields.sort_by_key(|(name, _)| *name);
                AggregateShape::RecordSet { fields }
            }
            other => other,
        }
    }

    fn compact_return_abi_shape(shape: Option<AggregateShape>) -> Option<AggregateShape> {
        shape
            .filter(Self::is_caller_owned_return_aggregate)
            .filter(|shape| Self::caller_owned_return_slot_count(shape).is_some())
            .filter(|shape| {
                !matches!(shape, AggregateShape::RecordSet { .. })
                    || Self::record_set_return_abi_compatible(shape)
            })
            .map(Self::canonical_compact_abi_shape)
            .filter(|shape| Self::caller_owned_return_slot_count(shape).is_some())
    }

    fn complete_inferred_compact_shape_from_expected(
        inferred: &AggregateShape,
        expected: &AggregateShape,
    ) -> Option<AggregateShape> {
        expected.fixed_width_slot_count_for_shape_completion()?;
        let completed =
            Self::complete_inferred_compact_shape_from_expected_inner(inferred, expected)?;
        if completed
            .fixed_width_slot_count_for_shape_completion()
            .is_some()
            && Self::compatible_compact_materialization_value(&completed, expected)
        {
            Some(completed)
        } else {
            None
        }
    }

    fn complete_inferred_compact_shape_from_expected_inner(
        inferred: &AggregateShape,
        expected: &AggregateShape,
    ) -> Option<AggregateShape> {
        if inferred == expected && Self::caller_owned_return_slot_count(expected).is_some() {
            return Some(inferred.clone());
        }

        if Self::is_single_slot_flat_aggregate_value(inferred)
            && Self::is_single_slot_flat_aggregate_value(expected)
            && Self::compatible_flat_aggregate_value(inferred, expected)
        {
            return Some(inferred.clone());
        }

        match (inferred, expected) {
            (
                AggregateShape::Record { fields: inferred },
                AggregateShape::Record { fields: expected },
            ) => {
                if inferred.len() != expected.len() {
                    return None;
                }
                let mut fields = Vec::with_capacity(inferred.len());
                for (name, inferred_shape) in inferred {
                    let (_, expected_shape) = expected
                        .iter()
                        .find(|(expected_name, _)| expected_name == name)?;
                    let expected_shape = expected_shape.as_deref()?;
                    fields.push((
                        *name,
                        Some(Box::new(Self::complete_optional_inferred_compact_shape(
                            inferred_shape.as_deref(),
                            expected_shape,
                        )?)),
                    ));
                }
                Some(AggregateShape::Record { fields })
            }
            (
                AggregateShape::Sequence {
                    extent: inferred_extent,
                    element: inferred_element,
                },
                AggregateShape::Sequence {
                    extent: expected_extent,
                    element: expected_element,
                },
            ) => {
                if inferred_extent.capacity() != expected_extent.capacity() {
                    return None;
                }
                let element = if inferred_extent.capacity() == 0 {
                    match (inferred_element.as_deref(), expected_element.as_deref()) {
                        (Some(inferred_element), Some(expected_element)) => Some(Box::new(
                            Self::complete_inferred_compact_shape_from_expected_inner(
                                inferred_element,
                                expected_element,
                            )?,
                        )),
                        _ => inferred_element.clone(),
                    }
                } else {
                    let inferred_element = inferred_element.as_deref()?;
                    Some(Box::new(Self::complete_optional_inferred_compact_shape(
                        Some(inferred_element),
                        expected_element.as_deref()?,
                    )?))
                };
                Some(AggregateShape::Sequence {
                    extent: *inferred_extent,
                    element,
                })
            }
            (
                AggregateShape::Function {
                    len: inferred_len,
                    domain_lo: Some(1),
                    value: inferred_value,
                },
                AggregateShape::Sequence {
                    extent: expected_extent,
                    element: expected_element,
                },
            ) => {
                if *inferred_len != expected_extent.capacity() {
                    return None;
                }
                let value = if *inferred_len == 0 {
                    inferred_value.clone().or_else(|| expected_element.clone())
                } else {
                    let inferred_value = inferred_value.as_deref()?;
                    Some(Box::new(Self::complete_optional_inferred_compact_shape(
                        Some(inferred_value),
                        expected_element.as_deref()?,
                    )?))
                };
                Some(AggregateShape::Function {
                    len: *inferred_len,
                    domain_lo: Some(1),
                    value,
                })
            }
            (
                AggregateShape::Function {
                    len: inferred_len,
                    domain_lo: inferred_domain_lo,
                    value: inferred_value,
                },
                AggregateShape::Function {
                    len: expected_len,
                    domain_lo: expected_domain_lo,
                    value: expected_value,
                },
            ) => {
                if inferred_len != expected_len || inferred_domain_lo != expected_domain_lo {
                    return None;
                }
                let value = if *inferred_len == 0 {
                    inferred_value.clone().or_else(|| expected_value.clone())
                } else {
                    let inferred_value = inferred_value.as_deref()?;
                    Some(Box::new(Self::complete_optional_inferred_compact_shape(
                        Some(inferred_value),
                        expected_value.as_deref()?,
                    )?))
                };
                Some(AggregateShape::Function {
                    len: *inferred_len,
                    domain_lo: *inferred_domain_lo,
                    value,
                })
            }
            (
                AggregateShape::RecordSet { fields: inferred },
                AggregateShape::RecordSet { fields: expected },
            ) => {
                if inferred.len() != expected.len() {
                    return None;
                }
                let mut fields = Vec::with_capacity(inferred.len());
                for (name, inferred_shape) in inferred {
                    let (_, expected_shape) = expected
                        .iter()
                        .find(|(expected_name, _)| expected_name == name)?;
                    if inferred_shape != expected_shape
                        || !Self::record_set_domain_return_slot_compatible(inferred_shape)
                    {
                        return None;
                    }
                    fields.push((*name, inferred_shape.clone()));
                }
                Some(AggregateShape::RecordSet { fields })
            }
            _ => None,
        }
    }

    fn complete_optional_inferred_compact_shape(
        inferred: Option<&AggregateShape>,
        expected: &AggregateShape,
    ) -> Option<AggregateShape> {
        expected.fixed_width_slot_count_for_shape_completion()?;
        match inferred {
            Some(inferred) => {
                Self::complete_inferred_compact_shape_from_expected_inner(inferred, expected)
            }
            None => Self::complete_missing_inferred_compact_shape_from_expected(expected),
        }
    }

    fn complete_missing_inferred_compact_shape_from_expected(
        expected: &AggregateShape,
    ) -> Option<AggregateShape> {
        expected.fixed_width_slot_count_for_shape_completion()?;
        if Self::is_single_slot_flat_aggregate_value(expected) {
            Some(expected.clone())
        } else {
            None
        }
    }

    pub(super) fn record_callee_expected_return_abi_shape(
        &mut self,
        op_idx: u16,
        shape: &AggregateShape,
    ) -> Result<(), TmirError> {
        let shape = Self::compact_return_abi_shape(Some(shape.clone())).ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact compound return for callee {op_idx} requires fixed-width ABI shape, got {shape:?}"
            ))
        })?;
        if let Some(existing) = self.callee_expected_return_abi_shapes.get(&op_idx) {
            if !Self::same_compact_physical_layout(existing, &shape) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "Call compact compound return ABI for callee {op_idx} differs between caller and callee callsites: existing={existing:?}, incoming={shape:?}"
                )));
            }
        } else {
            self.callee_expected_return_abi_shapes
                .insert(op_idx, shape.clone());
        }
        if let Some(lowered) = self.callee_lowered_return_abi_shapes.get(&op_idx) {
            match lowered {
                Some(lowered) if Self::same_compact_physical_layout(lowered, &shape) => {}
                Some(lowered) => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "Call compact compound return ABI for callee {op_idx} was discovered after the callee was lowered with a different ABI: lowered={lowered:?}, incoming={shape:?}"
                    )));
                }
                None => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "Call compact compound return ABI for callee {op_idx} was discovered after the callee was lowered without a compact return buffer: incoming={shape:?}"
                    )));
                }
            }
        }
        Ok(())
    }

    fn compact_return_abi_shape_for_callee(
        &self,
        op_idx: u16,
        inferred: Option<AggregateShape>,
    ) -> Result<Option<AggregateShape>, TmirError> {
        let expected = self.callee_expected_return_abi_shapes.get(&op_idx);
        match (inferred, expected) {
            (Some(inferred), Some(expected)) => {
                let completed = Self::complete_inferred_compact_shape_from_expected(
                    &inferred, expected,
                )
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "callee compact compound return for callee {op_idx} is incompatible with expected ABI shape: inferred={inferred:?}, expected={expected:?}"
                    ))
                })?;
                let abi_shape = Self::compact_return_abi_shape(Some(completed)).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "callee compact compound return for callee {op_idx} did not complete to a fixed ABI shape: inferred={inferred:?}, expected={expected:?}"
                    ))
                })?;
                if !Self::same_compact_physical_layout(&abi_shape, expected) {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "callee compact compound return for callee {op_idx} completed to ABI shape {abi_shape:?}, which differs from expected ABI shape {expected:?}"
                    )));
                }
                Ok(Some(abi_shape))
            }
            (None, Some(expected)) => Ok(Some(expected.clone())),
            (Some(inferred), None) => Ok(Self::compact_return_abi_shape(Some(inferred))),
            (None, None) => Ok(None),
        }
    }

    fn compatible_flat_aggregate_value(source: &AggregateShape, dest: &AggregateShape) -> bool {
        match (source, dest) {
            (AggregateShape::Scalar(source), AggregateShape::Scalar(dest)) => source == dest,
            (AggregateShape::ScalarIntDomain { .. }, AggregateShape::Scalar(ScalarShape::Int))
            | (AggregateShape::Scalar(ScalarShape::Int), AggregateShape::ScalarIntDomain { .. }) => {
                true
            }
            (
                AggregateShape::ScalarIntDomain {
                    universe_len: source_len,
                    universe: source_universe,
                },
                AggregateShape::ScalarIntDomain {
                    universe_len: dest_len,
                    universe: dest_universe,
                },
            ) => source_len == dest_len && source_universe == dest_universe,
            (
                AggregateShape::SetBitmask {
                    universe_len,
                    universe,
                },
                dest,
            ) => dest.compatible_set_bitmask_universe(*universe_len, universe),
            (
                AggregateShape::Record { fields: source },
                AggregateShape::Record { fields: dest },
            ) => {
                if source.len() != dest.len() {
                    return false;
                }
                dest.iter().all(|(dest_name, dest_shape)| {
                    let Some((_, source_shape)) = source
                        .iter()
                        .find(|(source_name, _)| source_name == dest_name)
                    else {
                        return false;
                    };
                    let (Some(source_shape), Some(dest_shape)) =
                        (source_shape.as_deref(), dest_shape.as_deref())
                    else {
                        return false;
                    };
                    Self::compatible_flat_aggregate_value(source_shape, dest_shape)
                })
            }
            (
                AggregateShape::Sequence {
                    extent: source_extent,
                    element: source_element,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) => {
                let source_capacity = source_extent.capacity();
                let dest_capacity = dest_extent.capacity();
                if source_capacity != dest_capacity {
                    return false;
                }
                if source_capacity == 0 {
                    return true;
                }
                let (Some(source_element), Some(dest_element)) =
                    (source_element.as_deref(), dest_element.as_deref())
                else {
                    return false;
                };
                Self::compatible_flat_aggregate_value(source_element, dest_element)
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: source_domain_lo,
                    value: source_value,
                },
                AggregateShape::Function {
                    len: dest_len,
                    domain_lo: dest_domain_lo,
                    value: dest_value,
                },
            ) => {
                if source_len != dest_len {
                    return false;
                }
                if source_domain_lo != dest_domain_lo {
                    return false;
                }
                if *source_len == 0 {
                    return true;
                }
                let (Some(source_value), Some(dest_value)) =
                    (source_value.as_deref(), dest_value.as_deref())
                else {
                    return false;
                };
                Self::compatible_flat_aggregate_value(source_value, dest_value)
            }
            _ => false,
        }
    }

    fn contains_compact_sequence(shape: &AggregateShape) -> bool {
        match shape {
            AggregateShape::Sequence { .. } => true,
            AggregateShape::Function {
                value: Some(value), ..
            } => Self::contains_compact_sequence(value),
            AggregateShape::Record { fields } => fields.iter().any(|(_, field)| {
                field
                    .as_deref()
                    .is_some_and(Self::contains_compact_sequence)
            }),
            _ => false,
        }
    }

    fn compatible_compact_materialization_value(
        source: &AggregateShape,
        dest: &AggregateShape,
    ) -> bool {
        if source == dest && source.materialized_return_slot_count().is_some() {
            return true;
        }
        match (source, dest) {
            (AggregateShape::Scalar(source), AggregateShape::Scalar(dest)) => source == dest,
            (AggregateShape::ScalarIntDomain { .. }, AggregateShape::Scalar(ScalarShape::Int))
            | (AggregateShape::Scalar(ScalarShape::Int), AggregateShape::ScalarIntDomain { .. }) => {
                true
            }
            (
                AggregateShape::ScalarIntDomain {
                    universe_len: source_len,
                    universe: source_universe,
                },
                AggregateShape::ScalarIntDomain {
                    universe_len: dest_len,
                    universe: dest_universe,
                },
            ) => source_len == dest_len && source_universe == dest_universe,
            (
                AggregateShape::SetBitmask {
                    universe_len,
                    universe,
                },
                dest,
            ) => dest.compatible_set_bitmask_universe(*universe_len, universe),
            (
                AggregateShape::Record { fields: source },
                AggregateShape::Record { fields: dest },
            ) => {
                if source.len() != dest.len() {
                    return false;
                }
                dest.iter().all(|(dest_name, dest_shape)| {
                    let Some((_, source_shape)) = source
                        .iter()
                        .find(|(source_name, _)| source_name == dest_name)
                    else {
                        return false;
                    };
                    let (Some(source_shape), Some(dest_shape)) =
                        (source_shape.as_deref(), dest_shape.as_deref())
                    else {
                        return false;
                    };
                    Self::compatible_compact_materialization_value(source_shape, dest_shape)
                })
            }
            (
                AggregateShape::Sequence {
                    extent: source_extent,
                    element: source_element,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) => {
                let source_capacity = source_extent.capacity();
                let dest_capacity = dest_extent.capacity();
                if source_capacity > dest_capacity {
                    return false;
                }
                if dest_capacity == 0 {
                    return true;
                }
                let Some(dest_element) = dest_element.as_deref() else {
                    return false;
                };
                if source_capacity == 0 {
                    return dest_element.compact_slot_count().is_some();
                }
                let Some(source_element) = source_element.as_deref() else {
                    return false;
                };
                Self::compatible_compact_materialization_value(source_element, dest_element)
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: Some(1),
                    value: source_value,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) => {
                if *source_len != dest_extent.capacity() {
                    return false;
                }
                if *source_len == 0 {
                    return true;
                }
                let Some(dest_element) = dest_element.as_deref() else {
                    return false;
                };
                let Some(source_value) = source_value.as_deref() else {
                    return false;
                };
                Self::compatible_compact_materialization_value(source_value, dest_element)
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: source_domain_lo,
                    value: source_value,
                },
                AggregateShape::Function {
                    len: dest_len,
                    domain_lo: dest_domain_lo,
                    value: dest_value,
                },
            ) => {
                if source_len != dest_len || source_domain_lo != dest_domain_lo {
                    return false;
                }
                if *source_len == 0 {
                    return true;
                }
                let (Some(source_value), Some(dest_value)) =
                    (source_value.as_deref(), dest_value.as_deref())
                else {
                    return false;
                };
                Self::compatible_compact_materialization_value(source_value, dest_value)
            }
            (
                AggregateShape::RecordSet { fields: source },
                AggregateShape::RecordSet { fields: dest },
            ) => {
                if source.len() != dest.len() {
                    return false;
                }
                dest.iter().all(|(dest_name, dest_shape)| {
                    source
                        .iter()
                        .find(|(source_name, _)| source_name == dest_name)
                        .is_some_and(|(_, source_shape)| {
                            source_shape == dest_shape
                                && Self::record_set_domain_return_slot_compatible(source_shape)
                        })
                })
            }
            _ => false,
        }
    }

    fn can_copy_flat_aggregate_to_compact_slots(
        source: &AggregateShape,
        dest: &AggregateShape,
    ) -> bool {
        match (source, dest) {
            (AggregateShape::Record { .. }, AggregateShape::Record { .. })
            | (AggregateShape::Sequence { .. }, AggregateShape::Sequence { .. })
            | (AggregateShape::Function { .. }, AggregateShape::Sequence { .. })
            | (AggregateShape::Function { .. }, AggregateShape::Function { .. })
            | (AggregateShape::RecordSet { .. }, AggregateShape::RecordSet { .. }) => {
                dest.compact_slot_count().is_some()
                    && Self::compatible_compact_materialization_value(source, dest)
            }
            _ => false,
        }
    }

    fn static_set_bitmask_materialization_mask(
        source_shape: &AggregateShape,
        dest_shape: &AggregateShape,
        context: &str,
    ) -> Result<Option<i64>, TmirError> {
        let AggregateShape::SetBitmask {
            universe_len,
            universe,
        } = dest_shape
        else {
            return Ok(None);
        };
        Self::compact_set_bitmask_valid_mask(*universe_len, context)?;

        match source_shape {
            AggregateShape::ExactIntSet { values } => {
                exact_int_set_mask_for_set_bitmask_universe(values, *universe_len, universe)
                    .map(Some)
                    .ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "{context}: exact integer Set source requires all values inside the destination SetBitmask universe, got source_shape={source_shape:?}, dest_shape={dest_shape:?}"
                        ))
                    })
            }
            AggregateShape::Set { len: 0, .. } => Ok(Some(0)),
            _ => Ok(None),
        }
    }

    fn copy_flat_slot_value_to_compact_slots(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        source_slot: u32,
        source_shape: &AggregateShape,
        dest_shape: &AggregateShape,
        dest_ptr: ValueId,
        dst_slot: u32,
    ) -> Result<CompactCopyResult, TmirError> {
        if Self::is_single_slot_flat_aggregate_value(source_shape)
            && Self::is_single_slot_flat_aggregate_value(dest_shape)
            && Self::compatible_flat_aggregate_value(source_shape, dest_shape)
        {
            let value = self.load_at_offset(block_idx, source_ptr, source_slot);
            self.store_at_offset(block_idx, dest_ptr, dst_slot, value);
            return Ok(CompactCopyResult {
                slots_written: 1,
                block_idx,
            });
        }

        if Self::is_compact_compound_aggregate(source_shape)
            && Self::is_compact_compound_aggregate(dest_shape)
            && Self::compatible_compact_materialization_value(source_shape, dest_shape)
        {
            let nested_ptr_i64 = self.load_at_offset(block_idx, source_ptr, source_slot);
            let nested_ptr = self.emit_with_result(
                block_idx,
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I64,
                    dst_ty: Ty::Ptr,
                    operand: nested_ptr_i64,
                },
            );
            if matches!(
                source_shape,
                AggregateShape::Sequence {
                    extent: SequenceExtent::Capacity(_),
                    ..
                }
            ) {
                return self.copy_compact_aggregate_to_compact_slots(
                    block_idx,
                    nested_ptr,
                    0,
                    source_shape,
                    dest_shape,
                    dest_ptr,
                    dst_slot,
                );
            }
            return self.copy_flat_aggregate_to_compact_slots(
                block_idx,
                nested_ptr,
                source_shape,
                dest_shape,
                dest_ptr,
                dst_slot,
                false,
            );
        }

        Err(TmirError::UnsupportedOpcode(format!(
            "compact flat aggregate slot copy requires compatible fixed-width source/destination shapes, got {source_shape:?} -> {dest_shape:?}"
        )))
    }

    fn copy_captured_compact_slot_value_to_compact_slots(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        source_slot: u32,
        source_shape: &AggregateShape,
        dest_shape: &AggregateShape,
        dest_ptr: ValueId,
        dst_slot: u32,
    ) -> Result<CompactCopyResult, TmirError> {
        if Self::is_single_slot_flat_aggregate_value(source_shape)
            && Self::is_single_slot_flat_aggregate_value(dest_shape)
            && Self::compatible_flat_aggregate_value(source_shape, dest_shape)
        {
            let value = self.load_at_offset(block_idx, source_ptr, source_slot);
            self.store_at_offset(block_idx, dest_ptr, dst_slot, value);
            return Ok(CompactCopyResult {
                slots_written: 1,
                block_idx,
            });
        }

        if Self::is_compact_compound_aggregate(source_shape)
            && Self::is_compact_compound_aggregate(dest_shape)
            && Self::compatible_compact_materialization_value(source_shape, dest_shape)
        {
            let nested_ptr_i64 = self.load_at_offset(block_idx, source_ptr, source_slot);
            let nested_ptr = self.emit_with_result(
                block_idx,
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I64,
                    dst_ty: Ty::Ptr,
                    operand: nested_ptr_i64,
                },
            );
            return self.copy_compact_aggregate_to_compact_slots(
                block_idx,
                nested_ptr,
                0,
                source_shape,
                dest_shape,
                dest_ptr,
                dst_slot,
            );
        }

        Err(TmirError::UnsupportedOpcode(format!(
            "captured FuncDef compact slot copy requires compatible fixed-width source/destination shapes, got {source_shape:?} -> {dest_shape:?}"
        )))
    }

    fn zero_compact_slots(
        &mut self,
        block_idx: usize,
        dest_ptr: ValueId,
        dst_base: u32,
        slot_count: u32,
        zero: ValueId,
    ) -> Result<(), TmirError> {
        for offset in 0..slot_count {
            let dst_slot = dst_base.checked_add(offset).ok_or_else(|| {
                TmirError::UnsupportedOpcode(
                    "compact slot zero destination offset overflows u32".to_owned(),
                )
            })?;
            self.store_at_offset(block_idx, dest_ptr, dst_slot, zero);
        }
        Ok(())
    }

    fn guard_compact_sequence_len_in_bounds<T>(
        &mut self,
        block_idx: usize,
        len_value: ValueId,
        capacity: u32,
        context: &str,
    ) -> T
    where
        T: From<CompactSequenceLenGuardResult>,
    {
        let zero = self.emit_i64_const(block_idx, 0);
        let non_negative = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sge,
                ty: Ty::I64,
                lhs: len_value,
                rhs: zero,
            },
        );

        let check_capacity_blk = self.new_aux_block(&format!("{context}_check_capacity"));
        let ok_blk = self.new_aux_block(&format!("{context}_ok"));
        let error_blk = self.new_aux_block(&format!("{context}_error"));
        let check_len_value = self.add_block_param(check_capacity_blk, Ty::I64);
        let ok_len_value = self.add_block_param(ok_blk, Ty::I64);
        let check_capacity_id = self.block_id_of(check_capacity_blk);
        let ok_id = self.block_id_of(ok_blk);
        let error_id = self.block_id_of(error_blk);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: non_negative,
                then_target: check_capacity_id,
                then_args: vec![len_value],
                else_target: error_id,
                else_args: vec![],
            }),
        );

        let capacity_val = self.emit_i64_const(check_capacity_blk, i64::from(capacity));
        let within_capacity = self.emit_with_result(
            check_capacity_blk,
            Inst::ICmp {
                op: ICmpOp::Sle,
                ty: Ty::I64,
                lhs: check_len_value,
                rhs: capacity_val,
            },
        );
        self.emit(
            check_capacity_blk,
            InstrNode::new(Inst::CondBr {
                cond: within_capacity,
                then_target: ok_id,
                then_args: vec![check_len_value],
                else_target: error_id,
                else_args: vec![],
            }),
        );
        self.emit_runtime_error_and_return(error_blk, JitRuntimeErrorKind::TypeMismatch);
        CompactSequenceLenGuardResult {
            block_idx: ok_blk,
            len_value: ok_len_value,
        }
        .into()
    }

    fn copy_flat_aggregate_to_compact_slots(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        source_shape: &AggregateShape,
        dest_shape: &AggregateShape,
        dest_ptr: ValueId,
        dst_base: u32,
        funcdef_values_are_captured_compact: bool,
    ) -> Result<CompactCopyResult, TmirError> {
        match (source_shape, dest_shape) {
            (
                AggregateShape::Record { fields: source },
                AggregateShape::Record { fields: dest },
            ) => {
                if source.len() != dest.len() {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar record slot copy field-count mismatch: {} vs {}",
                        source.len(),
                        dest.len()
                    )));
                }
                let mut slots_written = 0_u32;
                let mut current_block = block_idx;
                for (dest_name, dest_shape) in dest {
                    let Some((idx, (_, source_shape))) = source
                        .iter()
                        .enumerate()
                        .find(|(_, (source_name, _))| source_name == dest_name)
                    else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "StoreVar record slot copy missing source field: {dest_name:?}"
                        )));
                    };
                    let (Some(source_shape), Some(dest_shape)) =
                        (source_shape.as_deref(), dest_shape.as_deref())
                    else {
                        return Err(TmirError::UnsupportedOpcode(
                            "StoreVar record slot copy requires tracked field shapes".to_owned(),
                        ));
                    };
                    let field_slot = u32::try_from(idx).map_err(|_| {
                        TmirError::UnsupportedOpcode(
                            "StoreVar record field index overflows u32".to_owned(),
                        )
                    })?;
                    let field_copy = self.copy_flat_slot_value_to_compact_slots(
                        current_block,
                        source_ptr,
                        field_slot,
                        source_shape,
                        dest_shape,
                        dest_ptr,
                        dst_base + slots_written,
                    )?;
                    current_block = field_copy.block_idx;
                    slots_written = slots_written
                        .checked_add(field_copy.slots_written)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar record slot copy count overflows u32".to_owned(),
                            )
                        })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            (
                AggregateShape::RecordSet { fields: source },
                AggregateShape::RecordSet { fields: dest },
            ) => {
                if source.len() != dest.len() {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "RecordSet return copy field-count mismatch: {} vs {}",
                        source.len(),
                        dest.len()
                    )));
                }
                for (dst_offset, (dest_name, dest_shape)) in dest.iter().enumerate() {
                    let Some((source_idx, (_, source_shape))) = source
                        .iter()
                        .enumerate()
                        .find(|(_, (source_name, _))| source_name == dest_name)
                    else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "RecordSet return copy missing source field: {dest_name:?}"
                        )));
                    };
                    let source_slot = u32::try_from(source_idx).map_err(|_| {
                        TmirError::UnsupportedOpcode(
                            "RecordSet source field index overflows u32".to_owned(),
                        )
                    })?;
                    let dest_slot = dst_base
                        .checked_add(u32::try_from(dst_offset).map_err(|_| {
                            TmirError::UnsupportedOpcode(
                                "RecordSet destination field index overflows u32".to_owned(),
                            )
                        })?)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "RecordSet destination slot overflows u32".to_owned(),
                            )
                        })?;
                    self.copy_record_set_return_domain_slot(
                        block_idx,
                        source_ptr,
                        source_slot,
                        source_shape,
                        dest_shape,
                        dest_ptr,
                        dest_slot,
                        "RecordSet return copy",
                    )?;
                }
                Ok(CompactCopyResult {
                    slots_written: u32::try_from(dest.len()).map_err(|_| {
                        TmirError::UnsupportedOpcode(
                            "RecordSet field count overflows u32".to_owned(),
                        )
                    })?,
                    block_idx,
                })
            }
            (
                AggregateShape::Sequence {
                    extent: source_extent,
                    element: source_element,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) => {
                let source_capacity = source_extent.capacity();
                let dest_capacity = dest_extent.capacity();
                if source_capacity > dest_capacity {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar sequence slot copy source capacity {source_capacity} exceeds destination capacity {dest_capacity}"
                    )));
                }
                let source_exact_len = source_extent.exact_count();
                let loaded_len_value = self.load_at_offset(block_idx, source_ptr, 0);
                let (mut current_block, len_value) = if source_exact_len.is_some() {
                    (block_idx, loaded_len_value)
                } else {
                    let guarded_len: CompactSequenceLenGuardResult = self
                        .guard_compact_sequence_len_in_bounds(
                            block_idx,
                            loaded_len_value,
                            source_capacity,
                            "compact_flat_sequence_copy_len",
                        );
                    (guarded_len.block_idx, guarded_len.len_value)
                };
                self.store_at_offset(current_block, dest_ptr, dst_base, len_value);
                if dest_capacity == 0 {
                    return Ok(CompactCopyResult {
                        slots_written: 1,
                        block_idx: current_block,
                    });
                }
                let Some(dest_element) = dest_element.as_deref() else {
                    return Err(TmirError::UnsupportedOpcode(
                        "StoreVar sequence slot copy requires tracked destination element shape"
                            .to_owned(),
                    ));
                };
                let element_stride = dest_element.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "StoreVar sequence slot copy requires fixed-width element shape, got {dest_element:?}"
                    ))
                })?;
                let source_element = if source_capacity == 0 {
                    None
                } else {
                    Some(source_element.as_deref().ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "StoreVar sequence slot copy requires tracked source element shape"
                                .to_owned(),
                        )
                    })?)
                };
                if let Some(source_element) = source_element {
                    if !Self::compatible_compact_materialization_value(source_element, dest_element)
                    {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "StoreVar sequence slot copy requires compatible element shapes, got {source_element:?} -> {dest_element:?}"
                        )));
                    }
                }
                let mut slots_written = 1_u32;
                for idx in 0..dest_capacity {
                    let element_dst_slot = dst_base
                        .checked_add(1)
                        .and_then(|slot| slot.checked_add(idx.checked_mul(element_stride)?))
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar sequence destination slot overflows u32".to_owned(),
                            )
                        })?;
                    if source_exact_len.is_some_and(|len| idx >= len) {
                        let zero = self.emit_i64_const(current_block, 0);
                        self.zero_compact_slots(
                            current_block,
                            dest_ptr,
                            element_dst_slot,
                            element_stride,
                            zero,
                        )?;
                    } else if idx < source_capacity {
                        let source_slot = idx.checked_add(1).ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar sequence source slot overflows u32".to_owned(),
                            )
                        })?;
                        let source_element = source_element.ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar sequence slot copy requires tracked source element shape"
                                    .to_owned(),
                            )
                        })?;
                        if source_exact_len.is_some() {
                            let copied = self.copy_flat_slot_value_to_compact_slots(
                                current_block,
                                source_ptr,
                                source_slot,
                                source_element,
                                dest_element,
                                dest_ptr,
                                element_dst_slot,
                            )?;
                            if copied.slots_written != element_stride {
                                return Err(TmirError::UnsupportedOpcode(format!(
                                    "StoreVar sequence slot copy wrote {} slots for {element_stride}-slot element",
                                    copied.slots_written
                                )));
                            }
                            current_block = copied.block_idx;
                        } else {
                            let idx_value = self.emit_i64_const(current_block, i64::from(idx));
                            let is_active = self.emit_with_result(
                                current_block,
                                Inst::ICmp {
                                    op: ICmpOp::Slt,
                                    ty: Ty::I64,
                                    lhs: idx_value,
                                    rhs: len_value,
                                },
                            );
                            let active_blk =
                                self.new_aux_block("compact_flat_sequence_copy_active");
                            let inactive_blk =
                                self.new_aux_block("compact_flat_sequence_copy_inactive");
                            let merge_blk = self.new_aux_block("compact_flat_sequence_copy_merge");
                            let active_id = self.block_id_of(active_blk);
                            let inactive_id = self.block_id_of(inactive_blk);
                            let merge_id = self.block_id_of(merge_blk);
                            self.emit(
                                current_block,
                                InstrNode::new(Inst::CondBr {
                                    cond: is_active,
                                    then_target: active_id,
                                    then_args: vec![],
                                    else_target: inactive_id,
                                    else_args: vec![],
                                }),
                            );
                            let copied = self.copy_flat_slot_value_to_compact_slots(
                                active_blk,
                                source_ptr,
                                source_slot,
                                source_element,
                                dest_element,
                                dest_ptr,
                                element_dst_slot,
                            )?;
                            if copied.slots_written != element_stride {
                                return Err(TmirError::UnsupportedOpcode(format!(
                                    "StoreVar sequence slot copy wrote {} slots for {element_stride}-slot element",
                                    copied.slots_written
                                )));
                            }
                            self.emit(
                                copied.block_idx,
                                InstrNode::new(Inst::Br {
                                    target: merge_id,
                                    args: vec![],
                                }),
                            );
                            let zero = self.emit_i64_const(inactive_blk, 0);
                            self.zero_compact_slots(
                                inactive_blk,
                                dest_ptr,
                                element_dst_slot,
                                element_stride,
                                zero,
                            )?;
                            self.emit(
                                inactive_blk,
                                InstrNode::new(Inst::Br {
                                    target: merge_id,
                                    args: vec![],
                                }),
                            );
                            current_block = merge_blk;
                        }
                    } else {
                        let zero = self.emit_i64_const(current_block, 0);
                        self.zero_compact_slots(
                            current_block,
                            dest_ptr,
                            element_dst_slot,
                            element_stride,
                            zero,
                        )?;
                    }
                    slots_written = slots_written.checked_add(element_stride).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "StoreVar sequence slot copy count overflows u32".to_owned(),
                        )
                    })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: source_domain_lo,
                    value: source_value,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) if *source_domain_lo == Some(1) => {
                let dest_capacity = dest_extent.capacity();
                if *source_len != dest_capacity {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar dense function-to-sequence slot copy length mismatch: {source_len} vs {dest_capacity}"
                    )));
                }
                let len_value = self.emit_i64_const(block_idx, i64::from(dest_capacity));
                self.store_at_offset(block_idx, dest_ptr, dst_base, len_value);
                if dest_capacity == 0 {
                    return Ok(CompactCopyResult {
                        slots_written: 1,
                        block_idx,
                    });
                }
                let Some(dest_element) = dest_element.as_deref() else {
                    return Err(TmirError::UnsupportedOpcode(
                        "StoreVar dense function-to-sequence copy requires tracked destination element shape"
                            .to_owned(),
                    ));
                };
                let source_value = source_value.as_deref().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "StoreVar dense function-to-sequence copy requires tracked source value shape"
                            .to_owned(),
                    )
                })?;
                if !Self::compatible_compact_materialization_value(source_value, dest_element) {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar dense function-to-sequence copy requires compatible value shapes, got {source_value:?} -> {dest_element:?}"
                    )));
                }
                let dest_stride = dest_element.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "StoreVar dense function-to-sequence copy requires fixed-width destination element shape, got {dest_element:?}"
                    ))
                })?;
                let mut slots_written = 1_u32;
                let mut current_block = block_idx;
                for idx in 0..dest_capacity {
                    let source_slot = idx
                        .checked_mul(2)
                        .and_then(|slot| slot.checked_add(2))
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar dense function source value slot overflows u32"
                                    .to_owned(),
                            )
                        })?;
                    let dest_slot = dst_base
                        .checked_add(1)
                        .and_then(|slot| slot.checked_add(idx.checked_mul(dest_stride)?))
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar dense function-to-sequence destination slot overflows u32"
                                    .to_owned(),
                            )
                        })?;
                    let copied = if funcdef_values_are_captured_compact {
                        self.copy_captured_compact_slot_value_to_compact_slots(
                            current_block,
                            source_ptr,
                            source_slot,
                            source_value,
                            dest_element,
                            dest_ptr,
                            dest_slot,
                        )?
                    } else {
                        self.copy_flat_slot_value_to_compact_slots(
                            current_block,
                            source_ptr,
                            source_slot,
                            source_value,
                            dest_element,
                            dest_ptr,
                            dest_slot,
                        )?
                    };
                    if copied.slots_written != dest_stride {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "StoreVar dense function-to-sequence copy wrote {} slots for {dest_stride}-slot element",
                            copied.slots_written
                        )));
                    }
                    current_block = copied.block_idx;
                    slots_written = slots_written.checked_add(dest_stride).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "StoreVar dense function-to-sequence slot count overflows u32"
                                .to_owned(),
                        )
                    })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: source_domain_lo,
                    value: source_value,
                },
                AggregateShape::Function {
                    len: dest_len,
                    domain_lo: dest_domain_lo,
                    value: dest_value,
                },
            ) => {
                if source_len != dest_len {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar function slot copy length mismatch: {source_len} vs {dest_len}"
                    )));
                }
                if source_domain_lo != dest_domain_lo {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar function slot copy domain mismatch: {source_domain_lo:?} vs {dest_domain_lo:?}"
                    )));
                }
                if *source_len == 0 {
                    return Ok(CompactCopyResult {
                        slots_written: 0,
                        block_idx,
                    });
                }
                let (Some(source_value), Some(dest_value)) =
                    (source_value.as_deref(), dest_value.as_deref())
                else {
                    return Err(TmirError::UnsupportedOpcode(
                        "StoreVar function slot copy requires tracked value shapes".to_owned(),
                    ));
                };
                let value_stride = dest_value.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "StoreVar function slot copy requires fixed-width value shape, got {dest_value:?}"
                    ))
                })?;
                let mut slots_written = 0_u32;
                let mut current_block = block_idx;
                for idx in 0..*source_len {
                    let source_slot = idx
                        .checked_mul(2)
                        .and_then(|slot| slot.checked_add(2))
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar function source value slot overflows u32".to_owned(),
                            )
                        })?;
                    let value_dst_slot = dst_base
                        .checked_add(idx.checked_mul(value_stride).ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar function destination slot overflows u32".to_owned(),
                            )
                        })?)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "StoreVar function destination slot overflows u32".to_owned(),
                            )
                        })?;
                    let copied = if funcdef_values_are_captured_compact {
                        self.copy_captured_compact_slot_value_to_compact_slots(
                            current_block,
                            source_ptr,
                            source_slot,
                            source_value,
                            dest_value,
                            dest_ptr,
                            value_dst_slot,
                        )?
                    } else {
                        self.copy_flat_slot_value_to_compact_slots(
                            current_block,
                            source_ptr,
                            source_slot,
                            source_value,
                            dest_value,
                            dest_ptr,
                            value_dst_slot,
                        )?
                    };
                    current_block = copied.block_idx;
                    if copied.slots_written != value_stride {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "StoreVar function slot copy wrote {} slots for {value_stride}-slot value",
                            copied.slots_written
                        )));
                    }
                    slots_written =
                        slots_written
                            .checked_add(copied.slots_written)
                            .ok_or_else(|| {
                                TmirError::UnsupportedOpcode(
                                    "StoreVar function slot copy count overflows u32".to_owned(),
                                )
                            })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            _ if Self::is_single_slot_flat_aggregate_value(source_shape)
                && Self::is_single_slot_flat_aggregate_value(dest_shape)
                && Self::compatible_flat_aggregate_value(source_shape, dest_shape) =>
            {
                let value = self.load_at_offset(block_idx, source_ptr, 0);
                self.store_at_offset(block_idx, dest_ptr, dst_base, value);
                Ok(CompactCopyResult {
                    slots_written: 1,
                    block_idx,
                })
            }
            _ => Err(TmirError::UnsupportedOpcode(format!(
                "compact flat aggregate slot copy requires compatible fixed-width source/destination shapes, got {source_shape:?} -> {dest_shape:?}"
            ))),
        }
    }

    fn can_copy_compact_aggregate_to_compact_slots(
        source: &AggregateShape,
        dest: &AggregateShape,
    ) -> bool {
        match (source, dest) {
            (AggregateShape::Record { .. }, AggregateShape::Record { .. })
            | (AggregateShape::Sequence { .. }, AggregateShape::Sequence { .. })
            | (AggregateShape::Function { .. }, AggregateShape::Sequence { .. })
            | (AggregateShape::Function { .. }, AggregateShape::Function { .. })
            | (AggregateShape::RecordSet { .. }, AggregateShape::RecordSet { .. }) => {
                source.compact_slot_count().is_some()
                    && dest.compact_slot_count().is_some()
                    && Self::compatible_compact_materialization_value(source, dest)
            }
            _ => false,
        }
    }

    fn copy_compact_slot_value_to_compact_slots(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        source_slot: u32,
        source_shape: &AggregateShape,
        dest_shape: &AggregateShape,
        dest_ptr: ValueId,
        dst_slot: u32,
    ) -> Result<CompactCopyResult, TmirError> {
        if Self::is_single_slot_flat_aggregate_value(source_shape)
            && Self::is_single_slot_flat_aggregate_value(dest_shape)
            && Self::compatible_flat_aggregate_value(source_shape, dest_shape)
        {
            let value = self.load_at_offset(block_idx, source_ptr, source_slot);
            self.store_at_offset(block_idx, dest_ptr, dst_slot, value);
            return Ok(CompactCopyResult {
                slots_written: 1,
                block_idx,
            });
        }

        if Self::is_compact_compound_aggregate(source_shape)
            && Self::is_compact_compound_aggregate(dest_shape)
            && Self::compatible_compact_materialization_value(source_shape, dest_shape)
        {
            return self.copy_compact_aggregate_to_compact_slots(
                block_idx,
                source_ptr,
                source_slot,
                source_shape,
                dest_shape,
                dest_ptr,
                dst_slot,
            );
        }

        Err(TmirError::UnsupportedOpcode(format!(
            "compact aggregate slot copy requires compatible fixed-width source/destination shapes, got {source_shape:?} -> {dest_shape:?}"
        )))
    }

    fn copy_compact_aggregate_to_compact_slots(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        source_base: u32,
        source_shape: &AggregateShape,
        dest_shape: &AggregateShape,
        dest_ptr: ValueId,
        dst_base: u32,
    ) -> Result<CompactCopyResult, TmirError> {
        match (source_shape, dest_shape) {
            (
                AggregateShape::Record { fields: source },
                AggregateShape::Record { fields: dest },
            ) => {
                if source.len() != dest.len() {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact record slot copy field-count mismatch: {} vs {}",
                        source.len(),
                        dest.len()
                    )));
                }
                let mut slots_written = 0_u32;
                let mut current_block = block_idx;
                for (dest_name, dest_shape) in dest {
                    let Some((source_offset, source_shape)) =
                        source_shape.compact_record_field(*dest_name)
                    else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "compact record slot copy missing source field: {dest_name:?}"
                        )));
                    };
                    let Some(source_shape) = source_shape.as_ref() else {
                        return Err(TmirError::UnsupportedOpcode(
                            "compact record slot copy requires tracked source field shape"
                                .to_owned(),
                        ));
                    };
                    let Some(dest_shape) = dest_shape.as_deref() else {
                        return Err(TmirError::UnsupportedOpcode(
                            "compact record slot copy requires tracked destination field shape"
                                .to_owned(),
                        ));
                    };
                    let source_slot = source_base.checked_add(source_offset).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "compact record source slot overflows u32".to_owned(),
                        )
                    })?;
                    let dest_slot = dst_base.checked_add(slots_written).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "compact record destination slot overflows u32".to_owned(),
                        )
                    })?;
                    let field_copy = self.copy_compact_slot_value_to_compact_slots(
                        current_block,
                        source_ptr,
                        source_slot,
                        source_shape,
                        dest_shape,
                        dest_ptr,
                        dest_slot,
                    )?;
                    current_block = field_copy.block_idx;
                    slots_written = slots_written
                        .checked_add(field_copy.slots_written)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact record slot copy count overflows u32".to_owned(),
                            )
                        })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            (
                AggregateShape::RecordSet { fields: source },
                AggregateShape::RecordSet { fields: dest },
            ) => {
                if source.len() != dest.len() {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact RecordSet return copy field-count mismatch: {} vs {}",
                        source.len(),
                        dest.len()
                    )));
                }
                for (dst_offset, (dest_name, dest_shape)) in dest.iter().enumerate() {
                    let Some((source_idx, (_, source_shape))) = source
                        .iter()
                        .enumerate()
                        .find(|(_, (source_name, _))| source_name == dest_name)
                    else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "compact RecordSet return copy missing source field: {dest_name:?}"
                        )));
                    };
                    let source_slot = source_base
                        .checked_add(u32::try_from(source_idx).map_err(|_| {
                            TmirError::UnsupportedOpcode(
                                "compact RecordSet source field index overflows u32".to_owned(),
                            )
                        })?)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact RecordSet source slot overflows u32".to_owned(),
                            )
                        })?;
                    let dest_slot = dst_base
                        .checked_add(u32::try_from(dst_offset).map_err(|_| {
                            TmirError::UnsupportedOpcode(
                                "compact RecordSet destination field index overflows u32"
                                    .to_owned(),
                            )
                        })?)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact RecordSet destination slot overflows u32".to_owned(),
                            )
                        })?;
                    self.copy_record_set_return_domain_slot(
                        block_idx,
                        source_ptr,
                        source_slot,
                        source_shape,
                        dest_shape,
                        dest_ptr,
                        dest_slot,
                        "compact RecordSet return copy",
                    )?;
                }
                Ok(CompactCopyResult {
                    slots_written: u32::try_from(dest.len()).map_err(|_| {
                        TmirError::UnsupportedOpcode(
                            "compact RecordSet field count overflows u32".to_owned(),
                        )
                    })?,
                    block_idx,
                })
            }
            (
                AggregateShape::Sequence {
                    extent: source_extent,
                    element: source_element,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) => {
                let source_capacity = source_extent.capacity();
                let dest_capacity = dest_extent.capacity();
                if source_capacity > dest_capacity {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact sequence slot copy source capacity {source_capacity} exceeds destination capacity {dest_capacity}"
                    )));
                }
                let source_exact_len = source_extent.exact_count();
                let loaded_len_value = self.load_at_offset(block_idx, source_ptr, source_base);
                let (mut current_block, len_value) = if source_exact_len.is_some() {
                    (block_idx, loaded_len_value)
                } else {
                    let guarded_len: CompactSequenceLenGuardResult = self
                        .guard_compact_sequence_len_in_bounds(
                            block_idx,
                            loaded_len_value,
                            source_capacity,
                            "compact_sequence_copy_len",
                        );
                    (guarded_len.block_idx, guarded_len.len_value)
                };
                self.store_at_offset(current_block, dest_ptr, dst_base, len_value);
                if dest_capacity == 0 {
                    return Ok(CompactCopyResult {
                        slots_written: 1,
                        block_idx: current_block,
                    });
                }
                let Some(dest_element) = dest_element.as_deref() else {
                    return Err(TmirError::UnsupportedOpcode(
                        "compact sequence slot copy requires tracked destination element shape"
                            .to_owned(),
                    ));
                };
                let dest_stride = dest_element.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "compact sequence slot copy requires fixed-width destination element shape, got {dest_element:?}"
                    ))
                })?;
                let source_element = if source_capacity == 0 {
                    None
                } else {
                    Some(source_element.as_deref().ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "compact sequence slot copy requires tracked source element shape"
                                .to_owned(),
                        )
                    })?)
                };
                let source_stride = if let Some(source_element) = source_element {
                    if !Self::compatible_compact_materialization_value(source_element, dest_element)
                    {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "compact sequence slot copy requires compatible element shapes, got {source_element:?} -> {dest_element:?}"
                        )));
                    }
                    Some(source_element.compact_slot_count().ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "compact sequence slot copy requires fixed-width source element shape, got {source_element:?}"
                        ))
                    })?)
                } else {
                    None
                };
                let mut slots_written = 1_u32;
                for idx in 0..dest_capacity {
                    let dest_slot = dst_base
                        .checked_add(1)
                        .and_then(|slot| slot.checked_add(idx.checked_mul(dest_stride)?))
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact sequence destination slot overflows u32".to_owned(),
                            )
                        })?;
                    if source_exact_len.is_some_and(|len| idx >= len) {
                        let zero = self.emit_i64_const(current_block, 0);
                        self.zero_compact_slots(
                            current_block,
                            dest_ptr,
                            dest_slot,
                            dest_stride,
                            zero,
                        )?;
                    } else if idx < source_capacity {
                        let source_element = source_element.ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact sequence slot copy requires tracked source element shape"
                                    .to_owned(),
                            )
                        })?;
                        let source_stride = source_stride.ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact sequence slot copy requires tracked source element stride"
                                    .to_owned(),
                            )
                        })?;
                        let source_slot = source_base
                            .checked_add(1)
                            .and_then(|slot| slot.checked_add(idx.checked_mul(source_stride)?))
                            .ok_or_else(|| {
                                TmirError::UnsupportedOpcode(
                                    "compact sequence source slot overflows u32".to_owned(),
                                )
                            })?;
                        if source_exact_len.is_some() {
                            let copied = self.copy_compact_slot_value_to_compact_slots(
                                current_block,
                                source_ptr,
                                source_slot,
                                source_element,
                                dest_element,
                                dest_ptr,
                                dest_slot,
                            )?;
                            if copied.slots_written != dest_stride {
                                return Err(TmirError::UnsupportedOpcode(format!(
                                    "compact sequence slot copy wrote {} slots for {dest_stride}-slot element",
                                    copied.slots_written
                                )));
                            }
                            current_block = copied.block_idx;
                        } else {
                            let idx_value = self.emit_i64_const(current_block, i64::from(idx));
                            let is_active = self.emit_with_result(
                                current_block,
                                Inst::ICmp {
                                    op: ICmpOp::Slt,
                                    ty: Ty::I64,
                                    lhs: idx_value,
                                    rhs: len_value,
                                },
                            );
                            let active_blk = self.new_aux_block("compact_sequence_copy_active");
                            let inactive_blk =
                                self.new_aux_block("compact_sequence_copy_inactive");
                            let merge_blk = self.new_aux_block("compact_sequence_copy_merge");
                            let active_id = self.block_id_of(active_blk);
                            let inactive_id = self.block_id_of(inactive_blk);
                            let merge_id = self.block_id_of(merge_blk);
                            self.emit(
                                current_block,
                                InstrNode::new(Inst::CondBr {
                                    cond: is_active,
                                    then_target: active_id,
                                    then_args: vec![],
                                    else_target: inactive_id,
                                    else_args: vec![],
                                }),
                            );
                            let copied = self.copy_compact_slot_value_to_compact_slots(
                                active_blk,
                                source_ptr,
                                source_slot,
                                source_element,
                                dest_element,
                                dest_ptr,
                                dest_slot,
                            )?;
                            if copied.slots_written != dest_stride {
                                return Err(TmirError::UnsupportedOpcode(format!(
                                    "compact sequence slot copy wrote {} slots for {dest_stride}-slot element",
                                    copied.slots_written
                                )));
                            }
                            self.emit(
                                copied.block_idx,
                                InstrNode::new(Inst::Br {
                                    target: merge_id,
                                    args: vec![],
                                }),
                            );
                            let zero = self.emit_i64_const(inactive_blk, 0);
                            self.zero_compact_slots(
                                inactive_blk,
                                dest_ptr,
                                dest_slot,
                                dest_stride,
                                zero,
                            )?;
                            self.emit(
                                inactive_blk,
                                InstrNode::new(Inst::Br {
                                    target: merge_id,
                                    args: vec![],
                                }),
                            );
                            current_block = merge_blk;
                        }
                    } else {
                        let zero = self.emit_i64_const(current_block, 0);
                        self.zero_compact_slots(
                            current_block,
                            dest_ptr,
                            dest_slot,
                            dest_stride,
                            zero,
                        )?;
                    }
                    slots_written = slots_written.checked_add(dest_stride).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "compact sequence slot copy count overflows u32".to_owned(),
                        )
                    })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: source_domain_lo,
                    value: source_value,
                },
                AggregateShape::Sequence {
                    extent: dest_extent,
                    element: dest_element,
                },
            ) if *source_domain_lo == Some(1) => {
                let dest_capacity = dest_extent.capacity();
                if *source_len != dest_capacity {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact dense function-to-sequence slot copy length mismatch: {source_len} vs {dest_capacity}"
                    )));
                }
                let len_value = self.emit_i64_const(block_idx, i64::from(dest_capacity));
                self.store_at_offset(block_idx, dest_ptr, dst_base, len_value);
                if dest_capacity == 0 {
                    return Ok(CompactCopyResult {
                        slots_written: 1,
                        block_idx,
                    });
                }
                let Some(dest_element) = dest_element.as_deref() else {
                    return Err(TmirError::UnsupportedOpcode(
                        "compact dense function-to-sequence copy requires tracked destination element shape"
                            .to_owned(),
                    ));
                };
                let source_value = source_value.as_deref().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "compact dense function-to-sequence copy requires tracked source value shape"
                            .to_owned(),
                    )
                })?;
                if !Self::compatible_compact_materialization_value(source_value, dest_element) {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact dense function-to-sequence copy requires compatible value shapes, got {source_value:?} -> {dest_element:?}"
                    )));
                }
                let source_stride = source_value.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "compact dense function-to-sequence copy requires fixed-width source value shape, got {source_value:?}"
                    ))
                })?;
                let dest_stride = dest_element.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "compact dense function-to-sequence copy requires fixed-width destination element shape, got {dest_element:?}"
                    ))
                })?;
                let mut slots_written = 1_u32;
                let mut current_block = block_idx;
                for idx in 0..dest_capacity {
                    let source_slot = source_base
                        .checked_add(idx.checked_mul(source_stride).ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact dense function source value slot overflows u32".to_owned(),
                            )
                        })?)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact dense function source value slot overflows u32".to_owned(),
                            )
                        })?;
                    let dest_slot = dst_base
                        .checked_add(1)
                        .and_then(|slot| slot.checked_add(idx.checked_mul(dest_stride)?))
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact dense function-to-sequence destination slot overflows u32"
                                    .to_owned(),
                            )
                        })?;
                    let copied = self.copy_compact_slot_value_to_compact_slots(
                        current_block,
                        source_ptr,
                        source_slot,
                        source_value,
                        dest_element,
                        dest_ptr,
                        dest_slot,
                    )?;
                    if copied.slots_written != dest_stride {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "compact dense function-to-sequence copy wrote {} slots for {dest_stride}-slot element",
                            copied.slots_written
                        )));
                    }
                    current_block = copied.block_idx;
                    slots_written = slots_written.checked_add(dest_stride).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "compact dense function-to-sequence slot count overflows u32"
                                .to_owned(),
                        )
                    })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            (
                AggregateShape::Function {
                    len: source_len,
                    domain_lo: source_domain_lo,
                    value: source_value,
                },
                AggregateShape::Function {
                    len: dest_len,
                    domain_lo: dest_domain_lo,
                    value: dest_value,
                },
            ) => {
                if source_len != dest_len || source_domain_lo != dest_domain_lo {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact function slot copy shape mismatch: len {source_len} vs {dest_len}, domain {source_domain_lo:?} vs {dest_domain_lo:?}"
                    )));
                }
                if *source_len == 0 {
                    return Ok(CompactCopyResult {
                        slots_written: 0,
                        block_idx,
                    });
                }
                let (Some(source_value), Some(dest_value)) =
                    (source_value.as_deref(), dest_value.as_deref())
                else {
                    return Err(TmirError::UnsupportedOpcode(
                        "compact function slot copy requires tracked value shapes".to_owned(),
                    ));
                };
                let source_stride = source_value.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "compact function slot copy requires fixed-width source value shape, got {source_value:?}"
                    ))
                })?;
                let dest_stride = dest_value.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "compact function slot copy requires fixed-width destination value shape, got {dest_value:?}"
                    ))
                })?;
                let mut slots_written = 0_u32;
                let mut current_block = block_idx;
                for idx in 0..*source_len {
                    let source_slot = source_base
                        .checked_add(idx.checked_mul(source_stride).ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact function source slot overflows u32".to_owned(),
                            )
                        })?)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact function source slot overflows u32".to_owned(),
                            )
                        })?;
                    let dest_slot = dst_base
                        .checked_add(idx.checked_mul(dest_stride).ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact function destination slot overflows u32".to_owned(),
                            )
                        })?)
                        .ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "compact function destination slot overflows u32".to_owned(),
                            )
                        })?;
                    let copied = self.copy_compact_slot_value_to_compact_slots(
                        current_block,
                        source_ptr,
                        source_slot,
                        source_value,
                        dest_value,
                        dest_ptr,
                        dest_slot,
                    )?;
                    current_block = copied.block_idx;
                    if copied.slots_written != dest_stride {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "compact function slot copy wrote {} slots for {dest_stride}-slot value",
                            copied.slots_written
                        )));
                    }
                    slots_written =
                        slots_written
                            .checked_add(copied.slots_written)
                            .ok_or_else(|| {
                                TmirError::UnsupportedOpcode(
                                    "compact function slot copy count overflows u32".to_owned(),
                                )
                            })?;
                }
                Ok(CompactCopyResult {
                    slots_written,
                    block_idx: current_block,
                })
            }
            _ if Self::is_single_slot_flat_aggregate_value(source_shape)
                && Self::is_single_slot_flat_aggregate_value(dest_shape)
                && Self::compatible_flat_aggregate_value(source_shape, dest_shape) =>
            {
                let value = self.load_at_offset(block_idx, source_ptr, source_base);
                self.store_at_offset(block_idx, dest_ptr, dst_base, value);
                Ok(CompactCopyResult {
                    slots_written: 1,
                    block_idx,
                })
            }
            _ => Err(TmirError::UnsupportedOpcode(format!(
                "compact aggregate slot copy requires compatible fixed-width source/destination shapes, got {source_shape:?} -> {dest_shape:?}"
            ))),
        }
    }

    pub(super) fn load_reg_as_compatible_single_slot_value(
        &mut self,
        block_idx: usize,
        reg: u8,
        expected_shape: &AggregateShape,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        if !Self::is_single_slot_flat_aggregate_value(expected_shape) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: expected single-slot compact value shape for r{reg}, got {expected_shape:?}"
            )));
        }
        if let Some(source_shape) = self.aggregate_shapes.get(&reg) {
            if !Self::is_single_slot_flat_aggregate_value(source_shape)
                || !Self::compatible_flat_aggregate_value(source_shape, expected_shape)
            {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: source r{reg} is incompatible with scalar expected shape: source_shape={source_shape:?}, expected_shape={expected_shape:?}"
                )));
            }
        } else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: source r{reg} requires a tracked scalar shape for expected shape {expected_shape:?}"
            )));
        }
        self.load_reg(block_idx, reg)
    }

    pub(super) fn materialize_reg_as_compact_source(
        &mut self,
        block_idx: usize,
        reg: u8,
        expected_shape: &AggregateShape,
    ) -> Result<CompactMaterializationResult, TmirError> {
        let expected_slots = expected_shape.compact_slot_count().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "compact materialization requires fixed-width destination shape for r{reg}, got {expected_shape:?}"
            ))
        })?;

        if self.flat_funcdef_pair_list_regs.contains(&reg) {
            let raw_source_shape = self.aggregate_shapes.get(&reg).cloned().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "compact materialization requires a tracked flat FuncDef source shape for r{reg}, expected {expected_shape:?}"
                ))
            })?;
            let source_shape = Self::complete_inferred_compact_shape_from_expected(
                &raw_source_shape,
                expected_shape,
            )
            .unwrap_or(raw_source_shape);
            if !Self::can_copy_flat_aggregate_to_compact_slots(&source_shape, expected_shape) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "compact materialization requires compatible flat FuncDef source and compact destination shapes for r{reg}, got {source_shape:?} -> {expected_shape:?}"
                )));
            }

            let source_ptr = self.load_reg_as_ptr(block_idx, reg)?;
            let result_ptr = self.alloc_aggregate(block_idx, expected_slots);
            let copied = self.copy_flat_aggregate_to_compact_slots(
                block_idx,
                source_ptr,
                &source_shape,
                expected_shape,
                result_ptr,
                0,
                true,
            )?;
            if copied.slots_written != expected_slots {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "compact materialization copied {} flat FuncDef slots for r{reg}, expected {expected_slots}",
                    copied.slots_written
                )));
            }
            return Ok(CompactMaterializationResult {
                slot: CompactStateSlot::raw(result_ptr, 0),
                block_idx: copied.block_idx,
            });
        }

        if let Some(source_slot) = self.compact_state_slots.get(&reg).copied() {
            let source_slot = if source_slot.requires_pointer_reload_in_block(block_idx) {
                let reloaded_ptr = self.load_reg_as_ptr(block_idx, reg)?;
                CompactStateSlot::pointer_backed_in_block(
                    reloaded_ptr,
                    source_slot.offset,
                    block_idx,
                )
            } else {
                source_slot
            };
            let raw_source_shape = self.aggregate_shapes.get(&reg).cloned().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "compact materialization source r{reg} has stale compact provenance without a tracked shape"
                ))
            })?;
            let source_shape = Self::complete_inferred_compact_shape_from_expected(
                &raw_source_shape,
                expected_shape,
            )
            .unwrap_or(raw_source_shape);
            let source_slots = source_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "compact materialization source r{reg} has non-fixed shape {source_shape:?}"
                ))
            })?;
            if source_slots == expected_slots
                && Self::same_compact_physical_layout(&source_shape, expected_shape)
                && !Self::contains_compact_sequence(&source_shape)
            {
                return Ok(CompactMaterializationResult {
                    slot: source_slot,
                    block_idx,
                });
            }
            if Self::can_copy_compact_aggregate_to_compact_slots(&source_shape, expected_shape) {
                let result_ptr = self.alloc_aggregate(block_idx, expected_slots);
                let copied = self.copy_compact_aggregate_to_compact_slots(
                    block_idx,
                    source_slot.source_ptr,
                    source_slot.offset,
                    &source_shape,
                    expected_shape,
                    result_ptr,
                    0,
                )?;
                if copied.slots_written != expected_slots {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact materialization copied {} compact slots for r{reg}, expected {expected_slots}",
                        copied.slots_written
                    )));
                }
                return Ok(CompactMaterializationResult {
                    slot: CompactStateSlot::raw(result_ptr, 0),
                    block_idx: copied.block_idx,
                });
            }
            return Err(TmirError::UnsupportedOpcode(format!(
                "compact materialization source r{reg} is incompatible with expected shape: source_shape={source_shape:?}, expected_shape={expected_shape:?}, source_slots={source_slots}, expected_slots={expected_slots}"
            )));
        }

        if Self::is_single_slot_flat_aggregate_value(expected_shape) {
            if let Some(source_shape) = self.aggregate_shapes.get(&reg) {
                if let Some(mask) = Self::static_set_bitmask_materialization_mask(
                    source_shape,
                    expected_shape,
                    "compact materialization",
                )? {
                    let value = self.emit_i64_const(block_idx, mask);
                    let result_ptr = self.alloc_aggregate(block_idx, 1);
                    self.store_at_offset(block_idx, result_ptr, 0, value);
                    return Ok(CompactMaterializationResult {
                        slot: CompactStateSlot::raw(result_ptr, 0),
                        block_idx,
                    });
                }
            }
            let value = self.load_reg_as_compatible_single_slot_value(
                block_idx,
                reg,
                expected_shape,
                "compact materialization",
            )?;
            let result_ptr = self.alloc_aggregate(block_idx, 1);
            self.store_at_offset(block_idx, result_ptr, 0, value);
            return Ok(CompactMaterializationResult {
                slot: CompactStateSlot::raw(result_ptr, 0),
                block_idx,
            });
        }

        let raw_source_shape = self.aggregate_shapes.get(&reg).cloned().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "compact materialization requires a tracked source shape for r{reg}, expected {expected_shape:?}"
            ))
        })?;
        let source_shape =
            Self::complete_inferred_compact_shape_from_expected(&raw_source_shape, expected_shape)
                .unwrap_or(raw_source_shape);
        if !Self::can_copy_flat_aggregate_to_compact_slots(&source_shape, expected_shape) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "compact materialization requires compatible flat source and compact destination shapes for r{reg}, got {source_shape:?} -> {expected_shape:?}"
            )));
        }

        let source_ptr = self.load_reg_as_ptr(block_idx, reg)?;
        let result_ptr = self.alloc_aggregate(block_idx, expected_slots);
        let copied = self.copy_flat_aggregate_to_compact_slots(
            block_idx,
            source_ptr,
            &source_shape,
            expected_shape,
            result_ptr,
            0,
            false,
        )?;
        if copied.slots_written != expected_slots {
            return Err(TmirError::UnsupportedOpcode(format!(
                "compact materialization copied {} slots for r{reg}, expected {expected_slots}",
                copied.slots_written
            )));
        }

        Ok(CompactMaterializationResult {
            slot: CompactStateSlot::raw(result_ptr, 0),
            block_idx: copied.block_idx,
        })
    }

    /// Recover compile-time-known aggregate cardinality for a loaded state
    /// variable when the checker has inferred a stable layout for it.
    fn track_loaded_state_var(&mut self, rd: u8, var_idx: u16, source_ptr: ValueId) {
        self.const_scalar_values.remove(&rd);
        self.compact_state_slots.remove(&rd);
        self.flat_funcdef_pair_list_regs.remove(&rd);
        let shape = self
            .state_layout
            .as_ref()
            .and_then(|layout| layout.var_layout(usize::from(var_idx)))
            .and_then(|var_layout| match var_layout {
                VarLayout::ScalarInt => Some(AggregateShape::Scalar(ScalarShape::Int)),
                VarLayout::ScalarBool => Some(AggregateShape::Scalar(ScalarShape::Bool)),
                VarLayout::Compound(layout) => Self::tracked_shape_from_compound_layout(layout),
                _ => None,
            });
        if let Some(shape) = shape {
            if let Some(offset) = self.compact_state_slot_offset(var_idx) {
                self.compact_state_slots
                    .insert(rd, CompactStateSlot::raw(source_ptr, offset));
            }
            if let Some(len) = shape.tracked_len() {
                self.const_set_sizes.insert(rd, len);
            } else {
                self.const_set_sizes.remove(&rd);
            }
            self.aggregate_shapes.insert(rd, shape);
        } else {
            self.aggregate_shapes.insert(rd, AggregateShape::StateValue);
            self.const_set_sizes.remove(&rd);
        }
    }

    /// Mark that the current lowering has emitted at least one loop whose
    /// domain size is not compile-time known. Prevents emitting a
    /// `Terminates` annotation on the enclosing function.
    pub(super) fn mark_unbounded_loop(&mut self) {
        self.has_unbounded_loop = true;
    }

    /// Emit the shared quantifier prelude and return the typed
    /// [`BindingFrame`] that downstream `*_next` opcodes will consume.
    ///
    /// Every bounded TLA+ quantifier (`\A`, `\E`, `CHOOSE`, `[x \in S |-> ...]`)
    /// starts with the same CFG: load domain pointer+length, allocate and
    /// zero the iteration index, jump to a header that bounds-checks
    /// `i < |S|` and on success loads `S[i + 1]` into the body's binding
    /// register. The short-circuit / aggregate-store behaviour is
    /// quantifier-specific and lives in each `*_begin` caller.
    ///
    /// The method is named `emit_binding_frame_prelude` to reflect that
    /// the returned `BindingFrame` is the *typed* handle each caller uses
    /// to stitch in its body logic. `header_name` and `load_name` are
    /// purely diagnostic (they wind up as aux-block name hints).
    ///
    /// `pc` and `loop_end` come from the `*Begin` opcode; `block` is the
    /// block that opcode is being lowered into; `r_domain` is the register
    /// holding the domain aggregate; `r_binding` is the register that will
    /// receive each element in turn.
    ///
    /// On entry `block` is the caller's current block. On return:
    ///
    /// * `block` has an unconditional `Br` to `frame.header_block`.
    /// * `frame.header_block` ends in a `CondBr` on `i < len` whose
    ///   `else_target` is `frame.exit_block` (the post-loop block).
    /// * The load block (created internally, not exposed) branches to the
    ///   body block for the caller's PC (`pc + 1`).
    ///
    /// Callers remain responsible for:
    ///
    /// * Initializing `rd` to the quantifier's identity (TRUE for `\A`,
    ///   FALSE for `\E`, `rd` unused for CHOOSE, function pointer for
    ///   `FuncDef`).
    /// * Calling [`Ctx::annotate_loop_bound`] (and [`Ctx::mark_unbounded_loop`]
    ///   on failure) on `frame.header_block`.
    /// * Calling [`Ctx::annotate_parallel_map`] where applicable.
    /// * Recording per-iteration tracking state such as storing the key
    ///   into a FuncDef aggregate.
    /// * Storing the resulting `BindingFrame` (or equivalent
    ///   [`QuantifierLoopState`]) for the matching `*Next` opcode.
    ///
    /// Element type is fixed at `Ty::I64` today; the `BindingFrame.elem_ty`
    /// field is reserved for future typed-binding refinements.
    pub(super) fn emit_binding_frame_prelude(
        &mut self,
        pc: usize,
        block: usize,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
        header_name: &str,
        load_name: &str,
        opcode_label: &str,
    ) -> Result<binding_frame::BindingFrame, TmirError> {
        if let Some((universe_len, universe)) = self
            .aggregate_shapes
            .get(&r_domain)
            .and_then(AggregateShape::set_bitmask_universe)
        {
            return self.emit_compact_set_bitmask_binding_frame_prelude(
                pc,
                block,
                r_binding,
                r_domain,
                loop_end,
                header_name,
                load_name,
                opcode_label,
                universe_len,
                &universe,
                None,
            );
        } else if let Some(AggregateShape::SetBitmask { universe, .. }) =
            self.aggregate_shapes.get(&r_domain)
        {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{opcode_label}: compact SetBitmask domain requires exact universe metadata, got {universe:?}"
            )));
        }
        self.reject_compact_set_bitmask_powerset_iteration(r_domain, opcode_label)?;
        let binding_shape = self
            .aggregate_shapes
            .get(&r_domain)
            .and_then(binding_shape_from_domain);

        let exit_pc = self.resolve_forward_target(pc, loop_end, opcode_label)?;
        let body_pc = pc + 1;
        let exit_block = self.block_index_for_pc(exit_pc)?;
        let body_block = self.block_index_for_pc(body_pc)?;

        // Load domain pointer and length.
        let domain_ptr =
            self.load_reg_as_ptr_or_materialize_raw_compact(block, r_domain, opcode_label)?;
        let domain_len = self.load_at_offset(block, domain_ptr, 0);

        // Allocate and zero-initialize the iteration index.
        let idx_alloca = self.emit_with_result(
            block,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        let zero = self.emit_i64_const(block, 0);
        self.emit(
            block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        // Set up header / load / body / exit block ids.
        let header_block = self.new_aux_block(header_name);
        let load_block = self.new_aux_block(load_name);
        let header_id = self.block_id_of(header_block);
        let load_id = self.block_id_of(load_block);
        let body_id = self.block_id_of(body_block);
        let exit_id = self.block_id_of(exit_block);

        // Unconditional branch from the current block to the header.
        self.emit(
            block,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

        // Header: check i < len.
        let cur_idx = self.emit_with_result(
            header_block,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let in_bounds = self.emit_with_result(
            header_block,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: cur_idx,
                rhs: domain_len,
            },
        );
        self.emit(
            header_block,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: load_id,
                then_args: vec![],
                else_target: exit_id,
                else_args: vec![],
            }),
        );

        // Load block: read S[i + 1] into the binding register.
        let cur_idx2 = self.emit_with_result(
            load_block,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(load_block, 1);
        let slot_idx = self.emit_with_result(
            load_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur_idx2,
                rhs: one,
            },
        );
        let elem = self.load_at_dynamic_offset(load_block, domain_ptr, slot_idx);
        self.store_reg_value(load_block, r_binding, elem)?;
        self.invalidate_reg_tracking(r_binding);
        if let Some(binding_shape) = binding_shape {
            self.aggregate_shapes.insert(r_binding, binding_shape);
        }
        self.emit(
            load_block,
            InstrNode::new(Inst::Br {
                target: body_id,
                args: vec![],
            }),
        );

        Ok(binding_frame::BindingFrame {
            idx_alloca,
            domain_ptr,
            domain_len,
            binding_reg: r_binding,
            elem_ty: Ty::I64,
            header_block,
            exit_block,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_compact_set_bitmask_binding_frame_prelude(
        &mut self,
        pc: usize,
        block: usize,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
        header_name: &str,
        load_name: &str,
        opcode_label: &str,
        universe_len: u32,
        universe: &SetBitmaskUniverse,
        exhausted_block: Option<usize>,
    ) -> Result<binding_frame::BindingFrame, TmirError> {
        let _valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, opcode_label)?;
        let binding_shape = scalar_int_domain_shape_from_domain(&AggregateShape::SetBitmask {
            universe_len,
            universe: universe.clone(),
        });
        let exit_pc = self.resolve_forward_target(pc, loop_end, opcode_label)?;
        let body_pc = pc + 1;
        let exit_block = self.block_index_for_pc(exit_pc)?;
        let body_block = self.block_index_for_pc(body_pc)?;
        let exhausted_or_exit = exhausted_block.unwrap_or(exit_block);

        let mask = self.load_reg(block, r_domain)?;
        let idx_alloca = self.emit_with_result(
            block,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        let zero = self.emit_i64_const(block, 0);
        self.emit(
            block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let header_block = self.new_aux_block(header_name);
        let load_block = self.new_aux_block(load_name);
        let advance_block = self.new_aux_block(&format!("{header_name}_absent"));
        let header_id = self.block_id_of(header_block);
        let load_id = self.block_id_of(load_block);
        let advance_id = self.block_id_of(advance_block);
        let body_id = self.block_id_of(body_block);
        let exhausted_or_exit_id = self.block_id_of(exhausted_or_exit);

        self.emit(
            block,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

        let cur_idx = self.emit_with_result(
            header_block,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let len_val = self.emit_i64_const(header_block, i64::from(universe_len));
        let in_universe = self.emit_with_result(
            header_block,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: cur_idx,
                rhs: len_val,
            },
        );
        self.emit(
            header_block,
            InstrNode::new(Inst::CondBr {
                cond: in_universe,
                then_target: load_id,
                then_args: vec![],
                else_target: exhausted_or_exit_id,
                else_args: vec![],
            }),
        );

        let cur_idx2 = self.emit_with_result(
            load_block,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(load_block, 1);
        let bit = self.emit_with_result(
            load_block,
            Inst::BinOp {
                op: BinOp::Shl,
                ty: Ty::I64,
                lhs: one,
                rhs: cur_idx2,
            },
        );
        let present_bits = self.emit_with_result(
            load_block,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: mask,
                rhs: bit,
            },
        );
        let present = self.emit_with_result(
            load_block,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: present_bits,
                rhs: zero,
            },
        );
        let binding_value =
            self.emit_set_bitmask_universe_value(load_block, cur_idx2, universe, opcode_label)?;
        self.store_reg_value(load_block, r_binding, binding_value)?;
        self.invalidate_reg_tracking(r_binding);
        if let Some(binding_shape) = binding_shape {
            self.aggregate_shapes.insert(r_binding, binding_shape);
        }
        self.emit(
            load_block,
            InstrNode::new(Inst::CondBr {
                cond: present,
                then_target: body_id,
                then_args: vec![],
                else_target: advance_id,
                else_args: vec![],
            }),
        );

        self.emit_advance_loop(advance_block, idx_alloca, header_id);

        Ok(binding_frame::BindingFrame {
            idx_alloca,
            domain_ptr: self.state_in_ptr,
            domain_len: len_val,
            binding_reg: r_binding,
            elem_ty: Ty::I64,
            header_block,
            exit_block,
        })
    }

    fn emit_set_bitmask_universe_value(
        &mut self,
        block_idx: usize,
        idx: ValueId,
        universe: &SetBitmaskUniverse,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        match universe {
            SetBitmaskUniverse::IntRange { lo } => {
                let lo = self.emit_i64_const(block_idx, *lo);
                Ok(self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: idx,
                        rhs: lo,
                    },
                ))
            }
            SetBitmaskUniverse::ExplicitInt(values) => {
                let mut result = self.emit_i64_const(block_idx, 0);
                for (table_idx, element) in values.iter().copied().enumerate().rev() {
                    let table_idx_val = self.emit_i64_const(block_idx, table_idx as i64);
                    let is_idx = self.emit_with_result(
                        block_idx,
                        Inst::ICmp {
                            op: ICmpOp::Eq,
                            ty: Ty::I64,
                            lhs: idx,
                            rhs: table_idx_val,
                        },
                    );
                    let value = self.emit_i64_const(block_idx, element);
                    result = self.emit_with_result(
                        block_idx,
                        Inst::Select {
                            ty: Ty::I64,
                            cond: is_idx,
                            then_val: value,
                            else_val: result,
                        },
                    );
                }
                Ok(result)
            }
            SetBitmaskUniverse::Exact(_) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask iteration requires exact universe metadata with integer elements"
            ))),
            SetBitmaskUniverse::Unknown => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask iteration requires exact universe metadata"
            ))),
        }
    }

    pub(super) fn require_const_pool(&self) -> Result<&'cp ConstantPool, TmirError> {
        self.const_pool.ok_or_else(|| {
            TmirError::UnsupportedOpcode(
                "LoadConst/Unchanged requires a constant pool; use lower_*_with_constants()"
                    .to_owned(),
            )
        })
    }

    // =====================================================================
    // Multi-function module support
    // =====================================================================

    /// Return pending callee OpIdx values that have been referenced by Call
    /// opcodes but not yet lowered.
    fn pending_callees(&mut self) -> Vec<u16> {
        let pending: Vec<u16> = self.pending_callee_indices.drain(..).collect();
        pending
    }

    /// Lower a callee function and add it to the module.
    ///
    /// Callee functions receive entrypoint context pointers plus a hidden
    /// fixed-width record/sequence/function return buffer. Scalar and
    /// materialized-set callees return i64 directly; compact compound callees
    /// copy into the hidden buffer and return that pointer encoded as i64.
    fn lower_callee(
        &mut self,
        callee_func: &BytecodeFunction,
        op_idx: u16,
    ) -> Result<(), TmirError> {
        if callee_func.instructions.is_empty() {
            return Err(TmirError::Emission(format!(
                "callee function '{}' (idx={op_idx}) has empty instruction stream",
                callee_func.name
            )));
        }

        // The FuncId was pre-allocated when the Call opcode was first seen.
        let tmir_func_id = *self.callee_map.get(&op_idx).ok_or_else(|| {
            TmirError::Emission(format!(
                "callee function idx={op_idx} not found in callee_map"
            ))
        })?;

        // Build the callee function type. Callees receive the same context
        // pointers as the entrypoint (out_ptr, state_in, [state_out,]
        // state_len), then a caller-owned fixed-width record/sequence/function
        // return buffer, then their own i64 arguments. Scalar and
        // materialized-set callees still return i64 directly; compact compound
        // callees copy into the buffer and return the buffer pointer encoded
        // as i64.
        let arity = callee_func.arity as usize;
        let callee_return_abi_shape = self.compact_return_abi_shape_for_callee(
            op_idx,
            self.inferred_callee_return_shape_for_lowered_args(op_idx, arity),
        )?;
        self.callee_lowered_return_abi_shapes
            .insert(op_idx, callee_return_abi_shape.clone());
        let mut callee_params = match self.mode {
            LoweringMode::Invariant => vec![Ty::Ptr, Ty::Ptr, Ty::I32],
            LoweringMode::NextState => vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::I32],
        };
        callee_params.push(Ty::Ptr);
        for _ in 0..arity {
            callee_params.push(Ty::I64);
        }
        let callee_ty = tmir::ty::FuncTy {
            params: callee_params,
            returns: vec![Ty::I64],
            is_vararg: false,
        };
        let ft_id = self.module.add_func_type(callee_ty);

        let block_targets = collect_block_targets_for_lowering(
            &callee_func.instructions,
            callee_return_abi_shape.is_some(),
        )?;

        // Allocate parameter ValueIds for the callee's context + user args.
        let callee_out_ptr = self.alloc_value();
        let callee_state_in = self.alloc_value();
        let callee_state_out = if self.mode == LoweringMode::NextState {
            Some(self.alloc_value())
        } else {
            None
        };
        let _callee_state_len = self.alloc_value();
        let callee_return_ptr = self.alloc_value();

        let mut user_arg_vals = Vec::with_capacity(arity);
        for _ in 0..arity {
            user_arg_vals.push(self.alloc_value());
        }

        // Create entry block with parameter bindings.
        let entry_block_id = BlockId::new(self.next_aux_block);
        self.next_aux_block += 1;

        let mut entry_params = vec![(callee_out_ptr, Ty::Ptr), (callee_state_in, Ty::Ptr)];
        if let Some(sop) = callee_state_out {
            entry_params.push((sop, Ty::Ptr));
        }
        entry_params.push((_callee_state_len, Ty::I32));
        entry_params.push((callee_return_ptr, Ty::Ptr));
        for &arg_val in &user_arg_vals {
            entry_params.push((arg_val, Ty::I64));
        }

        let mut entry_block = Block::new(entry_block_id);
        entry_block.params = entry_params;

        // Create blocks for branch targets.
        let mut blocks = vec![entry_block];
        let mut block_map = HashMap::new();
        block_map.insert(0_usize, 0_usize);

        for &target_pc in block_targets.iter() {
            if target_pc == 0 {
                continue;
            }
            let block_id = BlockId::new(self.next_aux_block);
            self.next_aux_block += 1;
            let block = Block::new(block_id);
            let idx = blocks.len();
            blocks.push(block);
            block_map.insert(target_pc, idx);
        }

        // Allocate register file: one alloca i64 per bytecode register.
        let mut register_file = Vec::new();
        let mut alloca_insts = Vec::new();
        for _reg in 0..=callee_func.max_register {
            let alloca_val = self.alloc_value();
            register_file.push(alloca_val);
            alloca_insts.push(
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(alloca_val),
            );
        }

        // Store user arguments into their register allocas. Parameters
        // occupy registers 0..arity-1 (matching bytecode calling convention).
        let mut param_stores = Vec::new();
        for (i, &param_val) in user_arg_vals.iter().enumerate() {
            if let Some(&alloca) = register_file.get(i) {
                param_stores.push(InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: alloca,
                    value: param_val,
                    align: None,
                    volatile: false,
                }));
            }
        }

        // Prepend allocas + param stores to entry block.
        let entry = &mut blocks[0];
        let mut init_insts: Vec<InstrNode> = alloca_insts;
        init_insts.extend(param_stores);
        for inst in init_insts.into_iter().rev() {
            entry.body.insert(0, inst);
        }

        // Build the tMIR function.
        let callee_name = namespaced_callee_name(&self.module.name, op_idx, &callee_func.name);
        let func = tmir::Function::new(tmir_func_id, callee_name, ft_id, entry_block_id);
        let tmir_function = tmir::Function { blocks, ..func };
        self.module.functions.push(tmir_function);
        let callee_func_module_idx = self.module.functions.len() - 1;

        // Save and swap context for lowering the callee body.
        let saved_register_file = std::mem::replace(&mut self.register_file, register_file);
        let saved_block_map = std::mem::replace(&mut self.block_map, block_map);
        let saved_func_idx = std::mem::replace(&mut self.func_idx, callee_func_module_idx);
        let saved_instruction_len =
            std::mem::replace(&mut self.instruction_len, callee_func.instructions.len());
        let saved_is_callee = std::mem::replace(&mut self.is_callee, true);
        let saved_out_ptr = std::mem::replace(&mut self.out_ptr, callee_out_ptr);
        let saved_state_in = std::mem::replace(&mut self.state_in_ptr, callee_state_in);
        let saved_state_out = std::mem::replace(&mut self.state_out_ptr, callee_state_out);
        let saved_callee_return_ptr =
            std::mem::replace(&mut self.callee_return_ptr, Some(callee_return_ptr));
        let saved_callee_return_abi_shape =
            std::mem::replace(&mut self.callee_return_abi_shape, callee_return_abi_shape);
        let saved_quantifier_loops = std::mem::take(&mut self.quantifier_loops);
        let saved_loop_next_stack = std::mem::take(&mut self.loop_next_stack);
        let saved_compact_state_slots = std::mem::take(&mut self.compact_state_slots);
        let saved_flat_funcdef_pair_list_regs =
            std::mem::take(&mut self.flat_funcdef_pair_list_regs);
        let saved_aggregate_shapes = std::mem::take(&mut self.aggregate_shapes);
        let saved_const_set_sizes = std::mem::take(&mut self.const_set_sizes);
        let saved_const_scalar_values = std::mem::take(&mut self.const_scalar_values);

        self.seed_callee_arg_shapes(op_idx, arity);

        // Lower the callee body.
        let result = self.lower_body(callee_func);

        // Restore context.
        self.register_file = saved_register_file;
        self.block_map = saved_block_map;
        self.func_idx = saved_func_idx;
        self.instruction_len = saved_instruction_len;
        self.is_callee = saved_is_callee;
        self.out_ptr = saved_out_ptr;
        self.state_in_ptr = saved_state_in;
        self.state_out_ptr = saved_state_out;
        self.callee_return_ptr = saved_callee_return_ptr;
        self.callee_return_abi_shape = saved_callee_return_abi_shape;
        self.quantifier_loops = saved_quantifier_loops;
        self.loop_next_stack = saved_loop_next_stack;
        self.compact_state_slots = saved_compact_state_slots;
        self.flat_funcdef_pair_list_regs = saved_flat_funcdef_pair_list_regs;
        self.aggregate_shapes = saved_aggregate_shapes;
        self.const_set_sizes = saved_const_set_sizes;
        self.const_scalar_values = saved_const_scalar_values;

        result
    }

    /// Register a Call target. Pre-allocates a FuncId if not yet seen.
    /// Returns the tMIR FuncId for the callee.
    ///
    /// FuncId assignment: entrypoint is always FuncId(0). Callees get
    /// FuncId(1), FuncId(2), etc. in the order they are first referenced.
    pub(super) fn register_call_target(&mut self, op_idx: u16) -> FuncId {
        if let Some(&func_id) = self.callee_map.get(&op_idx) {
            return func_id;
        }
        // Allocate the next available FuncId. The entrypoint occupies
        // FuncId(0), so callees start at FuncId(1).
        let func_id = FuncId::new(1 + self.callee_map.len() as u32);
        self.callee_map.insert(op_idx, func_id);
        self.pending_callee_indices.push(op_idx);
        func_id
    }

    // =====================================================================
    // Value allocation
    // =====================================================================

    pub(super) fn alloc_value(&mut self) -> ValueId {
        let v = ValueId::new(self.next_value);
        self.next_value += 1;
        v
    }

    // =====================================================================
    // Block management
    // =====================================================================

    pub(super) fn new_aux_block(&mut self, _prefix: &str) -> usize {
        let block_id = BlockId::new(self.next_aux_block);
        self.next_aux_block += 1;
        let block = Block::new(block_id);
        let func = &mut self.module.functions[self.func_idx];
        let idx = func.blocks.len();
        func.blocks.push(block);
        idx
    }

    pub(super) fn add_block_param(&mut self, block_idx: usize, ty: Ty) -> ValueId {
        let value = self.alloc_value();
        let func = &mut self.module.functions[self.func_idx];
        func.blocks[block_idx].params.push((value, ty));
        value
    }

    pub(super) fn emit(&mut self, block_idx: usize, node: InstrNode) {
        let func = &mut self.module.functions[self.func_idx];
        func.blocks[block_idx].body.push(node);
    }

    pub(super) fn emit_with_result(&mut self, block_idx: usize, inst: Inst) -> ValueId {
        let result = self.alloc_value();
        self.emit(block_idx, InstrNode::new(inst).with_result(result));
        result
    }

    pub(super) fn block_is_terminated(&self, block_idx: usize) -> bool {
        let func = &self.module.functions[self.func_idx];
        func.blocks[block_idx]
            .body
            .last()
            .map_or(false, |n| n.is_terminator())
    }

    pub(super) fn block_id_of(&self, block_idx: usize) -> BlockId {
        self.module.functions[self.func_idx].blocks[block_idx].id
    }

    pub(super) fn block_index_for_pc(&self, pc: usize) -> Result<usize, TmirError> {
        self.block_map
            .get(&pc)
            .copied()
            .ok_or_else(|| TmirError::Emission(format!("missing basic block for bytecode pc {pc}")))
    }

    // =====================================================================
    // Register file access
    // =====================================================================

    pub(super) fn reg_ptr(&self, reg: u8) -> Result<ValueId, TmirError> {
        self.register_file
            .get(usize::from(reg))
            .copied()
            .ok_or_else(|| {
                TmirError::Emission(format!(
                    "register r{reg} is outside allocated register file (size={})",
                    self.register_file.len()
                ))
            })
    }

    pub(super) fn load_reg(&mut self, block_idx: usize, reg: u8) -> Result<ValueId, TmirError> {
        let ptr = self.reg_ptr(reg)?;
        Ok(self.emit_with_result(
            block_idx,
            Inst::Load {
                ty: Ty::I64,
                ptr,
                align: None,
                volatile: false,
            },
        ))
    }

    pub(super) fn store_reg_imm(
        &mut self,
        block_idx: usize,
        reg: u8,
        value: i64,
    ) -> Result<(), TmirError> {
        self.compact_state_slots.remove(&reg);
        self.flat_funcdef_pair_list_regs.remove(&reg);
        let ptr = self.reg_ptr(reg)?;
        let const_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(value)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value: const_val,
                align: None,
                volatile: false,
            }),
        );
        Ok(())
    }

    pub(super) fn store_reg_value(
        &mut self,
        block_idx: usize,
        reg: u8,
        value: ValueId,
    ) -> Result<(), TmirError> {
        self.compact_state_slots.remove(&reg);
        self.flat_funcdef_pair_list_regs.remove(&reg);
        let ptr = self.reg_ptr(reg)?;
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
                align: None,
                volatile: false,
            }),
        );
        Ok(())
    }

    // =====================================================================
    // State variable access
    // =====================================================================

    pub(super) fn emit_state_slot_ptr(
        &mut self,
        block_idx: usize,
        state_ptr: ValueId,
        var_idx: u16,
    ) -> Result<ValueId, TmirError> {
        let slot_idx =
            self.compact_state_slot_offset_or_legacy(var_idx, "LoadVar compact state slot offset")?;
        Ok(self.emit_state_slot_ptr_at_slot(block_idx, state_ptr, slot_idx))
    }

    pub(super) fn emit_state_slot_ptr_at_slot(
        &mut self,
        block_idx: usize,
        state_ptr: ValueId,
        slot_idx: u32,
    ) -> ValueId {
        let idx_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(slot_idx)),
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base: state_ptr,
                indices: vec![idx_val],
            },
        )
    }

    fn lower_load_var(&mut self, block_idx: usize, rd: u8, var_idx: u16) -> Result<(), TmirError> {
        let state_ptr = self.state_in_ptr;
        let ptr = self.emit_state_slot_ptr(block_idx, state_ptr, var_idx)?;
        let value = self.emit_with_result(
            block_idx,
            Inst::Load {
                ty: Ty::I64,
                ptr,
                align: None,
                volatile: false,
            },
        );
        self.store_reg_value(block_idx, rd, value)?;
        self.track_loaded_state_var(rd, var_idx, state_ptr);
        Ok(())
    }

    fn lower_load_from_state_ptr(
        &mut self,
        block_idx: usize,
        state_ptr: ValueId,
        rd: u8,
        var_idx: u16,
    ) -> Result<(), TmirError> {
        let ptr = self.emit_state_slot_ptr(block_idx, state_ptr, var_idx)?;
        let value = self.emit_with_result(
            block_idx,
            Inst::Load {
                ty: Ty::I64,
                ptr,
                align: None,
                volatile: false,
            },
        );
        self.store_reg_value(block_idx, rd, value)?;
        self.track_loaded_state_var(rd, var_idx, state_ptr);
        Ok(())
    }

    fn lower_store_var(
        &mut self,
        block_idx: usize,
        var_idx: u16,
        rs: u8,
    ) -> Result<usize, TmirError> {
        let state_out = self.state_out_ptr.ok_or_else(|| {
            TmirError::Emission(
                "state_out pointer requested outside next-state lowering".to_owned(),
            )
        })?;
        let dst_base = self
            .compact_state_slot_offset_or_legacy(var_idx, "StoreVar compact state slot offset")?;
        let slot_count =
            self.compact_state_slot_count_or_legacy(var_idx, "StoreVar compact state slot count")?;
        let compact_source_slot = if self.is_flat_funcdef_pair_list(rs) {
            None
        } else {
            self.compact_state_slots.get(&rs).copied()
        };
        if let Some(source_slot) = compact_source_slot {
            let source_slot = if source_slot.requires_pointer_reload_in_block(block_idx) {
                let reloaded_ptr = self.load_reg_as_ptr(block_idx, rs)?;
                CompactStateSlot::pointer_backed_in_block(
                    reloaded_ptr,
                    source_slot.offset,
                    block_idx,
                )
            } else {
                source_slot
            };
            let raw_source_shape = self.aggregate_shapes.get(&rs).cloned().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "StoreVar compact source r{rs} for v{var_idx} has stale provenance without a tracked shape"
                ))
            })?;
            let dest_shape = self.compact_state_shape_for_var(var_idx).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "StoreVar compact destination v{var_idx} has no tracked fixed layout"
                ))
            })?;
            let source_shape =
                Self::complete_inferred_compact_shape_from_expected(&raw_source_shape, &dest_shape)
                    .unwrap_or(raw_source_shape);
            let source_slot_count = source_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "StoreVar compact source r{rs} for v{var_idx} has non-fixed shape {source_shape:?}"
                ))
            })?;
            let dest_slot_count = dest_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "StoreVar compact destination v{var_idx} has non-fixed shape {dest_shape:?}"
                ))
            })?;
            if dest_slot_count != slot_count {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "StoreVar compact source r{rs} is incompatible with v{var_idx}: source_shape={source_shape:?}, dest_shape={dest_shape:?}, source_slots={source_slot_count}, dest_slots={dest_slot_count}, expected_slots={slot_count}"
                )));
            }
            if source_slot_count == slot_count
                && Self::same_compact_physical_layout(&source_shape, &dest_shape)
                && !Self::contains_compact_sequence(&source_shape)
            {
                for offset in 0..slot_count {
                    let src_ptr = self.emit_state_slot_ptr_at_slot(
                        block_idx,
                        source_slot.source_ptr,
                        source_slot.offset + offset,
                    );
                    let value = self.emit_with_result(
                        block_idx,
                        Inst::Load {
                            ty: Ty::I64,
                            ptr: src_ptr,
                            align: None,
                            volatile: false,
                        },
                    );
                    let dst_ptr =
                        self.emit_state_slot_ptr_at_slot(block_idx, state_out, dst_base + offset);
                    self.emit(
                        block_idx,
                        InstrNode::new(Inst::Store {
                            ty: Ty::I64,
                            ptr: dst_ptr,
                            value,
                            align: None,
                            volatile: false,
                        }),
                    );
                }
                return Ok(block_idx);
            }
            if Self::can_copy_compact_aggregate_to_compact_slots(&source_shape, &dest_shape) {
                let copied = self.copy_compact_aggregate_to_compact_slots(
                    block_idx,
                    source_slot.source_ptr,
                    source_slot.offset,
                    &source_shape,
                    &dest_shape,
                    state_out,
                    dst_base,
                )?;
                if copied.slots_written != slot_count {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar copied {} compact slots for v{var_idx}, expected {slot_count}",
                        copied.slots_written
                    )));
                }
                return Ok(copied.block_idx);
            }
            return Err(TmirError::UnsupportedOpcode(format!(
                "StoreVar compact source r{rs} is incompatible with v{var_idx}: source_shape={source_shape:?}, dest_shape={dest_shape:?}, source_slots={source_slot_count}, dest_slots={dest_slot_count}, expected_slots={slot_count}"
            )));
        }
        if let (Some(raw_source_shape), Some(dest_shape)) = (
            self.aggregate_shapes.get(&rs).cloned(),
            self.compact_state_shape_for_var(var_idx),
        ) {
            let source_shape =
                Self::complete_inferred_compact_shape_from_expected(&raw_source_shape, &dest_shape)
                    .unwrap_or(raw_source_shape);
            if Self::can_copy_flat_aggregate_to_compact_slots(&source_shape, &dest_shape)
                && dest_shape.compact_slot_count() == Some(slot_count)
            {
                let source_ptr = self.load_reg_as_ptr(block_idx, rs)?;
                let copied = self.copy_flat_aggregate_to_compact_slots(
                    block_idx,
                    source_ptr,
                    &source_shape,
                    &dest_shape,
                    state_out,
                    dst_base,
                    self.is_flat_funcdef_pair_list(rs),
                )?;
                if copied.slots_written != slot_count {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar copied {} slots for v{var_idx}, expected {slot_count}",
                        copied.slots_written
                    )));
                }
                return Ok(copied.block_idx);
            }
        }
        if slot_count > 1 {
            return Err(TmirError::UnsupportedOpcode(format!(
                "StoreVar for multi-slot variable v{var_idx} from r{rs} requires a compact aggregate source"
            )));
        }

        if let Some(dest_shape) = self.compact_state_shape_for_var(var_idx) {
            let source_shape = self.aggregate_shapes.get(&rs).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "StoreVar for compact scalar variable v{var_idx} from r{rs} requires tracked scalar source shape, got dest_shape={dest_shape:?}"
                ))
            })?;
            if let AggregateShape::SetBitmask {
                universe_len,
                universe,
            } = &dest_shape
            {
                Self::compact_set_bitmask_valid_mask(*universe_len, "StoreVar")?;
                match source_shape {
                    AggregateShape::ExactIntSet { values } => {
                        let Some(mask) = exact_int_set_mask_for_set_bitmask_universe(
                            values,
                            *universe_len,
                            universe,
                        ) else {
                            return Err(TmirError::UnsupportedOpcode(format!(
                                "StoreVar for compact SetBitmask variable v{var_idx} from exact integer Set r{rs} requires all values inside the destination universe, got source_shape={source_shape:?}, dest_shape={dest_shape:?}"
                            )));
                        };
                        let value = self.emit_i64_const(block_idx, mask);
                        let ptr = self.emit_state_slot_ptr_at_slot(block_idx, state_out, dst_base);
                        self.emit(
                            block_idx,
                            InstrNode::new(Inst::Store {
                                ty: Ty::I64,
                                ptr,
                                value,
                                align: None,
                                volatile: false,
                            }),
                        );
                        return Ok(block_idx);
                    }
                    AggregateShape::Set { len: 0, .. } => {
                        let value = self.emit_i64_const(block_idx, 0);
                        let ptr = self.emit_state_slot_ptr_at_slot(block_idx, state_out, dst_base);
                        self.emit(
                            block_idx,
                            InstrNode::new(Inst::Store {
                                ty: Ty::I64,
                                ptr,
                                value,
                                align: None,
                                volatile: false,
                            }),
                        );
                        return Ok(block_idx);
                    }
                    AggregateShape::Interval { lo, hi } => {
                        if !interval_convertible_to_set_bitmask(*lo, *hi, *universe_len, universe) {
                            return Err(TmirError::UnsupportedOpcode(format!(
                                "StoreVar for compact SetBitmask variable v{var_idx} from interval r{rs} requires all values inside the destination universe, got source_shape={source_shape:?}, dest_shape={dest_shape:?}"
                            )));
                        }
                        let Some(mask) = interval_mask_for_set_bitmask_universe(
                            *lo,
                            *hi,
                            *universe_len,
                            universe,
                        ) else {
                            return Err(TmirError::UnsupportedOpcode(format!(
                                "StoreVar for compact SetBitmask variable v{var_idx} from interval r{rs} requires integer destination universe metadata, got source_shape={source_shape:?}, dest_shape={dest_shape:?}"
                            )));
                        };
                        let value = self.emit_i64_const(block_idx, mask);
                        let ptr = self.emit_state_slot_ptr_at_slot(block_idx, state_out, dst_base);
                        self.emit(
                            block_idx,
                            InstrNode::new(Inst::Store {
                                ty: Ty::I64,
                                ptr,
                                value,
                                align: None,
                                volatile: false,
                            }),
                        );
                        return Ok(block_idx);
                    }
                    _ => {}
                }
                if !source_shape.compatible_set_bitmask_universe(*universe_len, universe) {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "StoreVar for compact SetBitmask variable v{var_idx} from r{rs} requires exact-compatible SetBitmask source, got source_shape={source_shape:?}, dest_shape={dest_shape:?}"
                    )));
                }
            }
            if !Self::is_single_slot_flat_aggregate_value(source_shape)
                || !Self::is_single_slot_flat_aggregate_value(&dest_shape)
                || !Self::compatible_flat_aggregate_value(source_shape, &dest_shape)
            {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "StoreVar for compact scalar variable v{var_idx} from r{rs} requires compatible scalar source, got source_shape={source_shape:?}, dest_shape={dest_shape:?}"
                )));
            }
        }

        let value = self.load_reg(block_idx, rs)?;
        let ptr = self.emit_state_slot_ptr_at_slot(block_idx, state_out, dst_base);
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
                align: None,
                volatile: false,
            }),
        );
        Ok(block_idx)
    }

    // =====================================================================
    // Out-pointer field access
    // =====================================================================

    pub(super) fn emit_out_field_ptr(&mut self, block_idx: usize, offset: usize) -> ValueId {
        let offset_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(offset as i128),
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: self.out_ptr,
                indices: vec![offset_val],
            },
        )
    }

    // =====================================================================
    // Return / error emission
    // =====================================================================

    fn callee_compact_return_reg_at(&self, instructions: &[Opcode], pc: usize) -> Option<u8> {
        if !self.is_callee || self.callee_return_abi_shape.is_none() {
            return None;
        }
        match instructions.get(pc) {
            Some(Opcode::Ret { rs }) => Some(*rs),
            _ => None,
        }
    }

    fn branch_target_or_callee_return_edge(
        &mut self,
        block_idx: usize,
        instructions: &[Opcode],
        target_pc: usize,
        target_block: Option<usize>,
        edge_name: &str,
    ) -> Result<BlockId, TmirError> {
        if let Some(rs) = self.callee_compact_return_reg_at(instructions, target_pc) {
            let return_block = self.new_aux_block(edge_name);
            self.emit_callee_return_from_reg(return_block, rs)?;
            return Ok(self.block_id_of(return_block));
        }
        let target_block = target_block.ok_or_else(|| {
            TmirError::Emission(format!(
                "missing non-return branch target block for pc {target_pc} from block {block_idx}"
            ))
        })?;
        Ok(self.block_id_of(target_block))
    }

    fn emit_callee_return_from_reg(
        &mut self,
        block_idx: usize,
        rs: u8,
    ) -> Result<usize, TmirError> {
        // Scalar callees return i64 directly. Fixed-width compound callees copy
        // into the caller-owned return buffer before returning its pointer as
        // i64, so aggregate pointers to callee-local allocas never escape.
        let result_shape = self.aggregate_shapes.get(&rs).cloned();
        let abi_shape = self.callee_return_abi_shape.clone();
        let (return_block, result) = if let Some(abi_shape) = abi_shape {
            let raw_source_shape = result_shape.ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "callee compact compound return for r{rs} requires a tracked source shape for ABI shape {abi_shape:?}"
                ))
            })?;
            let source_shape =
                Self::complete_inferred_compact_shape_from_expected(&raw_source_shape, &abi_shape)
                    .unwrap_or(raw_source_shape);
            if !Self::compatible_compact_materialization_value(&source_shape, &abi_shape) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "callee compact compound return shape for r{rs} is incompatible with ABI shape: source={source_shape:?}, abi={abi_shape:?}"
                )));
            }
            let slot_count = Self::caller_owned_return_slot_count(&abi_shape).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "callee compact compound return ABI requires fixed-width shape for r{rs}, got {abi_shape:?}"
                ))
            })?;
            let return_ptr = self.callee_return_ptr.ok_or_else(|| {
                TmirError::Emission("callee aggregate return buffer is unavailable".to_owned())
            })?;
            let (current_block, source_ptr, source_offset) =
                if Self::is_compact_compound_aggregate(&abi_shape) {
                    let materialized =
                        self.materialize_reg_as_compact_source(block_idx, rs, &abi_shape)?;
                    (
                        materialized.block_idx,
                        materialized.slot.source_ptr,
                        materialized.slot.offset,
                    )
                } else {
                    (block_idx, self.load_reg_as_ptr(block_idx, rs)?, 0)
                };
            let current_block = if let AggregateShape::BoundedSet { max_len, .. } = abi_shape {
                if source_offset != 0 {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "callee bounded-set return for r{rs} must be backed by a materialized aggregate pointer, got source offset {source_offset}"
                    )));
                }
                self.copy_bounded_materialized_return_buffer(
                    current_block,
                    source_ptr,
                    return_ptr,
                    max_len,
                )?
            } else {
                for offset in 0..slot_count {
                    let source_slot = source_offset.checked_add(offset).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(
                            "callee aggregate return source slot overflow".to_owned(),
                        )
                    })?;
                    let value = self.load_at_offset(current_block, source_ptr, source_slot);
                    self.store_at_offset(current_block, return_ptr, offset, value);
                }
                current_block
            };
            (current_block, self.ptr_to_i64(current_block, return_ptr))
        } else if let Some(shape) = result_shape {
            if Self::is_known_pointer_backed_return_shape(&shape) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "callee aggregate return for r{rs} has no caller-owned return ABI shape: source={shape:?}"
                )));
            }
            (block_idx, self.load_reg(block_idx, rs)?)
        } else {
            (block_idx, self.load_reg(block_idx, rs)?)
        };
        self.emit(
            return_block,
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        );
        Ok(return_block)
    }

    fn copy_bounded_materialized_return_buffer(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        return_ptr: ValueId,
        max_len: u32,
    ) -> Result<usize, TmirError> {
        let runtime_len = self.load_at_offset(block_idx, source_ptr, 0);
        let zero = self.emit_i64_const(block_idx, 0);
        let len_nonnegative = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sge,
                ty: Ty::I64,
                lhs: runtime_len,
                rhs: zero,
            },
        );

        let cap_check = self.new_aux_block("bounded_return_cap_check");
        let copy_init = self.new_aux_block("bounded_return_copy_init");
        let error_block = self.new_aux_block("bounded_return_error");
        let cap_check_id = self.block_id_of(cap_check);
        let copy_init_id = self.block_id_of(copy_init);
        let error_id = self.block_id_of(error_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: len_nonnegative,
                then_target: cap_check_id,
                then_args: vec![],
                else_target: error_id,
                else_args: vec![],
            }),
        );

        let max_len_value = self.emit_i64_const(cap_check, i64::from(max_len));
        let len_within_capacity = self.emit_with_result(
            cap_check,
            Inst::ICmp {
                op: ICmpOp::Sle,
                ty: Ty::I64,
                lhs: runtime_len,
                rhs: max_len_value,
            },
        );
        self.emit(
            cap_check,
            InstrNode::new(Inst::CondBr {
                cond: len_within_capacity,
                then_target: copy_init_id,
                then_args: vec![],
                else_target: error_id,
                else_args: vec![],
            }),
        );

        self.emit_runtime_error_and_return(error_block, JitRuntimeErrorKind::TypeMismatch);

        self.store_at_offset(copy_init, return_ptr, 0, runtime_len);
        let one = self.emit_i64_const(copy_init, 1);
        let idx_alloca = self.emit_with_result(
            copy_init,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            copy_init,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: one,
                align: None,
                volatile: false,
            }),
        );

        let copy_header = self.new_aux_block("bounded_return_copy_header");
        let copy_body = self.new_aux_block("bounded_return_copy_body");
        let copy_done = self.new_aux_block("bounded_return_copy_done");
        let copy_header_id = self.block_id_of(copy_header);
        let copy_body_id = self.block_id_of(copy_body);
        let copy_done_id = self.block_id_of(copy_done);

        self.emit(
            copy_init,
            InstrNode::new(Inst::Br {
                target: copy_header_id,
                args: vec![],
            }),
        );

        let idx = self.emit_with_result(
            copy_header,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let should_copy = self.emit_with_result(
            copy_header,
            Inst::ICmp {
                op: ICmpOp::Sle,
                ty: Ty::I64,
                lhs: idx,
                rhs: runtime_len,
            },
        );
        self.emit(
            copy_header,
            InstrNode::new(Inst::CondBr {
                cond: should_copy,
                then_target: copy_body_id,
                then_args: vec![],
                else_target: copy_done_id,
                else_args: vec![],
            }),
        );

        let idx_body = self.emit_with_result(
            copy_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let value = self.load_at_dynamic_offset(copy_body, source_ptr, idx_body);
        self.store_at_dynamic_offset(copy_body, return_ptr, idx_body, value);
        let next_idx = self.emit_with_result(
            copy_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: idx_body,
                rhs: one,
            },
        );
        self.emit(
            copy_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            copy_body,
            InstrNode::new(Inst::Br {
                target: copy_header_id,
                args: vec![],
            }),
        );

        let tail_start = self.emit_with_result(
            copy_done,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: runtime_len,
                rhs: one,
            },
        );
        self.emit(
            copy_done,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: tail_start,
                align: None,
                volatile: false,
            }),
        );

        let zero_header = self.new_aux_block("bounded_return_zero_header");
        let zero_body = self.new_aux_block("bounded_return_zero_body");
        let zero_done = self.new_aux_block("bounded_return_zero_done");
        let zero_header_id = self.block_id_of(zero_header);
        let zero_body_id = self.block_id_of(zero_body);
        let zero_done_id = self.block_id_of(zero_done);

        self.emit(
            copy_done,
            InstrNode::new(Inst::Br {
                target: zero_header_id,
                args: vec![],
            }),
        );

        let zero_idx = self.emit_with_result(
            zero_header,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let zero_max = self.emit_i64_const(zero_header, i64::from(max_len));
        let should_zero = self.emit_with_result(
            zero_header,
            Inst::ICmp {
                op: ICmpOp::Sle,
                ty: Ty::I64,
                lhs: zero_idx,
                rhs: zero_max,
            },
        );
        self.emit(
            zero_header,
            InstrNode::new(Inst::CondBr {
                cond: should_zero,
                then_target: zero_body_id,
                then_args: vec![],
                else_target: zero_done_id,
                else_args: vec![],
            }),
        );

        let zero_idx_body = self.emit_with_result(
            zero_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        self.store_at_dynamic_offset(zero_body, return_ptr, zero_idx_body, zero);
        let next_zero_idx = self.emit_with_result(
            zero_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: zero_idx_body,
                rhs: one,
            },
        );
        self.emit(
            zero_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_zero_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            zero_body,
            InstrNode::new(Inst::Br {
                target: zero_header_id,
                args: vec![],
            }),
        );

        Ok(zero_done)
    }

    pub(super) fn emit_success_return(
        &mut self,
        block_idx: usize,
        rs: u8,
    ) -> Result<(), TmirError> {
        let result = self.load_reg(block_idx, rs)?;

        // Store status = Ok
        let status_ptr = self.emit_out_field_ptr(block_idx, STATUS_OFFSET);
        let status_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(i128::from(JitStatus::Ok as u8)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I8,
                ptr: status_ptr,
                value: status_val,
                align: None,
                volatile: false,
            }),
        );

        // Store value
        let value_ptr = self.emit_out_field_ptr(block_idx, VALUE_OFFSET);
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: value_ptr,
                value: result,
                align: None,
                volatile: false,
            }),
        );

        // Return void
        self.emit(block_idx, InstrNode::new(Inst::Return { values: vec![] }));
        Ok(())
    }

    /// Return from the current function without mutating `JitCallOut`.
    ///
    /// Entrypoints return `void` and consume their status/value via the out
    /// struct. Callees still share the same out struct for fallback/runtime
    /// signaling, but their function type returns `i64`, so they must return a
    /// dummy scalar when unwinding due to a non-Ok shared status.
    pub(super) fn emit_passthrough_status_return(&mut self, block_idx: usize) {
        if self.is_callee {
            let zero = self.emit_with_result(
                block_idx,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                },
            );
            self.emit(
                block_idx,
                InstrNode::new(Inst::Return { values: vec![zero] }),
            );
        } else {
            self.emit(block_idx, InstrNode::new(Inst::Return { values: vec![] }));
        }
    }

    pub(super) fn emit_runtime_error_and_return(
        &mut self,
        block_idx: usize,
        kind: JitRuntimeErrorKind,
    ) {
        // Any lowering that emits a runtime error disqualifies NoPanic.
        self.encountered_runtime_error = true;

        // Store status = RuntimeError
        let status_ptr = self.emit_out_field_ptr(block_idx, STATUS_OFFSET);
        let status_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(i128::from(JitStatus::RuntimeError as u8)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I8,
                ptr: status_ptr,
                value: status_val,
                align: None,
                volatile: false,
            }),
        );

        // Store err_kind
        let err_kind_ptr = self.emit_out_field_ptr(block_idx, ERR_KIND_OFFSET);
        let err_kind_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(i128::from(kind as u8)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I8,
                ptr: err_kind_ptr,
                value: err_kind_val,
                align: None,
                volatile: false,
            }),
        );

        if std::env::var_os("TLA2_TMIR_RUNTIME_ERROR_BLOCK_DIAGNOSTICS").is_some() {
            let file_id = u32::try_from(self.func_idx).unwrap_or(u32::MAX);
            let span_start = u32::try_from(block_idx).unwrap_or(u32::MAX);
            let span_end = self.block_id_of(block_idx).index();
            for (offset, value) in [
                (ERR_FILE_ID_OFFSET, file_id),
                (ERR_SPAN_START_OFFSET, span_start),
                (ERR_SPAN_END_OFFSET, span_end),
            ] {
                let ptr = self.emit_out_field_ptr(block_idx, offset);
                let value = self.emit_with_result(
                    block_idx,
                    Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(i128::from(value)),
                    },
                );
                self.emit(
                    block_idx,
                    InstrNode::new(Inst::Store {
                        ty: Ty::I32,
                        ptr,
                        value,
                        align: None,
                        volatile: false,
                    }),
                );
            }
        }

        self.emit_passthrough_status_return(block_idx);
    }

    // =====================================================================
    // Aggregate helpers (sets, sequences, records)
    // =====================================================================
    //
    // TLA+ compound types (sets, sequences, records) are represented in tMIR as
    // heap-allocated aggregates. Each aggregate is a contiguous block of i64
    // slots allocated via `alloca`:
    //
    //   Sets/Sequences: slot[0] = length, slot[1..=N] = elements
    //   Records: slot[0..N] = field values (no length header, count is static)
    //
    // The aggregate pointer is cast to i64 (PtrToInt) and stored in the bytecode
    // register file. When accessed, it is cast back (IntToPtr). This keeps the
    // register file uniformly i64-typed while allowing compound values.
    /// Allocate a contiguous block of `count` i64 slots and return the pointer.
    pub(super) fn alloc_aggregate(&mut self, block_idx: usize, count: u32) -> ValueId {
        let count_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(count)),
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(count_val),
                align: None,
            },
        )
    }

    /// Allocate a contiguous block of `count_i64` i64 slots when the slot
    /// count is only available as an SSA value.
    pub(super) fn alloc_dynamic_i64_slots(
        &mut self,
        block_idx: usize,
        count_i64: ValueId,
    ) -> ValueId {
        let count_i32 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: count_i64,
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(count_i32),
                align: None,
            },
        )
    }

    /// Store a pointer value into a bytecode register as i64 (PtrToInt).
    pub(super) fn store_reg_ptr(
        &mut self,
        block_idx: usize,
        reg: u8,
        ptr: ValueId,
    ) -> Result<(), TmirError> {
        let as_int = self.ptr_to_i64(block_idx, ptr);
        self.store_reg_value(block_idx, reg, as_int)
    }

    /// Cast an aggregate pointer to the uniform i64 register representation.
    pub(super) fn ptr_to_i64(&mut self, block_idx: usize, ptr: ValueId) -> ValueId {
        self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: ptr,
            },
        )
    }

    /// Load a pointer from a bytecode register (IntToPtr of stored i64).
    pub(super) fn load_reg_as_ptr(
        &mut self,
        block_idx: usize,
        reg: u8,
    ) -> Result<ValueId, TmirError> {
        if let Some(AggregateShape::SetBitmask { .. }) = self.aggregate_shapes.get(&reg) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "load_reg_as_ptr: compact SetBitmask r{reg} is a raw mask, not an aggregate pointer"
            )));
        }
        if self
            .compact_state_slots
            .get(&reg)
            .copied()
            .is_some_and(CompactStateSlot::is_raw_compact_slot)
        {
            return Err(TmirError::UnsupportedOpcode(format!(
                "load_reg_as_ptr: raw compact slot r{reg} cannot be reinterpreted as an aggregate pointer"
            )));
        }
        let int_val = self.load_reg(block_idx, reg)?;
        Ok(self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: int_val,
            },
        ))
    }

    pub(super) fn reject_raw_compact_pointer_fallback(
        &self,
        reg: u8,
        context: &str,
    ) -> Result<(), TmirError> {
        if self
            .compact_state_slots
            .get(&reg)
            .copied()
            .is_some_and(CompactStateSlot::is_raw_compact_slot)
        {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: raw compact source r{reg} cannot fall back to aggregate-pointer lowering"
            )));
        }
        Ok(())
    }

    pub(super) fn compact_state_slot_for_use(
        &mut self,
        block_idx: usize,
        reg: u8,
    ) -> Result<Option<CompactStateSlot>, TmirError> {
        if self.is_flat_funcdef_pair_list(reg) {
            return Ok(None);
        }
        let Some(source_slot) = self.compact_state_slots.get(&reg).copied() else {
            return Ok(None);
        };
        if !source_slot.requires_pointer_reload_in_block(block_idx) {
            return Ok(Some(source_slot));
        }
        let reloaded_ptr = self.load_reg_as_ptr(block_idx, reg)?;
        Ok(Some(CompactStateSlot::pointer_backed_in_block(
            reloaded_ptr,
            source_slot.offset,
            block_idx,
        )))
    }

    pub(super) fn load_reg_as_ptr_or_materialize_raw_compact(
        &mut self,
        block_idx: usize,
        reg: u8,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        if self.is_flat_funcdef_pair_list(reg) {
            return self.load_reg_as_ptr(block_idx, reg);
        }
        let Some(source_slot) = self.compact_state_slots.get(&reg).copied() else {
            return self.load_reg_as_ptr(block_idx, reg);
        };
        if !source_slot.is_raw_compact_slot() {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact aggregate r{reg} is pointer-backed compact storage and \
                 cannot fall back to flat aggregate-pointer lowering"
            )));
        }

        let shape = self.aggregate_shapes.get(&reg).cloned().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: raw compact source r{reg} requires a tracked shape before materializing an aggregate pointer"
            ))
        })?;
        if shape.contains_unknown_set_bitmask() {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: raw compact source r{reg} contains unknown-universe SetBitmask payload and cannot be materialized as an aggregate pointer"
            )));
        }
        match shape {
            AggregateShape::Function {
                len,
                domain_lo: Some(domain_lo),
                value: Some(value_shape),
            } => {
                let value_stride = value_shape.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: raw compact function r{reg} requires fixed-width values, got {value_shape:?}"
                    ))
                })?;
                if value_stride != 1 {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: raw compact function r{reg} cannot materialize multi-slot values as generic function pairs, got {value_shape:?}"
                    )));
                }
                let pair_slots = len.checked_mul(2).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: raw compact function r{reg} pair slots overflow"
                    ))
                })?;
                let total_slots = pair_slots.checked_add(1).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: raw compact function r{reg} total slots overflow"
                    ))
                })?;
                let result_ptr = self.alloc_aggregate(block_idx, total_slots);
                let len_value = self.emit_i64_const(block_idx, i64::from(len));
                self.store_at_offset(block_idx, result_ptr, 0, len_value);
                for idx in 0..len {
                    let key = domain_lo.checked_add(i64::from(idx)).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "{context}: raw compact function r{reg} domain key overflow"
                        ))
                    })?;
                    let key_value = self.emit_i64_const(block_idx, key);
                    self.store_at_offset(block_idx, result_ptr, 1 + idx * 2, key_value);
                    let value = self.load_at_offset(
                        block_idx,
                        source_slot.source_ptr,
                        source_slot.offset + idx,
                    );
                    self.store_at_offset(block_idx, result_ptr, 2 + idx * 2, value);
                }
                Ok(result_ptr)
            }
            AggregateShape::Record { .. } => {
                let slot_count = shape.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: raw compact record r{reg} requires fixed-width shape, got {shape:?}"
                    ))
                })?;
                let result_ptr = self.alloc_aggregate(block_idx, slot_count);
                for slot in 0..slot_count {
                    let value = self.load_at_offset(
                        block_idx,
                        source_slot.source_ptr,
                        source_slot.offset + slot,
                    );
                    self.store_at_offset(block_idx, result_ptr, slot, value);
                }
                Ok(result_ptr)
            }
            AggregateShape::Sequence { ref element, .. } => {
                if element
                    .as_deref()
                    .is_some_and(|shape| shape.compact_slot_count().is_some_and(|n| n != 1))
                {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: raw compact sequence r{reg} cannot materialize multi-slot elements as generic sequence slots, got {shape:?}"
                    )));
                }
                let slot_count = shape.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: raw compact sequence r{reg} requires fixed-width shape, got {shape:?}"
                    ))
                })?;
                let result_ptr = self.alloc_aggregate(block_idx, slot_count);
                for slot in 0..slot_count {
                    let value = self.load_at_offset(
                        block_idx,
                        source_slot.source_ptr,
                        source_slot.offset + slot,
                    );
                    self.store_at_offset(block_idx, result_ptr, slot, value);
                }
                Ok(result_ptr)
            }
            other => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: raw compact source r{reg} with shape {other:?} cannot be materialized as an aggregate pointer"
            ))),
        }
    }

    /// Store an i64 value at a given offset within an aggregate pointer.
    pub(super) fn store_at_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        offset: u32,
        value: ValueId,
    ) {
        let idx = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(offset)),
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx],
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
                align: None,
                volatile: false,
            }),
        );
    }

    /// Load an i64 value from a given offset within an aggregate pointer.
    pub(super) fn load_at_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        offset: u32,
    ) -> ValueId {
        let idx = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(offset)),
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx],
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::Load {
                ty: Ty::I64,
                ptr,
                align: None,
                volatile: false,
            },
        )
    }

    /// Load an i64 value at a dynamic index within an aggregate pointer.
    pub(super) fn load_at_dynamic_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        index: ValueId,
    ) -> ValueId {
        // index is i64, truncate to i32 for GEP index
        let idx_i32 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: index,
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx_i32],
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::Load {
                ty: Ty::I64,
                ptr,
                align: None,
                volatile: false,
            },
        )
    }

    /// Store an i64 value at a dynamic index within an aggregate pointer.
    pub(super) fn store_at_dynamic_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        index: ValueId,
        value: ValueId,
    ) {
        let idx_i32 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: index,
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx_i32],
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
                align: None,
                volatile: false,
            }),
        );
    }

    /// Emit an i64 constant.
    pub(super) fn emit_i64_const(&mut self, block_idx: usize, value: i64) -> ValueId {
        self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(value)),
            },
        )
    }

    // =====================================================================
    // Body lowering
    // =====================================================================

    fn lower_body(&mut self, bytecode_func: &BytecodeFunction) -> Result<(), TmirError> {
        let mut current_block: Option<usize> = Some(self.block_index_for_pc(0)?);

        for (pc, opcode) in bytecode_func.instructions.iter().enumerate() {
            // Check if this PC starts a new basic block.
            if let Some(&target_block) = self.block_map.get(&pc) {
                match current_block {
                    Some(block) if block != target_block => {
                        // Emit fallthrough branch if the current block isn't terminated.
                        if !self.block_is_terminated(block) {
                            let target_id = self.block_id_of(target_block);
                            self.emit(
                                block,
                                InstrNode::new(Inst::Br {
                                    target: target_id,
                                    args: vec![],
                                }),
                            );
                        }
                        current_block = Some(target_block);
                    }
                    None => {
                        current_block = Some(target_block);
                    }
                    _ => {}
                }
            }

            let Some(block) = current_block else {
                continue;
            };

            current_block = self
                .lower_opcode(pc, opcode, block, &bytecode_func.instructions)
                .map_err(|err| {
                    TmirError::Emission(format!("while lowering pc {pc} opcode {opcode:?}: {err}"))
                })?;

            // Handle fallthrough to next block.
            if let Some(block) = current_block {
                if let Some(&next_block) = self.block_map.get(&(pc + 1)) {
                    if next_block != block && !self.block_is_terminated(block) {
                        let next_id = self.block_id_of(next_block);
                        self.emit(
                            block,
                            InstrNode::new(Inst::Br {
                                target: next_id,
                                args: vec![],
                            }),
                        );
                        current_block = Some(next_block);
                    }
                }
            }
        }

        // Verify the function ends with a terminator.
        if let Some(block) = current_block {
            if !self.block_is_terminated(block) {
                return Err(TmirError::Emission(format!(
                    "function reaches end of body without a terminator"
                )));
            }
        }

        Ok(())
    }

    fn lower_opcode(
        &mut self,
        pc: usize,
        opcode: &Opcode,
        block: usize,
        instructions: &[Opcode],
    ) -> Result<Option<usize>, TmirError> {
        match *opcode {
            Opcode::LoadImm { rd, value } => {
                self.invalidate_reg_tracking(rd);
                self.store_reg_imm(block, rd, value)?;
                self.aggregate_shapes
                    .insert(rd, AggregateShape::Scalar(ScalarShape::Int));
                self.record_scalar(rd, value);
                Ok(Some(block))
            }
            Opcode::LoadBool { rd, value } => {
                self.invalidate_reg_tracking(rd);
                self.store_reg_imm(block, rd, i64::from(value))?;
                self.aggregate_shapes
                    .insert(rd, AggregateShape::Scalar(ScalarShape::Bool));
                self.record_scalar(rd, i64::from(value));
                Ok(Some(block))
            }
            Opcode::LoadConst { rd, idx } => {
                // LoadConst may or may not produce a scalar — we don't
                // track constants from the const pool here; invalidate
                // conservatively.
                self.invalidate_reg_tracking(rd);
                self.lower_load_const(block, rd, idx)
            }
            Opcode::LoadVar { rd, var_idx } => {
                self.invalidate_reg_tracking(rd);
                self.lower_load_var(block, rd, var_idx)?;
                Ok(Some(block))
            }
            Opcode::LoadPrime { rd, var_idx } => match self.mode {
                LoweringMode::Invariant => Err(TmirError::NotEligible {
                    reason: "LoadPrime requires next-state lowering".to_owned(),
                }),
                LoweringMode::NextState => {
                    let state_out = self.state_out_ptr.ok_or_else(|| {
                        TmirError::Emission(
                            "missing state_out parameter for next-state lowering".to_owned(),
                        )
                    })?;
                    self.lower_load_from_state_ptr(block, state_out, rd, var_idx)?;
                    Ok(Some(block))
                }
            },
            Opcode::StoreVar { var_idx, rs } => match self.mode {
                LoweringMode::Invariant => Err(TmirError::NotEligible {
                    reason: "StoreVar requires next-state lowering".to_owned(),
                }),
                LoweringMode::NextState => {
                    let block = self.lower_store_var(block, var_idx, rs)?;
                    Ok(Some(block))
                }
            },
            Opcode::Move { rd, rs } => {
                let value = self.load_reg(block, rs)?;
                let source_shape = self.aggregate_shapes.get(&rs).cloned();
                let source_set_size = self.const_set_sizes.get(&rs).copied();
                let source_scalar = self.const_scalar_values.get(&rs).copied();
                let source_compact_slot = self.compact_state_slots.get(&rs).copied();
                let is_flat_funcdef_pair_list = self.flat_funcdef_pair_list_regs.contains(&rs);
                self.store_reg_value(block, rd, value)?;
                // Propagate tracking from source to destination.
                if let Some(shape) = source_shape {
                    self.aggregate_shapes.insert(rd, shape);
                } else {
                    self.aggregate_shapes.remove(&rd);
                }
                if let Some(n) = source_set_size {
                    self.const_set_sizes.insert(rd, n);
                } else {
                    self.const_set_sizes.remove(&rd);
                }
                if let Some(v) = source_scalar {
                    self.const_scalar_values.insert(rd, v);
                } else {
                    self.const_scalar_values.remove(&rd);
                }
                if let Some(slot) = source_compact_slot {
                    self.compact_state_slots.insert(rd, slot);
                } else {
                    self.compact_state_slots.remove(&rd);
                }
                if is_flat_funcdef_pair_list {
                    self.flat_funcdef_pair_list_regs.insert(rd);
                } else {
                    self.flat_funcdef_pair_list_regs.remove(&rd);
                }
                Ok(Some(block))
            }

            // Arithmetic
            Opcode::AddInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, OverflowOp::AddOverflow)
            }
            Opcode::SubInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, OverflowOp::SubOverflow)
            }
            Opcode::MulInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, OverflowOp::MulOverflow)
            }
            Opcode::IntDiv { rd, r1, r2 } => self.lower_checked_division(block, rd, r1, r2, true),
            Opcode::ModInt { rd, r1, r2 } => self.lower_checked_division(block, rd, r1, r2, false),
            Opcode::DivInt { rd, r1, r2 } => self.lower_real_division(block, rd, r1, r2),
            Opcode::NegInt { rd, rs } => self.lower_checked_negation(block, rd, rs),

            // Comparison
            Opcode::Eq { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Eq)?;
                Ok(Some(block))
            }
            Opcode::Neq { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Ne)?;
                Ok(Some(block))
            }
            Opcode::LtInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Slt)?;
                Ok(Some(block))
            }
            Opcode::LeInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Sle)?;
                Ok(Some(block))
            }
            Opcode::GtInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Sgt)?;
                Ok(Some(block))
            }
            Opcode::GeInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Sge)?;
                Ok(Some(block))
            }

            // Boolean
            Opcode::And { rd, r1, r2 } => {
                self.lower_boolean_binary(block, rd, r1, r2, BinOp::And)?;
                Ok(Some(block))
            }
            Opcode::Or { rd, r1, r2 } => {
                self.lower_boolean_binary(block, rd, r1, r2, BinOp::Or)?;
                Ok(Some(block))
            }
            Opcode::Not { rd, rs } => {
                self.lower_not(block, rd, rs)?;
                Ok(Some(block))
            }
            Opcode::Implies { rd, r1, r2 } => {
                self.lower_implies(block, rd, r1, r2)?;
                Ok(Some(block))
            }
            Opcode::Equiv { rd, r1, r2 } => {
                self.lower_equiv(block, rd, r1, r2)?;
                Ok(Some(block))
            }

            // Control flow
            Opcode::Jump { offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "Jump")?;
                if let Some(rs) = self.callee_compact_return_reg_at(instructions, target_pc) {
                    self.emit_callee_return_from_reg(block, rs)?;
                    return Ok(None);
                }
                let target_block = self.block_index_for_pc(target_pc)?;
                let target_id = self.block_id_of(target_block);
                self.emit(
                    block,
                    InstrNode::new(Inst::Br {
                        target: target_id,
                        args: vec![],
                    }),
                );
                Ok(None)
            }
            Opcode::JumpTrue { rs, offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "JumpTrue")?;
                let fallthrough_pc = pc + 1;
                let cond = self.load_reg(block, rs)?;
                let zero = self.emit_with_result(
                    block,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    },
                );
                let cond_bool = self.emit_with_result(
                    block,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I64,
                        lhs: cond,
                        rhs: zero,
                    },
                );
                let target_block = if self
                    .callee_compact_return_reg_at(instructions, target_pc)
                    .is_some()
                {
                    None
                } else {
                    Some(self.block_index_for_pc(target_pc)?)
                };
                let fallthrough_block = if self
                    .callee_compact_return_reg_at(instructions, fallthrough_pc)
                    .is_some()
                {
                    None
                } else {
                    Some(self.block_index_for_pc(fallthrough_pc)?)
                };
                let target_id = self.branch_target_or_callee_return_edge(
                    block,
                    instructions,
                    target_pc,
                    target_block,
                    "jump_true_ret",
                )?;
                let fallthrough_id = self.branch_target_or_callee_return_edge(
                    block,
                    instructions,
                    fallthrough_pc,
                    fallthrough_block,
                    "jump_true_fallthrough_ret",
                )?;
                self.emit(
                    block,
                    InstrNode::new(Inst::CondBr {
                        cond: cond_bool,
                        then_target: target_id,
                        then_args: vec![],
                        else_target: fallthrough_id,
                        else_args: vec![],
                    }),
                );
                Ok(None)
            }
            Opcode::JumpFalse { rs, offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "JumpFalse")?;
                let fallthrough_pc = pc + 1;
                let cond = self.load_reg(block, rs)?;
                let zero = self.emit_with_result(
                    block,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    },
                );
                let cond_bool = self.emit_with_result(
                    block,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I64,
                        lhs: cond,
                        rhs: zero,
                    },
                );
                let target_block = if self
                    .callee_compact_return_reg_at(instructions, target_pc)
                    .is_some()
                {
                    None
                } else {
                    Some(self.block_index_for_pc(target_pc)?)
                };
                let fallthrough_block = if self
                    .callee_compact_return_reg_at(instructions, fallthrough_pc)
                    .is_some()
                {
                    None
                } else {
                    Some(self.block_index_for_pc(fallthrough_pc)?)
                };
                let target_id = self.branch_target_or_callee_return_edge(
                    block,
                    instructions,
                    target_pc,
                    target_block,
                    "jump_false_ret",
                )?;
                let fallthrough_id = self.branch_target_or_callee_return_edge(
                    block,
                    instructions,
                    fallthrough_pc,
                    fallthrough_block,
                    "jump_false_fallthrough_ret",
                )?;
                // JumpFalse: branch to target when FALSE, fallthrough when TRUE
                self.emit(
                    block,
                    InstrNode::new(Inst::CondBr {
                        cond: cond_bool,
                        then_target: fallthrough_id,
                        then_args: vec![],
                        else_target: target_id,
                        else_args: vec![],
                    }),
                );
                Ok(None)
            }
            Opcode::CondMove { rd, cond, rs } => {
                let const_selected_shape =
                    self.const_scalar_values
                        .get(&cond)
                        .copied()
                        .and_then(|cond_value| {
                            if cond_value != 0 {
                                self.aggregate_shapes.get(&rs).cloned()
                            } else {
                                self.aggregate_shapes.get(&rd).cloned()
                            }
                        });
                let block = self.lower_cond_move(block, rd, cond, rs)?;
                if let Some(shape) = const_selected_shape {
                    if let Some(len) = shape.tracked_len() {
                        self.const_set_sizes.insert(rd, len);
                    }
                    self.aggregate_shapes.insert(rd, shape);
                }
                Ok(Some(block))
            }
            Opcode::Ret { rs } => {
                if self.is_callee {
                    self.emit_callee_return_from_reg(block, rs)?;
                } else {
                    // Entrypoint functions write to JitCallOut.
                    self.emit_success_return(block, rs)?;
                }
                Ok(None)
            }
            Opcode::Halt => {
                self.emit_runtime_error_and_return(block, JitRuntimeErrorKind::TypeMismatch);
                Ok(None)
            }
            Opcode::Nop => Ok(Some(block)),

            // Set operations
            Opcode::SetEnum { rd, start, count } => {
                let shape = self.set_enum_shape_from_registers(start, count);
                self.lower_set_enum(block, rd, start, count)?;
                if matches!(shape, AggregateShape::SetBitmask { .. }) {
                    self.const_set_sizes.remove(&rd);
                } else {
                    // SetEnum's cardinality is compile-time known by construction.
                    self.record_set_size(rd, u32::from(count));
                }
                self.aggregate_shapes.insert(rd, shape);
                self.const_scalar_values.remove(&rd);
                Ok(Some(block))
            }
            Opcode::SetIn { rd, elem, set } => {
                // Boolean result; clobber any prior tracking on rd.
                self.invalidate_reg_tracking(rd);
                self.lower_set_in(block, rd, elem, set)
            }
            Opcode::SetUnion { rd, r1, r2 } => {
                // Union cardinality is at most |r1| + |r2| but we cannot
                // compute the deduplicated size without a scan. Preserve only
                // a range-shape upper bound for consumers that use runtime
                // lengths, not exact domain arity.
                let shape = finite_set_union_shape(
                    self.aggregate_shapes.get(&r1),
                    self.aggregate_shapes.get(&r2),
                );
                self.invalidate_reg_tracking(rd);
                let next = self.lower_set_union(block, rd, r1, r2)?;
                if let Some(shape) = shape {
                    if !matches!(
                        self.aggregate_shapes.get(&rd),
                        Some(AggregateShape::SetBitmask { .. })
                    ) {
                        self.aggregate_shapes.insert(rd, shape);
                    }
                }
                Ok(next)
            }
            Opcode::SetIntersect { rd, r1, r2 } => {
                let shape = finite_set_intersect_shape(
                    self.aggregate_shapes.get(&r1),
                    self.aggregate_shapes.get(&r2),
                );
                self.invalidate_reg_tracking(rd);
                let next = self.lower_set_intersect(block, rd, r1, r2)?;
                if let Some(shape) = shape {
                    if !matches!(
                        self.aggregate_shapes.get(&rd),
                        Some(AggregateShape::SetBitmask { .. })
                    ) {
                        self.aggregate_shapes.insert(rd, shape);
                    }
                }
                Ok(next)
            }
            Opcode::SetDiff { rd, r1, r2 } => {
                let shape = finite_set_diff_shape(
                    self.aggregate_shapes.get(&r1),
                    self.aggregate_shapes.get(&r2),
                );
                self.invalidate_reg_tracking(rd);
                let next = self.lower_set_diff(block, rd, r1, r2)?;
                if let Some(shape) = shape {
                    if !matches!(
                        self.aggregate_shapes.get(&rd),
                        Some(AggregateShape::SetBitmask { .. })
                    ) {
                        self.aggregate_shapes.insert(rd, shape);
                    }
                }
                Ok(next)
            }
            Opcode::Subseteq { rd, r1, r2 } => {
                self.invalidate_reg_tracking(rd);
                self.lower_subseteq(block, rd, r1, r2)
            }
            Opcode::Powerset { rd, rs } => {
                self.invalidate_reg_tracking(rd);
                self.lower_powerset(block, rd, rs)?;
                Ok(Some(block))
            }
            Opcode::Range { rd, lo, hi } => {
                self.compact_state_slots.remove(&rd);
                // Track compile-time known range size when both endpoints
                // are known scalars. Empty ranges have len 0; overflow loses
                // boundedness rather than inventing a saturated length.
                if let (Some(lo_v), Some(hi_v)) = (self.scalar_of(lo), self.scalar_of(hi)) {
                    if let Some(n) = interval_len_u32(lo_v, hi_v) {
                        self.record_set_size(rd, n);
                        self.aggregate_shapes
                            .insert(rd, AggregateShape::Interval { lo: lo_v, hi: hi_v });
                    } else {
                        self.aggregate_shapes.remove(&rd);
                        self.const_set_sizes.remove(&rd);
                    }
                } else {
                    self.aggregate_shapes.insert(rd, AggregateShape::FiniteSet);
                    self.const_set_sizes.remove(&rd);
                }
                self.const_scalar_values.remove(&rd);
                self.lower_range(block, rd, lo, hi)
            }

            // Sequence operations
            Opcode::SeqNew { rd, start, count } => {
                self.lower_seq_new(block, rd, start, count)?;
                self.aggregate_shapes.insert(
                    rd,
                    AggregateShape::Sequence {
                        extent: SequenceExtent::Exact(u32::from(count)),
                        element: self.uniform_register_shapes(start, count),
                    },
                );
                self.const_set_sizes.remove(&rd);
                self.const_scalar_values.remove(&rd);
                Ok(Some(block))
            }

            // Tuple operations
            Opcode::TupleNew { rd, start, count } => {
                self.lower_tuple_new(block, rd, start, count)?;
                self.aggregate_shapes.insert(
                    rd,
                    AggregateShape::Sequence {
                        extent: SequenceExtent::Exact(u32::from(count)),
                        element: self.uniform_register_shapes(start, count),
                    },
                );
                self.const_set_sizes.remove(&rd);
                self.const_scalar_values.remove(&rd);
                Ok(Some(block))
            }
            Opcode::TupleGet { rd, rs, idx } => {
                let shape = sequence_element_shape(self.aggregate_shapes.get(&rs));
                self.lower_tuple_get(block, rd, rs, idx)?;
                self.record_aggregate_shape(rd, shape);
                Ok(Some(block))
            }

            // Record operations
            Opcode::RecordNew {
                rd,
                fields_start,
                values_start,
                count,
            } => {
                self.lower_record_new(block, rd, fields_start, values_start, count)?;
                Ok(Some(block))
            }
            Opcode::RecordSet {
                rd,
                fields_start,
                values_start,
                count,
            } => {
                self.lower_record_set(block, rd, fields_start, values_start, count)?;
                Ok(Some(block))
            }
            Opcode::RecordGet { rd, rs, field_idx } => {
                self.lower_record_get(block, rd, rs, field_idx)?;
                Ok(Some(block))
            }

            // Builtin operations (Cardinality, Len, Head, Tail, Append)
            Opcode::CallBuiltin {
                rd,
                builtin,
                args_start,
                argc,
            } => {
                use tla_tir::bytecode::BuiltinOp;
                match builtin {
                    BuiltinOp::Cardinality => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Cardinality expects 1 argument, got {argc}"
                            )));
                        }
                        self.lower_cardinality(block, rd, args_start)?;
                        self.aggregate_shapes
                            .insert(rd, AggregateShape::Scalar(ScalarShape::Int));
                        self.const_set_sizes.remove(&rd);
                        self.const_scalar_values.remove(&rd);
                        Ok(Some(block))
                    }
                    BuiltinOp::Len => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Len expects 1 argument, got {argc}"
                            )));
                        }
                        self.lower_seq_len(block, rd, args_start)?;
                        self.aggregate_shapes
                            .insert(rd, AggregateShape::Scalar(ScalarShape::Int));
                        self.const_set_sizes.remove(&rd);
                        self.const_scalar_values.remove(&rd);
                        Ok(Some(block))
                    }
                    BuiltinOp::Head => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Head expects 1 argument, got {argc}"
                            )));
                        }
                        let shape = sequence_head_shape(self.aggregate_shapes.get(&args_start));
                        let next = self.lower_seq_head(block, rd, args_start)?;
                        if !self.compact_state_slots.contains_key(&rd) {
                            self.record_aggregate_shape(rd, shape);
                        }
                        Ok(next)
                    }
                    BuiltinOp::Tail => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Tail expects 1 argument, got {argc}"
                            )));
                        }
                        let shape = sequence_tail_shape(self.aggregate_shapes.get(&args_start));
                        let next = self.lower_seq_tail(block, rd, args_start)?;
                        if !self.compact_state_slots.contains_key(&rd) {
                            self.record_aggregate_shape(rd, shape);
                        }
                        Ok(next)
                    }
                    BuiltinOp::Append => {
                        if argc != 2 {
                            return Err(TmirError::Emission(format!(
                                "Append expects 2 arguments, got {argc}"
                            )));
                        }
                        let elem_reg = args_start.checked_add(1).ok_or_else(|| {
                            TmirError::Emission(format!(
                                "Append argument register overflow: args_start={args_start} + 1"
                            ))
                        })?;
                        let shape = sequence_append_shape(
                            self.aggregate_shapes.get(&args_start),
                            self.aggregate_shapes.get(&elem_reg),
                        );
                        let next =
                            self.lower_seq_append(block, rd, args_start, elem_reg, shape.clone())?;
                        if !self.compact_state_slots.contains_key(&rd) {
                            self.record_aggregate_shape(rd, shape);
                        }
                        Ok(next)
                    }
                    BuiltinOp::Seq => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Seq expects 1 argument, got {argc}"
                            )));
                        }
                        self.lower_seq_set(block, rd, args_start)?;
                        Ok(Some(block))
                    }
                    BuiltinOp::FoldFunctionOnSetSum => {
                        if argc != 2 {
                            return Err(TmirError::Emission(format!(
                                "FoldFunctionOnSetSum expects 2 arguments, got {argc}"
                            )));
                        }
                        let set_arg = args_start.checked_add(1).ok_or_else(|| {
                            TmirError::Emission(format!(
                                "FoldFunctionOnSetSum argument register overflow: args_start={args_start} + 1"
                            ))
                        })?;
                        self.lower_fold_function_on_set_sum(block, rd, args_start, set_arg)
                    }
                    other_builtin => Err(TmirError::UnsupportedOpcode(format!(
                        "CallBuiltin({other_builtin:?})"
                    ))),
                }
            }

            // Quantifier operations
            Opcode::ForallBegin {
                rd,
                r_binding,
                r_domain,
                loop_end,
            } => self.lower_forall_begin(pc, block, rd, r_binding, r_domain, loop_end),
            Opcode::ForallNext {
                rd,
                r_binding,
                r_body,
                ..
            } => self.lower_forall_next(pc, block, rd, r_binding, r_body),
            Opcode::ExistsBegin {
                rd,
                r_binding,
                r_domain,
                loop_end,
            } => self.lower_exists_begin(pc, block, rd, r_binding, r_domain, loop_end),
            Opcode::ExistsNext {
                rd,
                r_binding,
                r_body,
                ..
            } => self.lower_exists_next(pc, block, rd, r_binding, r_body),
            Opcode::ChooseBegin {
                rd,
                r_binding,
                r_domain,
                loop_end,
            } => self.lower_choose_begin(pc, block, rd, r_binding, r_domain, loop_end),
            Opcode::ChooseNext {
                rd,
                r_binding,
                r_body,
                ..
            } => self.lower_choose_next(pc, block, rd, r_binding, r_body),
            Opcode::SetFilterBegin {
                rd,
                r_binding,
                r_domain,
                loop_end,
            } => self.lower_set_filter_begin(pc, block, rd, r_binding, r_domain, loop_end),

            // Phase 4: Function operations
            Opcode::FuncApply { rd, func, arg } => self.lower_func_apply(block, rd, func, arg),
            Opcode::Domain { rd, rs } => self.lower_domain(block, rd, rs),
            Opcode::FuncExcept {
                rd,
                func,
                path,
                val,
            } => self.lower_func_except(block, rd, func, path, val),
            Opcode::FuncDefBegin {
                rd,
                r_binding,
                r_domain,
                loop_end,
            } => self.lower_func_def_begin(pc, block, rd, r_binding, r_domain, loop_end),
            Opcode::LoopNext {
                r_binding, r_body, ..
            } => self.lower_loop_next(pc, block, r_binding, r_body),

            // Phase 5: Constants and frame conditions
            Opcode::Unchanged { rd, start, count } => self.lower_unchanged(block, rd, start, count),

            // Phase 6: Function sets
            Opcode::FuncSet { rd, domain, range } => {
                self.lower_func_set(block, rd, domain, range)?;
                Ok(Some(block))
            }

            // Inter-function call
            Opcode::Call {
                rd,
                op_idx,
                args_start,
                argc,
            } => self.lower_call(block, rd, op_idx, args_start, argc),

            other => Err(TmirError::UnsupportedOpcode(format!("{other:?}"))),
        }
    }
}

// =========================================================================
// Free functions
// =========================================================================

fn collect_block_targets(instructions: &[Opcode]) -> Result<BTreeSet<usize>, TmirError> {
    collect_block_targets_for_lowering(instructions, false)
}

fn compact_return_edge_target(instructions: &[Opcode], pc: usize, enabled: bool) -> bool {
    enabled && matches!(instructions.get(pc), Some(Opcode::Ret { .. }))
}

fn collect_block_targets_for_lowering(
    instructions: &[Opcode],
    compact_return_edges: bool,
) -> Result<BTreeSet<usize>, TmirError> {
    let mut targets = BTreeSet::new();
    targets.insert(0);

    for (pc, opcode) in instructions.iter().enumerate() {
        match *opcode {
            Opcode::Jump { offset } => {
                let target = validate_forward_target(pc, offset, instructions.len(), "Jump")?;
                if !compact_return_edge_target(instructions, target, compact_return_edges) {
                    targets.insert(target);
                }
            }
            Opcode::JumpTrue { offset, .. } => {
                let target = validate_forward_target(pc, offset, instructions.len(), "JumpTrue")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(TmirError::NotEligible {
                        reason: format!("JumpTrue at pc {pc} has no fallthrough instruction"),
                    });
                }
                if !compact_return_edge_target(instructions, target, compact_return_edges) {
                    targets.insert(target);
                }
                if !compact_return_edge_target(instructions, fallthrough, compact_return_edges) {
                    targets.insert(fallthrough);
                }
            }
            Opcode::JumpFalse { offset, .. } => {
                let target = validate_forward_target(pc, offset, instructions.len(), "JumpFalse")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(TmirError::NotEligible {
                        reason: format!("JumpFalse at pc {pc} has no fallthrough instruction"),
                    });
                }
                if !compact_return_edge_target(instructions, target, compact_return_edges) {
                    targets.insert(target);
                }
                if !compact_return_edge_target(instructions, fallthrough, compact_return_edges) {
                    targets.insert(fallthrough);
                }
            }
            // Quantifier/loop Begin opcodes: fallthrough (pc+1) is the body start,
            // loop_end target is the exit block.
            Opcode::ForallBegin { loop_end, .. }
            | Opcode::ExistsBegin { loop_end, .. }
            | Opcode::ChooseBegin { loop_end, .. }
            | Opcode::SetFilterBegin { loop_end, .. }
            | Opcode::FuncDefBegin { loop_end, .. } => {
                let exit_target =
                    validate_forward_target(pc, loop_end, instructions.len(), "QuantBegin")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(TmirError::NotEligible {
                        reason: format!("QuantBegin at pc {pc} has no fallthrough instruction"),
                    });
                }
                targets.insert(exit_target);
                targets.insert(fallthrough);
            }
            // Quantifier/loop Next opcodes: loop_begin is a backward jump to the body,
            // fallthrough (pc+1) is the exit block.
            Opcode::ForallNext { loop_begin, .. }
            | Opcode::ExistsNext { loop_begin, .. }
            | Opcode::ChooseNext { loop_begin, .. }
            | Opcode::LoopNext { loop_begin, .. } => {
                let body_target =
                    validate_any_target(pc, loop_begin, instructions.len(), "QuantNext")?;
                let fallthrough = pc + 1;
                if fallthrough < instructions.len() {
                    targets.insert(fallthrough);
                }
                targets.insert(body_target);
            }
            _ => {}
        }
    }

    Ok(targets)
}

fn validate_forward_target(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<usize, TmirError> {
    let target = resolve_target(pc, offset)?;
    if target <= pc {
        return Err(TmirError::NotEligible {
            reason: format!(
                "{opcode_name} at pc {pc} must target a later instruction (offset {offset})"
            ),
        });
    }
    if target >= len {
        return Err(TmirError::NotEligible {
            reason: format!("{opcode_name} at pc {pc} targets {target}, outside body len {len}"),
        });
    }
    Ok(target)
}

/// Validate a jump target that may go backward (used by quantifier Next opcodes).
fn validate_any_target(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<usize, TmirError> {
    let target = resolve_target(pc, offset)?;
    if target >= len {
        return Err(TmirError::NotEligible {
            reason: format!("{opcode_name} at pc {pc} targets {target}, outside body len {len}"),
        });
    }
    Ok(target)
}

fn resolve_target(pc: usize, offset: i32) -> Result<usize, TmirError> {
    let target = (pc as i64) + i64::from(offset);
    usize::try_from(target).map_err(|_| TmirError::NotEligible {
        reason: format!("jump target before start of function: pc {pc}, offset {offset}"),
    })
}

/// Push a `ProofAnnotation` onto a proofs vec only if not already present.
/// De-duplication keeps the IR stable under redundant annotation calls
/// (e.g. nested quantifier lowering that re-visits the same header).
fn push_unique_proof(
    proofs: &mut Vec<tmir::proof::ProofAnnotation>,
    proof: tmir::proof::ProofAnnotation,
) {
    if !proofs.iter().any(|p| p == &proof) {
        proofs.push(proof);
    }
}
