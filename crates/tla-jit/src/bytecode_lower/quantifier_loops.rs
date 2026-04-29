// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier loop lowering: ForallBegin/Next, ExistsBegin/Next, ChooseBegin/Next.
//!
//! Compiles quantifier opcodes to Cranelift counted loops. Two domain sources:
//!
//! 1. **Pre-materialized arrays** (`QuantifierDomains`): The caller provides
//!    domain elements at compile time. The array is leaked into JIT memory and
//!    accessed via embedded pointer.
//!
//! 2. **Range-based iteration** (new): When a `Range` opcode produced the domain
//!    register, the loop iterates `lo..hi` (inclusive) without materializing an
//!    array. The `RangeTracker` thread-local maps domain registers to their
//!    lo/hi register indices.
//!
//! # Register convention
//!
//! After `*Begin`, the `r_domain` register is repurposed:
//! - Array mode: holds the 0-based loop iteration index.
//! - Range mode: holds the current value (starts at lo, incremented each iteration).
//!
//! # Body pattern optimizations
//!
//! - **Forall conjunction early-exit**: When the body is `A /\ B /\ ...`, each
//!   conjunct is checked independently. If any conjunct is false, the loop
//!   short-circuits immediately without evaluating remaining conjuncts.
//!
//! - **Exists disjunction early-exit**: When the body is `A \/ B \/ ...`, each
//!   disjunct is checked independently. If any disjunct is true, the loop
//!   short-circuits immediately.
//!
//! These patterns are detected by `analyze_quantifier_body()` which scans the
//! instruction stream between Begin and Next for And/Or chains feeding r_body.

use crate::error::JitError;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, Block, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use num_traits::ToPrimitive;
use std::alloc::Layout;
use std::collections::{BTreeSet, HashMap};
use tla_tir::bytecode::Opcode;

use super::RegMap;

/// Pre-materialized domain elements for quantifier compilation.
///
/// Maps the `r_domain` register index to the array of i64 domain elements.
/// The caller is responsible for evaluating the domain set at compile time
/// and providing the elements here.
pub type QuantifierDomains = HashMap<u8, Vec<i64>>;

// Thread-local storage for leaked domain array allocations.
//
// Domain arrays are leaked so their pointers remain valid for the lifetime
// of the JIT'd code. Tracked here for cleanup when the JIT module is dropped.
thread_local! {
    pub(crate) static LEAKED_DOMAIN_ALLOCS: std::cell::RefCell<Vec<(*mut u8, Layout)>>
        = std::cell::RefCell::new(Vec::new());
}

// Thread-local tracker for registers that hold Range-produced virtual sets.
//
// When `set_ops::lower_set_op` processes a `Range { rd, lo, hi }` opcode,
// it records `rd -> (lo, hi)` here. `lower_quantifier_begin` checks this
// tracker to decide whether to use range-based iteration.
thread_local! {
    pub(crate) static RANGE_TRACKER: std::cell::RefCell<HashMap<u8, (u8, u8)>>
        = std::cell::RefCell::new(HashMap::new());
}

/// Record that register `rd` holds a Range set `lo..hi`.
/// Called from `set_ops::lower_set_op` when processing `Range` opcodes.
pub(crate) fn record_range_for_quantifier(rd: u8, lo: u8, hi: u8) {
    RANGE_TRACKER.with(|rt| {
        rt.borrow_mut().insert(rd, (lo, hi));
    });
}

/// Clear the range tracker. Should be called at the start of each compilation.
pub(crate) fn clear_range_tracker() {
    RANGE_TRACKER.with(|rt| {
        rt.borrow_mut().clear();
    });
}

/// Extract pre-materialized quantifier domains from a bytecode function's
/// instruction stream and constant pool.
///
/// Handles three domain patterns:
///
/// 1. **SetEnum pattern**: `LoadConst/LoadImm` into element registers, then
///    `SetEnum { rd, start, count }` → extract constant elements.
///
/// 2. **LoadConst Interval pattern**: `LoadConst { rd, idx }` where the constant
///    is a `Value::Interval(lo, hi)` → generate `[lo, lo+1, ..., hi]`.
///
/// 3. **LoadConst Set pattern**: `LoadConst { rd, idx }` where the constant is
///    a `Value::Set` of `SmallInt` values → extract elements directly.
///
/// Range-based quantifiers (where a `Range` opcode produces the domain register)
/// are handled separately by the `RangeTracker` at lowering time.
///
/// Returns a `QuantifierDomains` map from `r_domain` register to domain elements.
pub(crate) fn collect_quantifier_domains_from_bytecode(
    instructions: &[Opcode],
    constants: Option<&tla_tir::bytecode::ConstantPool>,
) -> QuantifierDomains {
    let mut domains = QuantifierDomains::new();
    let pool = match constants {
        Some(p) => p,
        None => return domains,
    };

    // Step 1: Build maps for domain source tracking.

    // SetEnum { rd, start, count } → record rd -> (start, count)
    let mut set_enum_map: HashMap<u8, (u8, u8)> = HashMap::new();
    // LoadConst { rd, idx } where the constant is a set/interval → record rd -> elements
    let mut const_domain_map: HashMap<u8, Vec<i64>> = HashMap::new();
    // Range opcodes are tracked separately — record rd so we skip them
    let mut range_regs: HashMap<u8, bool> = HashMap::new();
    // Scalar constants from LoadImm/LoadConst/LoadBool for SetEnum element tracking
    let mut reg_constants: HashMap<u8, i64> = HashMap::new();

    for op in instructions {
        match *op {
            Opcode::SetEnum { rd, start, count } => {
                set_enum_map.insert(rd, (start, count));
            }
            Opcode::Range { rd, .. } => {
                // Range domains are handled by RangeTracker at lowering time.
                range_regs.insert(rd, true);
            }
            Opcode::LoadImm { rd, value } => {
                reg_constants.insert(rd, value);
            }
            Opcode::LoadBool { rd, value } => {
                reg_constants.insert(rd, if value { 1 } else { 0 });
            }
            Opcode::LoadConst { rd, idx } => {
                let val = pool.get_value(idx);
                match val {
                    tla_value::Value::SmallInt(n) => {
                        reg_constants.insert(rd, *n);
                    }
                    tla_value::Value::Bool(b) => {
                        reg_constants.insert(rd, if *b { 1 } else { 0 });
                    }
                    // String and ModelValue constants used as SetEnum elements:
                    // intern to NameId for consistent JIT representation.
                    // Part of #3958.
                    tla_value::Value::String(s) => {
                        let name_id = tla_core::intern_name(s);
                        reg_constants.insert(rd, name_id.0 as i64);
                    }
                    tla_value::Value::ModelValue(s) => {
                        let name_id = tla_core::intern_name(s);
                        reg_constants.insert(rd, name_id.0 as i64);
                    }
                    tla_value::Value::Interval(iv) => {
                        // Interval [lo, hi] — extract all integer elements.
                        if let (Some(lo), Some(hi)) = (iv.low().to_i64(), iv.high().to_i64()) {
                            if hi >= lo && (hi - lo) < 1000 {
                                let elements: Vec<i64> = (lo..=hi).collect();
                                const_domain_map.insert(rd, elements);
                            }
                        }
                    }
                    tla_value::Value::Set(sorted_set) => {
                        // Finite set — extract scalar elements as i64.
                        // Handles SmallInt, Bool, String, and ModelValue elements.
                        // String/ModelValue are interned to NameId, matching how
                        // scalar_ops.rs handles LoadConst/String. This enables
                        // quantifier domain materialization for specs like
                        // `\A proc \in {"p1", "p2"} : ...` where the domain is
                        // a set of model values or strings.
                        // Part of #3958.
                        let mut elements = Vec::new();
                        let mut all_scalar = true;
                        for elem in sorted_set.iter() {
                            match elem {
                                tla_value::Value::SmallInt(n) => elements.push(*n),
                                tla_value::Value::Bool(b) => elements.push(if *b { 1 } else { 0 }),
                                tla_value::Value::String(s) => {
                                    let name_id = tla_core::intern_name(s);
                                    elements.push(name_id.0 as i64);
                                }
                                tla_value::Value::ModelValue(s) => {
                                    let name_id = tla_core::intern_name(s);
                                    elements.push(name_id.0 as i64);
                                }
                                _ => {
                                    all_scalar = false;
                                    break;
                                }
                            }
                        }
                        if all_scalar && !elements.is_empty() {
                            const_domain_map.insert(rd, elements);
                        }
                    }
                    other => {
                        if std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() == Ok("1") {
                            eprintln!(
                                "[jit-domain-debug] LoadConst rd={rd} idx={idx} → unhandled type: {}",
                                other.type_name()
                            );
                        }
                    }
                }
            }
            _ => {}
        }
    }

    if std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() == Ok("1") {
        eprintln!(
            "[jit-domain-debug] Step1 results: const_domain_map keys={:?}, set_enum_map keys={:?}, range_regs keys={:?}, reg_constants count={}",
            const_domain_map.keys().collect::<Vec<_>>(),
            set_enum_map.keys().collect::<Vec<_>>(),
            range_regs.keys().collect::<Vec<_>>(),
            reg_constants.len(),
        );
    }

    // Step 2: For each quantifier Begin, resolve its domain.
    for op in instructions {
        let r_domain = match *op {
            Opcode::ForallBegin { r_domain, .. }
            | Opcode::ExistsBegin { r_domain, .. }
            | Opcode::ChooseBegin { r_domain, .. } => r_domain,
            _ => continue,
        };

        // Already have a domain for this register
        if domains.contains_key(&r_domain) {
            continue;
        }

        // Skip Range-produced domains (handled by RangeTracker at lowering time)
        if range_regs.contains_key(&r_domain) {
            continue;
        }

        // Try SetEnum pattern: domain register from SetEnum with constant elements
        if let Some(&(start, count)) = set_enum_map.get(&r_domain) {
            let mut elements = Vec::with_capacity(count as usize);
            let mut all_resolved = true;
            for i in 0..count {
                let elem_reg = start + i;
                if let Some(&val) = reg_constants.get(&elem_reg) {
                    elements.push(val);
                } else {
                    all_resolved = false;
                    break;
                }
            }
            if all_resolved && !elements.is_empty() {
                domains.insert(r_domain, elements);
                continue;
            }
        }

        // Try LoadConst pattern: domain register from LoadConst of Interval or Set
        if let Some(elements) = const_domain_map.get(&r_domain) {
            domains.insert(r_domain, elements.clone());
        }
    }

    domains
}

/// The kind of quantifier loop.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum QuantifierKind {
    Forall,
    Exists,
    Choose,
}

/// Domain source for a quantifier loop.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum DomainSource {
    /// Pre-materialized array: base pointer + element count.
    Array { base_ptr_addr: i64, count: usize },
    /// Range-based iteration: lo and hi register indices.
    /// The binding variable takes values lo, lo+1, ..., hi (inclusive).
    Range { r_lo: u8, r_hi: u8 },
    /// Compound-tracked set iteration: reads count and elements from a
    /// serialized set buffer at runtime. Format: [TAG_SET, count, (TAG, val)...]
    /// The base pointer is saved to a stack slot for access in the advance step.
    CompoundSet {
        /// Stack slot holding the base pointer to the set buffer.
        base_ptr_slot: cranelift_codegen::ir::StackSlot,
    },
}

/// Metadata for an active quantifier loop, pushed by `*Begin` and popped by `*Next`.
pub(crate) struct QuantifierLoopInfo {
    /// How the domain elements are accessed.
    domain: DomainSource,
    /// The kind of quantifier (forall, exists, or choose).
    kind: QuantifierKind,
    /// The register repurposed to hold the loop index (originally r_domain).
    r_index: u8,
    /// Detected body pattern for early-exit optimization.
    body_pattern: BodyPattern,
}

/// Stack of active quantifier loops for nested quantifier support.
pub(crate) type QuantifierLoopStack = Vec<QuantifierLoopInfo>;

/// Detected body pattern for quantifier optimization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BodyPattern {
    /// No special pattern detected. Use standard single-check short-circuit.
    Simple,
    /// Body is a conjunction: `r_body = a1 /\ a2 /\ ... /\ aN`.
    /// Contains the register indices of each conjunct (the inputs to the And chain).
    /// For ForAll, we can short-circuit on the first false conjunct.
    Conjunction(Vec<u8>),
    /// Body is a disjunction: `r_body = a1 \/ a2 \/ ... \/ aN`.
    /// Contains the register indices of each disjunct.
    /// For Exists, we can short-circuit on the first true disjunct.
    Disjunction(Vec<u8>),
}

/// Analyze the instruction stream between a quantifier Begin (exclusive) and
/// Next (exclusive) to detect conjunction/disjunction patterns.
///
/// Looks for And/Or chains feeding into `r_body`. Only detects simple patterns
/// where the And/Or chain is a linear sequence with no other consumers.
///
/// # Arguments
/// * `instructions` - Full instruction stream
/// * `body_start_pc` - PC of the first body instruction (Begin + 1)
/// * `next_pc` - PC of the *Next opcode
/// * `r_body` - The register read by *Next as the body result
/// * `kind` - Forall or Exists (determines which pattern to look for)
pub(crate) fn analyze_quantifier_body(
    instructions: &[Opcode],
    body_start_pc: usize,
    next_pc: usize,
    r_body: u8,
    kind: QuantifierKind,
) -> BodyPattern {
    if next_pc <= body_start_pc || next_pc > instructions.len() {
        return BodyPattern::Simple;
    }

    let body = &instructions[body_start_pc..next_pc];

    match kind {
        QuantifierKind::Forall => detect_conjunction(body, r_body),
        QuantifierKind::Exists => detect_disjunction(body, r_body),
        QuantifierKind::Choose => BodyPattern::Simple,
    }
}

/// Detect a conjunction pattern: `r_body = a /\ b /\ c /\ ...`
///
/// Traces backward from `r_body` through And opcodes to collect leaf registers.
/// Returns `Conjunction(leaves)` if found, `Simple` otherwise.
fn detect_conjunction(body: &[Opcode], r_body: u8) -> BodyPattern {
    let mut leaves = Vec::new();
    let mut to_expand = vec![r_body];
    let mut visited = std::collections::HashSet::new();

    // Build a map from destination register to And opcode inputs
    let mut and_map: HashMap<u8, (u8, u8)> = HashMap::new();
    for op in body {
        if let Opcode::And { rd, r1, r2 } = *op {
            and_map.insert(rd, (r1, r2));
        }
    }

    // Need at least one And to detect a conjunction
    if and_map.is_empty() {
        return BodyPattern::Simple;
    }

    while let Some(reg) = to_expand.pop() {
        if !visited.insert(reg) {
            continue;
        }
        if let Some(&(r1, r2)) = and_map.get(&reg) {
            to_expand.push(r1);
            to_expand.push(r2);
        } else {
            leaves.push(reg);
        }
    }

    if leaves.len() >= 2 {
        // Sort for deterministic ordering
        leaves.sort_unstable();
        BodyPattern::Conjunction(leaves)
    } else {
        BodyPattern::Simple
    }
}

/// Detect a disjunction pattern: `r_body = a \/ b \/ c \/ ...`
///
/// Traces backward from `r_body` through Or opcodes to collect leaf registers.
/// Returns `Disjunction(leaves)` if found, `Simple` otherwise.
fn detect_disjunction(body: &[Opcode], r_body: u8) -> BodyPattern {
    let mut leaves = Vec::new();
    let mut to_expand = vec![r_body];
    let mut visited = std::collections::HashSet::new();

    let mut or_map: HashMap<u8, (u8, u8)> = HashMap::new();
    for op in body {
        if let Opcode::Or { rd, r1, r2 } = *op {
            or_map.insert(rd, (r1, r2));
        }
    }

    if or_map.is_empty() {
        return BodyPattern::Simple;
    }

    while let Some(reg) = to_expand.pop() {
        if !visited.insert(reg) {
            continue;
        }
        if let Some(&(r1, r2)) = or_map.get(&reg) {
            to_expand.push(r1);
            to_expand.push(r2);
        } else {
            leaves.push(reg);
        }
    }

    if leaves.len() >= 2 {
        leaves.sort_unstable();
        BodyPattern::Disjunction(leaves)
    } else {
        BodyPattern::Simple
    }
}

/// Find the matching Next opcode for a Begin at `begin_pc` and analyze the body.
///
/// Scans forward from `begin_pc + 1` to find the first ForallNext/ExistsNext/ChooseNext
/// that jumps back to the body start. Extracts `r_body` and runs body pattern analysis.
fn find_and_analyze_body(
    instructions: &[Opcode],
    begin_pc: usize,
    kind: QuantifierKind,
) -> BodyPattern {
    let body_start = begin_pc + 1;
    // Scan forward for the matching Next opcode
    for (offset, op) in instructions[body_start..].iter().enumerate() {
        let next_pc = body_start + offset;
        let r_body = match *op {
            Opcode::ForallNext { r_body, .. } if kind == QuantifierKind::Forall => r_body,
            Opcode::ExistsNext { r_body, .. } if kind == QuantifierKind::Exists => r_body,
            Opcode::ChooseNext { r_body, .. } if kind == QuantifierKind::Choose => r_body,
            // If we hit another Begin, we've entered a nested quantifier — skip it
            Opcode::ForallBegin { .. }
            | Opcode::ExistsBegin { .. }
            | Opcode::ChooseBegin { .. } => continue,
            _ => continue,
        };
        return analyze_quantifier_body(instructions, body_start, next_pc, r_body, kind);
    }
    BodyPattern::Simple
}

/// Collect additional jump targets introduced by quantifier opcodes.
///
/// Quantifier loops need blocks at:
/// - PC+1 after `*Begin` (loop body start, back-edge target from `*Next`)
/// - `loop_end` target of `*Begin` (exit point)
/// - PC+1 after `*Next` (post-loop continuation)
pub(crate) fn collect_quantifier_targets(instructions: &[Opcode], targets: &mut BTreeSet<usize>) {
    for (pc, op) in instructions.iter().enumerate() {
        match *op {
            Opcode::ForallBegin { loop_end, .. }
            | Opcode::ExistsBegin { loop_end, .. }
            | Opcode::ChooseBegin { loop_end, .. } => {
                targets.insert(pc + 1);
                let end_pc = ((pc as i64) + (loop_end as i64)) as usize;
                targets.insert(end_pc);
            }
            Opcode::ForallNext { loop_begin, .. }
            | Opcode::ExistsNext { loop_begin, .. }
            | Opcode::ChooseNext { loop_begin, .. } => {
                let body_pc = ((pc as i64) + (loop_begin as i64)) as usize;
                targets.insert(body_pc);
                targets.insert(pc + 1);
            }
            _ => {}
        }
    }
}

/// Lower a `ForallBegin` or `ExistsBegin` opcode.
///
/// Terminates the current block by jumping to either the exit block
/// (empty domain) or the body block (non-empty domain, first element loaded).
///
/// Supports two domain sources:
/// 1. Pre-materialized array via `QuantifierDomains` (existing path)
/// 2. Range-based iteration via `RangeTracker` (new: eliminates array allocation)
///
/// When the domain register was produced by `LoadVar` (a state-loaded compound
/// set), the domain cannot be materialized at JIT compile time. In this case,
/// emits `FallbackNeeded`/`PartialPass` and returns `Ok(true)` so the caller
/// marks subsequent instructions as dead code. A dummy loop stack entry is
/// pushed to prevent panics if the (unreachable) `*Next` opcode is lowered.
///
/// Returns `true` if the opcode was handled.
pub(crate) fn lower_quantifier_begin(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    pc: usize,
    regs: &mut RegMap,
    block_map: &[Option<Block>],
    domains: &QuantifierDomains,
    loop_stack: &mut QuantifierLoopStack,
    out_ptr: cranelift_codegen::ir::Value,
    instructions: &[Opcode],
    conjuncts_passed: u32,
    compound_tracker: Option<&super::func_record_ops::CompoundRegTracker>,
) -> Result<bool, JitError> {
    let (rd, r_binding, r_domain, loop_end, kind) = match *op {
        Opcode::ForallBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => (rd, r_binding, r_domain, loop_end, QuantifierKind::Forall),
        Opcode::ExistsBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => (rd, r_binding, r_domain, loop_end, QuantifierKind::Exists),
        Opcode::ChooseBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => (rd, r_binding, r_domain, loop_end, QuantifierKind::Choose),
        _ => return Ok(false),
    };

    // Analyze the body pattern between Begin and the matching Next for
    // conjunction/disjunction early-exit optimization.
    let body_pattern = find_and_analyze_body(instructions, pc, kind);

    let exit_pc = ((pc as i64) + (loop_end as i64)) as usize;
    let exit_block = block_map[exit_pc].ok_or_else(|| {
        JitError::CompileError(format!("quantifier exit target PC {exit_pc} has no block"))
    })?;
    let body_block = block_map[pc + 1].ok_or_else(|| {
        JitError::CompileError(format!(
            "quantifier body block at PC {} has no block",
            pc + 1
        ))
    })?;

    // Check if the domain register was produced by a Range opcode.
    // If so, use native range-based iteration instead of pre-materialized array.
    let range_info = RANGE_TRACKER.with(|rt| rt.borrow().get(&r_domain).copied());
    if let Some((r_lo, r_hi)) = range_info {
        return lower_range_quantifier_begin(
            builder,
            regs,
            loop_stack,
            out_ptr,
            rd,
            r_binding,
            r_domain,
            r_lo,
            r_hi,
            kind,
            exit_block,
            body_block,
            body_pattern,
        );
    }

    let elements = match domains.get(&r_domain) {
        Some(elems) => elems,
        None => {
            // Try compound-tracked set: the domain register holds a pointer
            // to a serialized set buffer (from SetDiff, LoadConst Interval, etc.)
            if let Some(ct) = compound_tracker {
                if let Some(info) = ct.get(r_domain) {
                    if info.is_direct_ptr {
                        if let crate::compound_layout::CompoundLayout::Set {
                            ref element_layout,
                            ..
                        } = info.layout
                        {
                            if element_layout.is_scalar() {
                                return lower_compound_set_quantifier_begin(
                                    builder,
                                    regs,
                                    loop_stack,
                                    out_ptr,
                                    rd,
                                    r_binding,
                                    r_domain,
                                    kind,
                                    exit_block,
                                    body_block,
                                    body_pattern,
                                );
                            }
                        }
                    }
                }
            }

            // Domain register was not pre-materialized and not compound-tracked.
            if std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() == Ok("1") {
                let start = pc.saturating_sub(5);
                let end = (pc + 3).min(instructions.len());
                eprintln!("[jit-debug] quantifier at PC {pc}: r_domain={r_domain}, no domain — emitting fallback");
                eprintln!(
                    "[jit-debug] domains map keys: {:?}",
                    domains.keys().collect::<Vec<_>>()
                );
                for i in start..end {
                    eprintln!("[jit-debug]   PC {i}: {:?}", instructions[i]);
                }
            }

            // Emit FallbackNeeded/PartialPass + return
            super::func_record_ops::emit_fallback_and_return(builder, out_ptr, conjuncts_passed);

            // Push a dummy loop stack entry so that the (unreachable) *Next
            // opcode doesn't panic when it tries to pop.
            loop_stack.push(QuantifierLoopInfo {
                domain: DomainSource::Array {
                    base_ptr_addr: 0,
                    count: 0,
                },
                kind,
                r_index: r_domain,
                body_pattern: body_pattern.clone(),
            });
            return Ok(true);
        }
    };

    let count = elements.len();

    if count == 0 {
        if kind == QuantifierKind::Choose {
            emit_runtime_error(builder, out_ptr);
        } else {
            let default_val = if kind == QuantifierKind::Forall {
                1i64
            } else {
                0i64
            };
            let result = builder.ins().iconst(types::I64, default_val);
            regs.set(rd, result);
            let incoming = regs.values().to_vec();
            builder.ins().jump(exit_block, &incoming);
        }

        loop_stack.push(QuantifierLoopInfo {
            domain: DomainSource::Array {
                base_ptr_addr: 0,
                count: 0,
            },
            kind,
            r_index: r_domain,
            body_pattern: body_pattern.clone(),
        });
        return Ok(true);
    }

    // Leak domain array and embed pointer
    let domain_array: Box<[i64]> = elements.to_vec().into_boxed_slice();
    let base_addr = Box::into_raw(domain_array) as *const i64 as i64;
    LEAKED_DOMAIN_ALLOCS.with(|allocs| {
        let layout = Layout::array::<i64>(count).expect("valid layout");
        allocs.borrow_mut().push((base_addr as *mut u8, layout));
    });

    // Initialize registers:
    // r_domain = 0  (repurposed as loop index)
    // r_binding = array[0]  (first element)
    // rd = default value (forall=1, exists/choose=0)
    let zero_idx = builder.ins().iconst(types::I64, 0);
    regs.set(r_domain, zero_idx);

    let base_ptr = builder.ins().iconst(types::I64, base_addr);
    let first_elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), base_ptr, 0);
    regs.set(r_binding, first_elem);

    let default_val = if kind == QuantifierKind::Forall {
        1i64
    } else {
        0i64
    };
    let rd_val = builder.ins().iconst(types::I64, default_val);
    regs.set(rd, rd_val);

    loop_stack.push(QuantifierLoopInfo {
        domain: DomainSource::Array {
            base_ptr_addr: base_addr,
            count,
        },
        kind,
        r_index: r_domain,
        body_pattern,
    });

    let incoming = regs.values().to_vec();
    builder.ins().jump(body_block, &incoming);

    Ok(true)
}

/// Lower the Begin for a range-based quantifier (domain from Range opcode).
///
/// Instead of materializing a domain array, iterates `r_binding` from lo to hi
/// (inclusive, matching TLA+ `lo..hi` semantics) using direct register arithmetic.
///
/// # Generated block structure (Forall over Range)
///
/// ```text
/// [current block — ForallBegin]:
///   if lo > hi: rd=1 (empty range), jump to exit_block
///   else: r_domain=lo, r_binding=lo, rd=1, jump to body_block
/// ```
///
/// The loop-back in ForallNext increments r_binding directly and checks `> hi`.
#[allow(clippy::too_many_arguments)]
fn lower_range_quantifier_begin(
    builder: &mut FunctionBuilder,
    regs: &mut RegMap,
    loop_stack: &mut QuantifierLoopStack,
    out_ptr: cranelift_codegen::ir::Value,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
    r_lo: u8,
    r_hi: u8,
    kind: QuantifierKind,
    exit_block: Block,
    body_block: Block,
    body_pattern: BodyPattern,
) -> Result<bool, JitError> {
    let lo_val = regs.get(r_lo);
    let hi_val = regs.get(r_hi);

    // Check if range is empty: lo > hi
    let empty = builder.ins().icmp(IntCC::SignedGreaterThan, lo_val, hi_val);

    let non_empty_block = builder.create_block();

    if kind == QuantifierKind::Choose {
        // CHOOSE over empty range: RuntimeError
        let error_block = builder.create_block();
        builder
            .ins()
            .brif(empty, error_block, &[], non_empty_block, &[]);
        builder.switch_to_block(error_block);
        builder.seal_block(error_block);
        emit_runtime_error(builder, out_ptr);
    } else {
        let empty_exit_block = builder.create_block();
        builder
            .ins()
            .brif(empty, empty_exit_block, &[], non_empty_block, &[]);
        builder.switch_to_block(empty_exit_block);
        builder.seal_block(empty_exit_block);
        let default_val = if kind == QuantifierKind::Forall {
            1i64
        } else {
            0i64
        };
        let result = builder.ins().iconst(types::I64, default_val);
        regs.set(rd, result);
        let incoming = regs.values().to_vec();
        builder.ins().jump(exit_block, &incoming);
    }

    // Non-empty block: initialize loop
    builder.switch_to_block(non_empty_block);
    builder.seal_block(non_empty_block);

    // For range mode, r_domain holds the current value (starts at lo)
    // r_binding = lo (first element)
    regs.set(r_domain, lo_val);
    regs.set(r_binding, lo_val);

    let default_val = if kind == QuantifierKind::Forall {
        1i64
    } else {
        0i64
    };
    let rd_val = builder.ins().iconst(types::I64, default_val);
    regs.set(rd, rd_val);

    loop_stack.push(QuantifierLoopInfo {
        domain: DomainSource::Range { r_lo, r_hi },
        kind,
        r_index: r_domain,
        body_pattern,
    });

    let incoming = regs.values().to_vec();
    builder.ins().jump(body_block, &incoming);

    Ok(true)
}

/// Lower a quantifier begin whose domain is a compound-tracked set buffer.
///
/// The buffer format is: [TAG_SET, count, TAG_INT, elem0, TAG_INT, elem1, ...]
/// Each element value is at byte offset `(2 + i*2 + 1) * 8` from the base pointer.
///
/// Uses an index-based loop: r_domain holds the loop index (0..count-1),
/// r_binding holds the current element value.
#[allow(clippy::too_many_arguments)]
fn lower_compound_set_quantifier_begin(
    builder: &mut FunctionBuilder,
    regs: &mut RegMap,
    loop_stack: &mut QuantifierLoopStack,
    out_ptr: cranelift_codegen::ir::Value,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
    kind: QuantifierKind,
    exit_block: Block,
    body_block: Block,
    body_pattern: BodyPattern,
) -> Result<bool, JitError> {
    // r_domain register currently holds the base pointer to the compound set buffer
    let base_ptr = regs.get(r_domain);

    // Save base pointer to a stack slot so the advance step can reload it
    // (r_domain will be repurposed as the loop index)
    use cranelift_codegen::ir::StackSlotData;
    let base_ptr_slot = builder.create_sized_stack_slot(StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        8, // one i64
        8,
    ));
    let ptr_type = types::I64; // pointers are i64 on 64-bit
    builder.ins().stack_store(base_ptr, base_ptr_slot, 0);

    // Load the count from buffer[1] (offset 8 bytes)
    let count_val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), base_ptr, 8);

    // Check if empty: count == 0
    let zero = builder.ins().iconst(types::I64, 0);
    let is_empty = builder.ins().icmp(IntCC::Equal, count_val, zero);

    let non_empty_block = builder.create_block();

    if kind == QuantifierKind::Choose {
        let error_block = builder.create_block();
        builder
            .ins()
            .brif(is_empty, error_block, &[], non_empty_block, &[]);
        builder.switch_to_block(error_block);
        builder.seal_block(error_block);
        emit_runtime_error(builder, out_ptr);
    } else {
        let empty_exit_block = builder.create_block();
        builder
            .ins()
            .brif(is_empty, empty_exit_block, &[], non_empty_block, &[]);
        builder.switch_to_block(empty_exit_block);
        builder.seal_block(empty_exit_block);
        let default_val = if kind == QuantifierKind::Forall {
            1i64
        } else {
            0i64
        };
        let result = builder.ins().iconst(types::I64, default_val);
        regs.set(rd, result);
        let incoming = regs.values().to_vec();
        builder.ins().jump(exit_block, &incoming);
    }

    builder.switch_to_block(non_empty_block);
    builder.seal_block(non_empty_block);

    // Load first element: value at offset (2 + 0*2 + 1) * 8 = 24 bytes
    let first_elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), base_ptr, 24);

    // r_domain repurposed as loop index (starts at 0)
    regs.set(r_domain, zero);
    // r_binding = first element value
    regs.set(r_binding, first_elem);

    let default_val = if kind == QuantifierKind::Forall {
        1i64
    } else {
        0i64
    };
    let rd_val = builder.ins().iconst(types::I64, default_val);
    regs.set(rd, rd_val);

    let _ = ptr_type; // used for clarity

    loop_stack.push(QuantifierLoopInfo {
        domain: DomainSource::CompoundSet { base_ptr_slot },
        kind,
        r_index: r_domain,
        body_pattern,
    });

    let incoming = regs.values().to_vec();
    builder.ins().jump(body_block, &incoming);

    Ok(true)
}

/// Emit a RuntimeError (TypeMismatch) to out_ptr and return.
/// Used for CHOOSE with empty domain or no matching element.
fn emit_runtime_error(builder: &mut FunctionBuilder, out_ptr: cranelift_codegen::ir::Value) {
    use crate::abi::{JitCallOut, JitRuntimeErrorKind, JitStatus};
    let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
    let err_kind_offset = std::mem::offset_of!(JitCallOut, err_kind) as i32;
    let status = builder
        .ins()
        .iconst(types::I8, JitStatus::RuntimeError as i64);
    let err_kind = builder
        .ins()
        .iconst(types::I8, JitRuntimeErrorKind::TypeMismatch as i64);
    builder
        .ins()
        .store(MemFlags::trusted(), status, out_ptr, status_offset);
    builder
        .ins()
        .store(MemFlags::trusted(), err_kind, out_ptr, err_kind_offset);
    builder.ins().return_(&[]);
}

/// Emit a chain of conditional branches for multi-leaf short-circuit checking.
///
/// For `short_on_true == false` (Forall conjunction): each leaf is checked;
/// if the leaf is false (== 0), branch to `short_circuit_block`. If all leaves
/// are true, fall through to `continue_block`.
///
/// For `short_on_true == true` (Exists disjunction): each leaf is checked;
/// if the leaf is true (!= 0), branch to `short_circuit_block`. If all leaves
/// are false, fall through to `continue_block`.
///
/// Generates a chain of blocks: one per leaf (except the last, which branches
/// directly to continue_block or short_circuit_block).
fn emit_multi_leaf_short_circuit(
    builder: &mut FunctionBuilder,
    regs: &RegMap,
    leaves: &[u8],
    short_circuit_block: Block,
    continue_block: Block,
    short_on_true: bool,
) {
    debug_assert!(leaves.len() >= 2, "multi-leaf requires >= 2 leaves");

    for (i, &leaf_reg) in leaves.iter().enumerate() {
        let leaf_val = regs.get(leaf_reg);
        let leaf_bool = builder.ins().icmp_imm(IntCC::NotEqual, leaf_val, 0);

        let is_last = i == leaves.len() - 1;
        let next_block = if is_last {
            continue_block
        } else {
            builder.create_block()
        };

        if short_on_true {
            // Exists disjunction: true -> short-circuit, false -> check next
            builder
                .ins()
                .brif(leaf_bool, short_circuit_block, &[], next_block, &[]);
        } else {
            // Forall conjunction: false -> short-circuit, true -> check next
            builder
                .ins()
                .brif(leaf_bool, next_block, &[], short_circuit_block, &[]);
        }

        if !is_last {
            builder.switch_to_block(next_block);
            // Seal after predecessor's brif has been emitted — each intermediate
            // block has exactly one predecessor (the previous block in the chain).
            builder.seal_block(next_block);
        }
    }
}

/// Lower a `ForallNext` or `ExistsNext` opcode.
///
/// Implements short-circuit check, index increment, bounds check, and
/// loop back-edge. Terminates the current block (all paths jump somewhere).
///
/// Returns `true` if the opcode was handled.
pub(crate) fn lower_quantifier_next(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    pc: usize,
    regs: &mut RegMap,
    block_map: &[Option<Block>],
    loop_stack: &mut QuantifierLoopStack,
    out_ptr: cranelift_codegen::ir::Value,
) -> Result<bool, JitError> {
    let (rd, _r_binding, r_body, loop_begin) = match *op {
        Opcode::ForallNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => (rd, r_binding, r_body, loop_begin),
        Opcode::ExistsNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => (rd, r_binding, r_body, loop_begin),
        Opcode::ChooseNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => (rd, r_binding, r_body, loop_begin),
        _ => return Ok(false),
    };

    let info = match loop_stack.pop() {
        Some(info) => info,
        None => {
            // The matching ForallBegin/ExistsBegin was in dead code (e.g., due to
            // a FallbackEmitted from a SetDiff that produced the domain), so no
            // entry was pushed onto the loop stack. The body block was still entered
            // because collect_quantifier_targets creates a block at Begin+1, and
            // the block-switching code clears in_dead_code unconditionally.
            //
            // Gracefully emit FallbackNeeded so the caller re-evaluates via the
            // interpreter. This fixes JIT compilation for actions like Enter(p)
            // in LamportMutex where the quantifier domain is `Proc \ {p}` (SetDiff).
            super::func_record_ops::emit_fallback_and_return(builder, out_ptr, 0);
            return Ok(true);
        }
    };

    let exit_pc = pc + 1;
    let exit_block = block_map[exit_pc].ok_or_else(|| {
        JitError::CompileError(format!(
            "quantifier exit block at PC {exit_pc} has no block"
        ))
    })?;

    // Empty array domain: Begin already jumped to exit.
    if let DomainSource::Array { count: 0, .. } = info.domain {
        let incoming = regs.values().to_vec();
        builder.ins().jump(exit_block, &incoming);
        return Ok(true);
    }

    let body_pc = ((pc as i64) + (loop_begin as i64)) as usize;
    let body_block = block_map[body_pc].ok_or_else(|| {
        JitError::CompileError(format!(
            "quantifier body block at PC {body_pc} has no block"
        ))
    })?;

    // Step 1: Check body result for short-circuit.
    //
    // With body pattern optimization:
    // - Forall + Conjunction(leaves): check each conjunct; short-circuit on first false
    // - Exists + Disjunction(leaves): check each disjunct; short-circuit on first true
    // - Simple / Choose / mismatched pattern: check r_body as a single value

    let short_circuit_block = builder.create_block();
    let advance_block = builder.create_block();

    match (&info.body_pattern, info.kind) {
        (BodyPattern::Conjunction(leaves), QuantifierKind::Forall) if leaves.len() >= 2 => {
            // Forall conjunction early-exit: check each conjunct leaf.
            // If any leaf is false (== 0), jump to short_circuit_block.
            // Chain: check leaf[0] -> check leaf[1] -> ... -> advance_block
            emit_multi_leaf_short_circuit(
                builder,
                regs,
                leaves,
                short_circuit_block,
                advance_block,
                false,
            );
        }
        (BodyPattern::Disjunction(leaves), QuantifierKind::Exists) if leaves.len() >= 2 => {
            // Exists disjunction early-exit: check each disjunct leaf.
            // If any leaf is true (!= 0), jump to short_circuit_block.
            emit_multi_leaf_short_circuit(
                builder,
                regs,
                leaves,
                short_circuit_block,
                advance_block,
                true,
            );
        }
        _ => {
            // Simple pattern: check r_body as a single boolean
            let body_val = regs.get(r_body);
            let body_bool = builder.ins().icmp_imm(IntCC::NotEqual, body_val, 0);
            match info.kind {
                QuantifierKind::Forall => {
                    builder
                        .ins()
                        .brif(body_bool, advance_block, &[], short_circuit_block, &[]);
                }
                QuantifierKind::Exists | QuantifierKind::Choose => {
                    builder
                        .ins()
                        .brif(body_bool, short_circuit_block, &[], advance_block, &[]);
                }
            }
        }
    }

    // Short-circuit block: set early-exit result and jump to exit
    builder.switch_to_block(short_circuit_block);
    builder.seal_block(short_circuit_block);
    match info.kind {
        QuantifierKind::Forall => {
            let early_result = builder.ins().iconst(types::I64, 0);
            regs.set(rd, early_result);
        }
        QuantifierKind::Exists => {
            let early_result = builder.ins().iconst(types::I64, 1);
            regs.set(rd, early_result);
        }
        QuantifierKind::Choose => {
            let binding_val = regs.get(_r_binding);
            regs.set(rd, binding_val);
        }
    }
    let incoming_exit = regs.values().to_vec();
    builder.ins().jump(exit_block, &incoming_exit);

    // Advance block: increment index, check bounds
    builder.switch_to_block(advance_block);
    builder.seal_block(advance_block);

    match info.domain {
        DomainSource::Array {
            base_ptr_addr,
            count,
        } => {
            lower_array_advance(
                builder,
                regs,
                info.r_index,
                _r_binding,
                rd,
                info.kind,
                base_ptr_addr,
                count,
                exit_block,
                body_block,
                out_ptr,
            );
        }
        DomainSource::Range { r_lo: _, r_hi } => {
            lower_range_advance(
                builder,
                regs,
                info.r_index,
                _r_binding,
                rd,
                info.kind,
                r_hi,
                exit_block,
                body_block,
                out_ptr,
            );
        }
        DomainSource::CompoundSet { base_ptr_slot } => {
            lower_compound_set_advance(
                builder,
                regs,
                info.r_index,
                _r_binding,
                rd,
                info.kind,
                base_ptr_slot,
                exit_block,
                body_block,
                out_ptr,
            );
        }
    }

    Ok(true)
}

/// Emit the advance logic for array-based domain iteration.
#[allow(clippy::too_many_arguments)]
fn lower_array_advance(
    builder: &mut FunctionBuilder,
    regs: &mut RegMap,
    r_index: u8,
    r_binding: u8,
    rd: u8,
    kind: QuantifierKind,
    base_ptr_addr: i64,
    count: usize,
    exit_block: Block,
    body_block: Block,
    out_ptr: cranelift_codegen::ir::Value,
) {
    let current_idx = regs.get(r_index);
    let one = builder.ins().iconst(types::I64, 1);
    let next_idx = builder.ins().iadd(current_idx, one);

    let count_val = builder.ins().iconst(types::I64, count as i64);
    let at_end = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, next_idx, count_val);

    let exhausted_block = builder.create_block();
    let loop_back_block = builder.create_block();

    builder
        .ins()
        .brif(at_end, exhausted_block, &[], loop_back_block, &[]);

    // Exhausted block
    builder.switch_to_block(exhausted_block);
    builder.seal_block(exhausted_block);
    emit_exhausted(builder, regs, rd, kind, exit_block, out_ptr);

    // Loop-back block: load next element, update registers, jump to body
    builder.switch_to_block(loop_back_block);
    builder.seal_block(loop_back_block);

    regs.set(r_index, next_idx);

    let base_ptr = builder.ins().iconst(types::I64, base_ptr_addr);
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_offset = builder.ins().imul(next_idx, eight);
    let elem_addr = builder.ins().iadd(base_ptr, byte_offset);
    let next_elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);
    regs.set(r_binding, next_elem);

    let default_val = if kind == QuantifierKind::Forall {
        1i64
    } else {
        0i64
    };
    let initial_rd = builder.ins().iconst(types::I64, default_val);
    regs.set(rd, initial_rd);

    let incoming_body = regs.values().to_vec();
    builder.ins().jump(body_block, &incoming_body);
}

/// Emit the advance logic for range-based domain iteration.
///
/// Increments the current value and checks if it exceeds hi.
#[allow(clippy::too_many_arguments)]
fn lower_range_advance(
    builder: &mut FunctionBuilder,
    regs: &mut RegMap,
    r_index: u8,
    r_binding: u8,
    rd: u8,
    kind: QuantifierKind,
    r_hi: u8,
    exit_block: Block,
    body_block: Block,
    out_ptr: cranelift_codegen::ir::Value,
) {
    let current_val = regs.get(r_index);
    let one = builder.ins().iconst(types::I64, 1);
    let next_val = builder.ins().iadd(current_val, one);

    let hi_val = regs.get(r_hi);
    let at_end = builder
        .ins()
        .icmp(IntCC::SignedGreaterThan, next_val, hi_val);

    let exhausted_block = builder.create_block();
    let loop_back_block = builder.create_block();

    builder
        .ins()
        .brif(at_end, exhausted_block, &[], loop_back_block, &[]);

    // Exhausted block
    builder.switch_to_block(exhausted_block);
    builder.seal_block(exhausted_block);
    emit_exhausted(builder, regs, rd, kind, exit_block, out_ptr);

    // Loop-back block: update binding to next value
    builder.switch_to_block(loop_back_block);
    builder.seal_block(loop_back_block);

    regs.set(r_index, next_val);
    regs.set(r_binding, next_val);

    let default_val = if kind == QuantifierKind::Forall {
        1i64
    } else {
        0i64
    };
    let initial_rd = builder.ins().iconst(types::I64, default_val);
    regs.set(rd, initial_rd);

    let incoming_body = regs.values().to_vec();
    builder.ins().jump(body_block, &incoming_body);
}

/// Emit the advance logic for compound-set-based domain iteration.
///
/// The set buffer format is: [TAG_SET, count, TAG_INT, elem0, TAG_INT, elem1, ...]
/// Element `i` value is at byte offset `(2 + i*2 + 1) * 8 = (i*2 + 3) * 8` from base.
#[allow(clippy::too_many_arguments)]
fn lower_compound_set_advance(
    builder: &mut FunctionBuilder,
    regs: &mut RegMap,
    r_index: u8,
    r_binding: u8,
    rd: u8,
    kind: QuantifierKind,
    base_ptr_slot: cranelift_codegen::ir::StackSlot,
    exit_block: Block,
    body_block: Block,
    out_ptr: cranelift_codegen::ir::Value,
) {
    // Increment index
    let current_idx = regs.get(r_index);
    let one = builder.ins().iconst(types::I64, 1);
    let next_idx = builder.ins().iadd(current_idx, one);

    // Reload base pointer from stack slot
    let base_ptr = builder.ins().stack_load(types::I64, base_ptr_slot, 0);

    // Reload count from buffer[1] (offset 8)
    let count_val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), base_ptr, 8);

    // Check bounds: next_idx >= count → exhausted
    let at_end = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, next_idx, count_val);

    let exhausted_block = builder.create_block();
    let loop_back_block = builder.create_block();

    builder
        .ins()
        .brif(at_end, exhausted_block, &[], loop_back_block, &[]);

    // Exhausted block
    builder.switch_to_block(exhausted_block);
    builder.seal_block(exhausted_block);
    emit_exhausted(builder, regs, rd, kind, exit_block, out_ptr);

    // Loop-back block: load next element, update registers, jump to body
    builder.switch_to_block(loop_back_block);
    builder.seal_block(loop_back_block);

    regs.set(r_index, next_idx);

    // Element value offset: (next_idx * 2 + 3) * 8
    let two = builder.ins().iconst(types::I64, 2);
    let three = builder.ins().iconst(types::I64, 3);
    let eight = builder.ins().iconst(types::I64, 8);
    let idx_times_2 = builder.ins().imul(next_idx, two);
    let slot_idx = builder.ins().iadd(idx_times_2, three);
    let byte_offset = builder.ins().imul(slot_idx, eight);
    let elem_addr = builder.ins().iadd(base_ptr, byte_offset);
    let next_elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);
    regs.set(r_binding, next_elem);

    let default_val = if kind == QuantifierKind::Forall {
        1i64
    } else {
        0i64
    };
    let initial_rd = builder.ins().iconst(types::I64, default_val);
    regs.set(rd, initial_rd);

    let incoming_body = regs.values().to_vec();
    builder.ins().jump(body_block, &incoming_body);
}

/// Emit the exhausted-domain logic (shared between array and range modes).
fn emit_exhausted(
    builder: &mut FunctionBuilder,
    regs: &mut RegMap,
    rd: u8,
    kind: QuantifierKind,
    exit_block: Block,
    out_ptr: cranelift_codegen::ir::Value,
) {
    match kind {
        QuantifierKind::Forall => {
            let default_result = builder.ins().iconst(types::I64, 1);
            regs.set(rd, default_result);
            let incoming = regs.values().to_vec();
            builder.ins().jump(exit_block, &incoming);
        }
        QuantifierKind::Exists => {
            let default_result = builder.ins().iconst(types::I64, 0);
            regs.set(rd, default_result);
            let incoming = regs.values().to_vec();
            builder.ins().jump(exit_block, &incoming);
        }
        QuantifierKind::Choose => {
            emit_runtime_error(builder, out_ptr);
        }
    }
}
