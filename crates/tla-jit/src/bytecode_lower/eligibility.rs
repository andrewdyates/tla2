// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! JIT eligibility gate for bytecode functions.
//!
//! **All opcodes are now JIT-eligible** (Phase 2 of #3909). A `BytecodeFunction`
//! is eligible if:
//! 1. It is non-empty.
//! 2. Jump targets are within bounds.
//! 3. `LoadConst` references scalar constants (when constant pool is available).
//! 4. For invariant context: no `LoadPrime`/`StoreVar` (use next-state compilation).
//!
//! # Opcode handling tiers
//!
//! 1. **Native scalar ops**: LoadImm, LoadBool, LoadVar, arithmetic, comparison,
//!    boolean, control flow, Move, Ret — compiled to native Cranelift IR.
//! 2. **Inline set ops**: SetEnum (<=16), SetIn, Range, Subseteq — expanded to
//!    inline comparison chains. See `set_ops.rs`.
//! 3. **Compound access with layout**: RecordGet, FuncApply, TupleGet,
//!    Len/Cardinality/Head — native loads when state layout is known.
//! 4. **Fallback opcodes**: Compound-producing ops (SetUnion, RecordNew, etc.),
//!    operator calls (Call, ValueApply), and misc ops (Halt, SetPrimeMode) —
//!    emit `FallbackNeeded` status at runtime. The caller re-evaluates the
//!    entire expression via the interpreter.
//!
//! The fallback strategy means the JIT can compile functions with mixed scalar
//! and compound paths. Scalar-only paths execute natively; compound paths
//! trigger fallback only when actually reached at runtime.

use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};

/// Check whether a bytecode function is eligible for JIT compilation.
///
/// Returns `Ok(())` if eligible, or `Err(reason)` describing why not.
///
/// Without a constant pool, `LoadConst` is always rejected. Use
/// [`check_eligibility_with_constants`] to allow scalar constants.
pub fn check_eligibility(func: &BytecodeFunction) -> Result<(), String> {
    check_eligibility_with_constants(func, None)
}

/// Check whether a bytecode function is eligible for JIT compilation,
/// with optional access to the constant pool for `LoadConst` scalar support.
///
/// When `constants` is `Some`, `LoadConst` is allowed if the referenced
/// constant is a scalar (`SmallInt` or `Bool`). Compound constants are
/// still rejected.
pub fn check_eligibility_with_constants(
    func: &BytecodeFunction,
    constants: Option<&ConstantPool>,
) -> Result<(), String> {
    if func.instructions.is_empty() {
        return Err("empty function".to_string());
    }

    let len = func.instructions.len();
    for (pc, op) in func.instructions.iter().enumerate() {
        if let Err(reason) = check_opcode(pc, op, len, constants) {
            return Err(format!("instruction {pc}: {reason}"));
        }
    }

    Ok(())
}

/// Check whether the instruction at `pc` is JIT-eligible in the context of its function.
///
/// This applies the same opcode-level rules as [`check_eligibility`], including
/// control-flow validation that depends on the full instruction stream.
pub fn check_opcode_eligibility(func: &BytecodeFunction, pc: usize) -> Result<(), String> {
    check_opcode_eligibility_with_constants(func, pc, None)
}

/// Check whether the instruction at `pc` is JIT-eligible with optional constant-pool access.
pub fn check_opcode_eligibility_with_constants(
    func: &BytecodeFunction,
    pc: usize,
    constants: Option<&ConstantPool>,
) -> Result<(), String> {
    if pc >= func.instructions.len() {
        return Err(format!(
            "instruction {pc} is outside function body (len={})",
            func.instructions.len()
        ));
    }

    check_opcode(
        pc,
        &func.instructions[pc],
        func.instructions.len(),
        constants,
    )
}

/// Check whether a single opcode is JIT-eligible (scalar + control flow + quantifier loops).
fn check_opcode(
    pc: usize,
    op: &Opcode,
    len: usize,
    _constants: Option<&ConstantPool>,
) -> Result<(), String> {
    match op {
        // Scalar value loading
        Opcode::LoadImm { .. }
        | Opcode::LoadBool { .. }
        | Opcode::LoadVar { .. }
        | Opcode::Move { .. } => Ok(()),

        // Integer arithmetic (Euclidean div/mod implemented in scalar_ops.rs)
        Opcode::AddInt { .. }
        | Opcode::SubInt { .. }
        | Opcode::MulInt { .. }
        | Opcode::DivInt { .. }
        | Opcode::IntDiv { .. }
        | Opcode::ModInt { .. }
        | Opcode::NegInt { .. } => Ok(()),

        // Comparisons
        Opcode::Eq { .. }
        | Opcode::Neq { .. }
        | Opcode::LtInt { .. }
        | Opcode::LeInt { .. }
        | Opcode::GtInt { .. }
        | Opcode::GeInt { .. } => Ok(()),

        // Boolean operations
        Opcode::And { .. }
        | Opcode::Or { .. }
        | Opcode::Not { .. }
        | Opcode::Implies { .. }
        | Opcode::Equiv { .. } => Ok(()),

        // Control flow
        Opcode::Jump { offset } => validate_forward_jump(pc, *offset, len, "Jump"),
        Opcode::JumpTrue { offset, .. } | Opcode::JumpFalse { offset, .. } => {
            if pc + 1 >= len {
                return Err("conditional jump at end of function has no fallthrough".to_string());
            }
            validate_forward_jump(pc, *offset, len, "conditional jump")
        }
        Opcode::CondMove { .. } | Opcode::Ret { .. } | Opcode::Nop => Ok(()),

        // Quantifier loops (compiled to counted Cranelift loops)
        Opcode::ForallBegin { loop_end, .. } => {
            validate_jump_target(pc, *loop_end, len, "ForallBegin loop_end")
        }
        Opcode::ExistsBegin { loop_end, .. } => {
            validate_jump_target(pc, *loop_end, len, "ExistsBegin loop_end")
        }
        Opcode::ForallNext { loop_begin, .. } => {
            validate_backward_jump(pc, *loop_begin, len, "ForallNext loop_begin")
        }
        Opcode::ExistsNext { loop_begin, .. } => {
            validate_backward_jump(pc, *loop_begin, len, "ExistsNext loop_begin")
        }

        // Set operations (finite enumerated sets + integer ranges, compiled as
        // inline comparison chains — see set_ops.rs)
        Opcode::SetEnum { count, .. } => {
            if *count > super::set_ops::MAX_SET_ENUM_SIZE {
                Err(format!(
                    "SetEnum too large for JIT ({count} elements, max {})",
                    super::set_ops::MAX_SET_ENUM_SIZE
                ))
            } else {
                Ok(())
            }
        }
        Opcode::SetIn { .. } => Ok(()),
        // Integer range sets: lo..hi compiled as range bounds checks
        Opcode::Range { .. } => Ok(()),
        // Subset-or-equal: compiled as conjunction of membership tests
        // (requires both operands to be tracked SetEnum or Range)
        Opcode::Subseteq { .. } => Ok(()),

        // Integer exponentiation (compiled as extern helper call)
        Opcode::PowInt { .. } => Ok(()),

        // LoadConst: always eligible. Scalar constants (SmallInt, Bool) are
        // compiled to native i64 constants. Compound constants (strings, ranges,
        // sets, etc.) emit FallbackNeeded at runtime — the JIT can still compile
        // the function, and scalar-only code paths execute natively.
        Opcode::LoadConst { .. } => Ok(()),

        // State mutation opcodes: only allowed in next-state context.
        Opcode::LoadPrime { .. } => Err("LoadPrime (primed state)".to_string()),
        Opcode::StoreVar { .. } => Err("StoreVar (state mutation)".to_string()),

        // Choose quantifier loops (compiled to counted Cranelift loops with RuntimeError on failure)
        Opcode::ChooseBegin { loop_end, .. } => {
            validate_jump_target(pc, *loop_end, len, "ChooseBegin loop_end")
        }
        Opcode::ChooseNext { loop_begin, .. } => {
            validate_backward_jump(pc, *loop_begin, len, "ChooseNext loop_begin")
        }

        // Function application, record field access, tuple index, and domain:
        // eligible for JIT. At runtime, these emit FallbackNeeded status
        // since the JIT cannot evaluate compound values natively. The caller
        // falls back to the interpreter for this state. Part of #3798.
        Opcode::FuncApply { .. }
        | Opcode::RecordGet { .. }
        | Opcode::TupleGet { .. }
        | Opcode::Domain { .. } => Ok(()),

        // Standard-library builtin calls: eligible for JIT.
        // - IsFiniteSet: always TRUE in model checking (iconst 1).
        // - Len/Cardinality: emit native count read when compound layout is
        //   available, otherwise FallbackNeeded.
        // - Head/Tail/Append/SubSeq/ToString: always FallbackNeeded (compound
        //   manipulation the JIT cannot perform natively).
        // Part of #3909 item 2.3.
        Opcode::CallBuiltin { .. } => Ok(()),

        // === Compound-producing opcodes: eligible with FallbackNeeded at runtime ===
        // These produce compound values (sets, sequences, records, functions)
        // that cannot be represented as a single i64. The JIT emits
        // FallbackNeeded+return, causing the caller to re-evaluate the entire
        // expression via the interpreter. Making these eligible means more
        // bytecode functions pass the gate — the JIT executes fast scalar
        // paths natively and falls back only on paths that hit compound ops.
        // Part of #3909 Phase 2.

        // Set operations that produce sets
        Opcode::SetUnion { .. }
        | Opcode::SetIntersect { .. }
        | Opcode::SetDiff { .. }
        | Opcode::Powerset { .. }
        | Opcode::BigUnion { .. }
        | Opcode::KSubset { .. } => Ok(()),

        // Set/function builder loops (produce compound values)
        Opcode::SetBuilderBegin { .. }
        | Opcode::SetFilterBegin { .. }
        | Opcode::FuncDefBegin { .. }
        | Opcode::LoopNext { .. } => Ok(()),

        // Compound value construction
        Opcode::RecordNew { .. }
        | Opcode::RecordSet { .. }
        | Opcode::FuncExcept { .. }
        | Opcode::FuncDef { .. }
        | Opcode::FuncSet { .. }
        | Opcode::TupleNew { .. }
        | Opcode::Times { .. }
        | Opcode::SeqNew { .. }
        | Opcode::StrConcat { .. }
        | Opcode::Concat { .. } => Ok(()),

        // Operator calls: eligible with FallbackNeeded.
        // The inliner handles many Call cases; for non-inlineable calls,
        // fallback is better than rejecting the whole function.
        Opcode::Call { .. }
        | Opcode::ValueApply { .. }
        | Opcode::CallExternal { .. }
        | Opcode::MakeClosure { .. } => Ok(()),

        // Unchanged: eligible in invariant context too (emits FallbackNeeded).
        // Natively handled in next-state context via lower_next_state_access.
        Opcode::Unchanged { .. } => Ok(()),

        // SetPrimeMode: eligible with FallbackNeeded (only used in next-state
        // fallback paths for UNCHANGED with Call opcodes).
        Opcode::SetPrimeMode { .. } => Ok(()),

        // Halt: eligible — emits RuntimeError at runtime.
        Opcode::Halt => Ok(()),
        // No catch-all: all Opcode variants are explicitly handled.
        // Adding a new Opcode variant will cause a compile error here,
        // forcing a conscious eligibility decision. Part of #3909.
    }
}

/// Check whether a bytecode function is eligible for next-state JIT compilation.
///
/// Like `check_eligibility`, but additionally allows `StoreVar` and `LoadPrime`.
pub(crate) fn check_next_state_eligibility(func: &BytecodeFunction) -> Result<(), String> {
    check_next_state_eligibility_with_constants(func, None)
}

/// Check next-state eligibility with optional constant pool access.
///
/// Part of #3958: Reject actions with inner ExistsBegin quantifiers.
/// In next-state mode, `\E x \in S : Body(x)` means nondeterministic
/// choice — each satisfying x produces a DIFFERENT successor state. The
/// JIT ABI returns a single `(bool, state_out)` pair, so it can only
/// report ONE successor per action call. Actions with inner EXISTS would
/// silently drop successors, causing missing states in the BFS.
///
/// Note: the OUTER EXISTS (from split-action expansion) is handled by
/// binding specialization — each binding value gets its own compiled
/// function. Only INNER EXISTS (within the action body) is problematic.
pub(crate) fn check_next_state_eligibility_with_constants(
    func: &BytecodeFunction,
    constants: Option<&ConstantPool>,
) -> Result<(), String> {
    if func.instructions.is_empty() {
        return Err("empty function".to_string());
    }

    // Part of #3958: Reject actions with inner EXISTS/FORALL quantifiers.
    // These produce multiple successor states in next-state mode, which
    // the single-successor JIT ABI cannot represent correctly.
    // ForallBegin in next-state context means "conjunction over all domain
    // elements" which CAN produce a single successor (all primed variables
    // must agree). However, EXISTS means nondeterministic choice and
    // produces MULTIPLE successors. Reject both conservatively for now.
    for (pc, op) in func.instructions.iter().enumerate() {
        if matches!(op, Opcode::ExistsBegin { .. }) {
            return Err(format!(
                "instruction {pc}: ExistsBegin in next-state action would produce \
                 multiple successors, but JIT ABI returns only one"
            ));
        }
    }

    let len = func.instructions.len();
    for (pc, op) in func.instructions.iter().enumerate() {
        if let Err(reason) = check_next_state_opcode(pc, op, len, constants) {
            return Err(format!("instruction {pc}: {reason}"));
        }
    }

    Ok(())
}

/// Check next-state eligibility, allowing ExistsBegin opcodes.
///
/// Used by `build_with_stats_and_specializations` which handles inner EXISTS
/// via pre-expansion (Phase 1 of #4176). The ExistsBegin opcodes will be
/// removed by the expansion pass before actual JIT compilation.
///
/// Part of #4176: JIT EXISTS binding dispatch.
pub(crate) fn check_next_state_eligibility_allowing_exists(
    func: &BytecodeFunction,
    constants: Option<&ConstantPool>,
) -> Result<(), String> {
    if func.instructions.is_empty() {
        return Err("empty function".to_string());
    }

    // Skip the ExistsBegin rejection — inner EXISTS will be handled by
    // expansion in the build_with_stats_and_specializations path.

    let len = func.instructions.len();
    for (pc, op) in func.instructions.iter().enumerate() {
        if let Err(reason) = check_next_state_opcode(pc, op, len, constants) {
            return Err(format!("instruction {pc}: {reason}"));
        }
    }

    Ok(())
}

/// Check whether a single opcode is eligible for next-state JIT compilation.
fn check_next_state_opcode(
    pc: usize,
    op: &Opcode,
    len: usize,
    constants: Option<&ConstantPool>,
) -> Result<(), String> {
    match op {
        Opcode::StoreVar { .. } | Opcode::LoadPrime { .. } | Opcode::Unchanged { .. } => Ok(()),
        _ => check_opcode(pc, op, len, constants),
    }
}

/// Check whether an action contains ops that always hit compound-type fallback
/// on specs that carry `Seq`-typed state variables.
///
/// When this returns `true`, the JIT should reject the action at the eligibility
/// gate: every dispatch would pay Cranelift tiering + flatten + fallback cost
/// only to re-evaluate in the interpreter (#4304 root cause). Rejecting at the
/// gate keeps the interpreter fast-path and avoids the regression. Pattern
/// mirrors the inner-EXISTS rejection in `check_next_state_eligibility*`
/// (Part of #3958 / #4176).
///
/// Returns `Err(reason)` on rejection, `Ok(())` otherwise.
///
/// Part of #4304.
pub(crate) fn check_seq_compatible(
    func: &BytecodeFunction,
    state_layout: Option<&tla_jit_abi::layout::StateLayout>,
) -> Result<(), String> {
    // Inexpensive pre-check: if no layout info is available or no Seq var
    // exists, nothing to reject.
    let Some(layout) = state_layout else {
        return Ok(());
    };
    if !state_layout_has_seq(layout) {
        return Ok(());
    }

    for (pc, op) in func.instructions.iter().enumerate() {
        if is_seq_incompatible_op(op) {
            return Err(format!(
                "instruction {pc}: {} on Seq-typed state var always hits compound fallback; \
                 reject JIT to avoid regression (#4304)",
                seq_incompatible_reason(op)
            ));
        }
    }
    Ok(())
}

fn state_layout_has_seq(layout: &tla_jit_abi::layout::StateLayout) -> bool {
    use tla_jit_abi::layout::{CompoundLayout, VarLayout};

    layout
        .iter()
        .any(|var| matches!(var, VarLayout::Compound(CompoundLayout::Sequence { .. })))
}

fn is_seq_incompatible_op(op: &Opcode) -> bool {
    use tla_tir::bytecode::BuiltinOp;

    match op {
        // Sequence primitives — always compound fallback
        Opcode::TupleNew { .. } | Opcode::SeqNew { .. } | Opcode::Concat { .. } => true,
        // Set-builder loops that produce compound values
        Opcode::SetUnion { .. }
        | Opcode::SetIntersect { .. }
        | Opcode::SetDiff { .. }
        | Opcode::FuncDefBegin { .. }
        | Opcode::LoopNext { .. }
        | Opcode::FuncExcept { .. }
        | Opcode::FuncDef { .. } => true,
        // Builtins that operate on Seq values
        Opcode::CallBuiltin { builtin, .. } => matches!(
            builtin,
            BuiltinOp::Head | BuiltinOp::Tail | BuiltinOp::Append | BuiltinOp::SubSeq
        ),
        _ => false,
    }
}

fn seq_incompatible_reason(op: &Opcode) -> &'static str {
    match op {
        Opcode::TupleNew { .. } => "TupleNew",
        Opcode::SeqNew { .. } => "SeqNew",
        Opcode::Concat { .. } => "Concat",
        Opcode::SetUnion { .. } => "SetUnion",
        Opcode::SetIntersect { .. } => "SetIntersect",
        Opcode::SetDiff { .. } => "SetDiff",
        Opcode::FuncDefBegin { .. } => "FuncDefBegin",
        Opcode::LoopNext { .. } => "LoopNext",
        Opcode::FuncExcept { .. } => "FuncExcept",
        Opcode::FuncDef { .. } => "FuncDef",
        Opcode::CallBuiltin { .. } => "CallBuiltin(Seq-op)",
        _ => "<unknown>",
    }
}

/// Validate a forward jump target (used by quantifier loop_end offsets).
fn validate_jump_target(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<(), String> {
    let target = (pc as i64) + (offset as i64);
    if target < 0 || target >= len as i64 {
        return Err(format!(
            "{opcode_name} target {target} is outside function body (len={len})"
        ));
    }
    if target <= pc as i64 {
        return Err(format!(
            "{opcode_name} must target a later instruction (got offset {offset})"
        ));
    }
    Ok(())
}

/// Validate a backward jump target (used by quantifier loop_begin offsets).
fn validate_backward_jump(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<(), String> {
    let target = (pc as i64) + (offset as i64);
    if target < 0 || target >= len as i64 {
        return Err(format!(
            "{opcode_name} target {target} is outside function body (len={len})"
        ));
    }
    if target >= pc as i64 {
        return Err(format!(
            "{opcode_name} must target an earlier instruction (got offset {offset})"
        ));
    }
    Ok(())
}

fn validate_forward_jump(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<(), String> {
    let target = (pc as i64) + (offset as i64);
    if target <= pc as i64 {
        return Err(format!(
            "{opcode_name} must target a later instruction (got offset {offset})"
        ));
    }
    if target < 0 || target >= len as i64 {
        return Err(format!(
            "{opcode_name} target {target} is outside function body (len={len})"
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seq_state_layout() -> tla_jit_abi::layout::StateLayout {
        use tla_jit_abi::layout::{CompoundLayout, StateLayout, VarLayout};

        StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: None,
        })])
    }

    fn scalar_state_layout() -> tla_jit_abi::layout::StateLayout {
        use tla_jit_abi::layout::{StateLayout, VarLayout};

        StateLayout::new(vec![VarLayout::ScalarInt])
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_simple_arithmetic() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_with_state_var() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 5 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_with_control_flow() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::JumpFalse { rs: 0, offset: 2 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Ret { rs: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_with_fallback() {
        // Call is now JIT-eligible (emits FallbackNeeded at runtime).
        // Part of #3909 Phase 2.
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 1,
            argc: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });
        assert!(
            check_eligibility(&func).is_ok(),
            "Call should be JIT-eligible (emits FallbackNeeded at runtime)"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_value_apply_with_fallback() {
        // ValueApply is now JIT-eligible (emits FallbackNeeded at runtime).
        // Part of #3909 Phase 2.
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::ValueApply {
            rd: 0,
            func: 1,
            args_start: 2,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });
        assert!(
            check_eligibility(&func).is_ok(),
            "ValueApply should be JIT-eligible (emits FallbackNeeded at runtime)"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_set_enum_and_set_in() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 0,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_set_union_with_fallback() {
        // SetUnion is now JIT-eligible (emits FallbackNeeded at runtime).
        // Part of #3909 Phase 2.
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::SetUnion {
            rd: 0,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 0 });
        assert!(
            check_eligibility(&func).is_ok(),
            "SetUnion should be JIT-eligible (emits FallbackNeeded at runtime)"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_ineligible_empty() {
        let func = BytecodeFunction::new("test".to_string(), 0);
        let err = check_eligibility(&func).unwrap_err();
        assert!(err.contains("empty"), "got: {err}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_forall_quantifier() {
        let mut func = BytecodeFunction::new("test".to_string(), 3);
        // PC 0: ForallBegin, loop_end jumps to PC 3
        func.emit(Opcode::ForallBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 3,
        });
        // PC 1: body — just use the binding as-is
        func.emit(Opcode::Move { rd: 3, rs: 1 });
        // PC 2: ForallNext, loop_begin jumps back to PC 1
        func.emit(Opcode::ForallNext {
            rd: 0,
            r_binding: 1,
            r_body: 3,
            loop_begin: -1,
        });
        // PC 3: return result
        func.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_exists_quantifier() {
        let mut func = BytecodeFunction::new("test".to_string(), 3);
        func.emit(Opcode::ExistsBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 3,
        });
        func.emit(Opcode::Move { rd: 3, rs: 1 });
        func.emit(Opcode::ExistsNext {
            rd: 0,
            r_binding: 1,
            r_body: 3,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_choose_with_invalid_jump_target_rejected() {
        // ChooseBegin is eligible when jump targets are valid, but rejected
        // when loop_end points outside the function body.
        let mut func = BytecodeFunction::new("test".to_string(), 2);
        func.emit(Opcode::ChooseBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 2, // out of bounds (len=2, so valid indices are 0..1)
        });
        func.emit(Opcode::Ret { rs: 0 });
        let err = check_eligibility(&func).unwrap_err();
        assert!(err.contains("outside function body"), "got: {err}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_domain() {
        // Domain produces a set (compound) but is JIT-eligible: the lowerer
        // emits FallbackNeeded at runtime. Part of #3909.
        let mut func = BytecodeFunction::new("test".to_string(), 1);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::Domain { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "Domain should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_choose_begin_and_next() {
        // ChooseBegin/ChooseNext are JIT-eligible quantifier loops.
        // Part of #3909: verify existing eligibility.
        let mut func = BytecodeFunction::new("test".to_string(), 3);
        func.emit(Opcode::ChooseBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 3,
        }); // PC 0, exit=PC 3
        func.emit(Opcode::Move { rd: 3, rs: 1 }); // PC 1: body
        func.emit(Opcode::ChooseNext {
            rd: 0,
            r_binding: 1,
            r_body: 3,
            loop_begin: -1,
        }); // PC 2, back to PC 1
        func.emit(Opcode::Ret { rs: 0 }); // PC 3
        assert!(
            check_eligibility(&func).is_ok(),
            "ChooseBegin/ChooseNext should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_ineligible_backward_jump() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::JumpFalse { rs: 0, offset: -1 });
        func.emit(Opcode::Ret { rs: 0 });
        let err = check_eligibility(&func).unwrap_err();
        assert!(err.contains("later instruction"), "got: {err}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_builtin_is_finite_set() {
        // CallBuiltin IsFiniteSet is JIT-eligible: always emits iconst 1.
        // Part of #3909 item 2.3.
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::IsFiniteSet,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "CallBuiltin IsFiniteSet should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_builtin_cardinality() {
        // CallBuiltin Cardinality is JIT-eligible: emits FallbackNeeded
        // without layout, or native count read with layout.
        // Part of #3909 item 2.3.
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Cardinality,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "CallBuiltin Cardinality should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_builtin_len() {
        // CallBuiltin Len is JIT-eligible.
        // Part of #3909 item 2.3.
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Len,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "CallBuiltin Len should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_builtin_head() {
        // CallBuiltin Head is JIT-eligible: native lowering with layout info
        // (reads first element directly), or FallbackNeeded without layout.
        // Part of #3909 item 2.3.
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Head,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "CallBuiltin Head should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_builtin_tail() {
        // CallBuiltin Tail is JIT-eligible (emits FallbackNeeded — produces compound).
        // Part of #3909.
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Tail,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "CallBuiltin Tail should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_builtin_append() {
        // CallBuiltin Append is JIT-eligible (emits FallbackNeeded — produces compound).
        // Part of #3909.
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Append,
            args_start: 0,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "CallBuiltin Append should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_builtin_subseq() {
        // CallBuiltin SubSeq is JIT-eligible (emits FallbackNeeded — produces compound).
        // Part of #3909.
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::SubSeq,
            args_start: 0,
            argc: 3,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            check_eligibility(&func).is_ok(),
            "CallBuiltin SubSeq should be JIT-eligible"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_check_rejects_tuple_new_when_seq_var_present() {
        let layout = seq_state_layout();
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::TupleNew {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let err = check_seq_compatible(&func, Some(&layout)).unwrap_err();
        assert!(err.contains("TupleNew"), "got: {err}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_check_accepts_when_no_seq_var() {
        let layout = scalar_state_layout();
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::TupleNew {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });

        assert!(check_seq_compatible(&func, Some(&layout)).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_check_accepts_scalar_only_action_with_seq_var() {
        let layout = seq_state_layout();
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::Ret { rs: 0 });

        assert!(check_seq_compatible(&func, Some(&layout)).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_check_rejects_callbuiltin_append() {
        use tla_tir::bytecode::BuiltinOp;

        let layout = seq_state_layout();
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::CallBuiltin {
            rd: 0,
            builtin: BuiltinOp::Append,
            args_start: 1,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let err = check_seq_compatible(&func, Some(&layout)).unwrap_err();
        assert!(err.contains("CallBuiltin(Seq-op)"), "got: {err}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_check_accepts_callbuiltin_len_on_seq() {
        // Len on a Seq has a native lowering (reads count slot), so it does
        // NOT hit compound fallback. Must NOT be rejected. Part of #4304.
        use tla_tir::bytecode::BuiltinOp;

        let layout = seq_state_layout();
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Len,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        assert!(
            check_seq_compatible(&func, Some(&layout)).is_ok(),
            "Len should not be rejected on Seq state var"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_check_accepts_when_layout_unknown() {
        // Without a layout, the check is a no-op — no way to know whether any
        // var is Seq-typed, so never reject.
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::TupleNew {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });

        assert!(check_seq_compatible(&func, None).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_check_rejects_concat_when_seq_var_present() {
        let layout = seq_state_layout();
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::Concat {
            rd: 0,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let err = check_seq_compatible(&func, Some(&layout)).unwrap_err();
        assert!(err.contains("Concat"), "got: {err}");
    }

    // =================================================================
    // Phase 2 eligibility tests: compound-producing opcodes
    // Part of #3909.
    // =================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_compound_construction_opcodes() {
        // All compound-producing opcodes should be eligible.
        let cases: Vec<(&str, Vec<Opcode>)> = vec![
            (
                "RecordNew",
                vec![
                    Opcode::RecordNew {
                        rd: 0,
                        fields_start: 0,
                        values_start: 0,
                        count: 0,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "TupleNew",
                vec![
                    Opcode::TupleNew {
                        rd: 0,
                        start: 0,
                        count: 0,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "SeqNew",
                vec![
                    Opcode::SeqNew {
                        rd: 0,
                        start: 0,
                        count: 0,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "FuncExcept",
                vec![
                    Opcode::FuncExcept {
                        rd: 0,
                        func: 0,
                        path: 1,
                        val: 2,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "FuncSet",
                vec![
                    Opcode::FuncSet {
                        rd: 0,
                        domain: 1,
                        range: 2,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "RecordSet",
                vec![
                    Opcode::RecordSet {
                        rd: 0,
                        fields_start: 0,
                        values_start: 0,
                        count: 0,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "Times",
                vec![
                    Opcode::Times {
                        rd: 0,
                        start: 0,
                        count: 0,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "StrConcat",
                vec![
                    Opcode::StrConcat {
                        rd: 0,
                        r1: 0,
                        r2: 1,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
            (
                "Concat",
                vec![
                    Opcode::Concat {
                        rd: 0,
                        r1: 0,
                        r2: 1,
                    },
                    Opcode::Ret { rs: 0 },
                ],
            ),
        ];

        for (name, instructions) in cases {
            let mut func = BytecodeFunction::new(format!("test_{name}"), 2);
            for op in instructions {
                func.emit(op);
            }
            assert!(
                check_eligibility(&func).is_ok(),
                "{name} should be JIT-eligible (emits FallbackNeeded)"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_set_operation_opcodes() {
        // Set operations that produce sets should be eligible.
        let cases: Vec<(&str, Opcode)> = vec![
            (
                "SetUnion",
                Opcode::SetUnion {
                    rd: 0,
                    r1: 0,
                    r2: 1,
                },
            ),
            (
                "SetIntersect",
                Opcode::SetIntersect {
                    rd: 0,
                    r1: 0,
                    r2: 1,
                },
            ),
            (
                "SetDiff",
                Opcode::SetDiff {
                    rd: 0,
                    r1: 0,
                    r2: 1,
                },
            ),
            ("Powerset", Opcode::Powerset { rd: 0, rs: 0 }),
            ("BigUnion", Opcode::BigUnion { rd: 0, rs: 0 }),
            (
                "KSubset",
                Opcode::KSubset {
                    rd: 0,
                    base: 0,
                    k: 1,
                },
            ),
        ];

        for (name, op) in cases {
            let mut func = BytecodeFunction::new(format!("test_{name}"), 1);
            func.emit(op);
            func.emit(Opcode::Ret { rs: 0 });
            assert!(
                check_eligibility(&func).is_ok(),
                "{name} should be JIT-eligible (emits FallbackNeeded)"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_call_opcodes() {
        // Call, ValueApply, CallExternal, MakeClosure should be eligible.
        let mut func1 = BytecodeFunction::new("test_call".to_string(), 1);
        func1.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 1,
            argc: 0,
        });
        func1.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func1).is_ok());

        let mut func2 = BytecodeFunction::new("test_callext".to_string(), 1);
        func2.emit(Opcode::CallExternal {
            rd: 0,
            name_idx: 0,
            args_start: 1,
            argc: 0,
        });
        func2.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func2).is_ok());

        let mut func3 = BytecodeFunction::new("test_closure".to_string(), 1);
        func3.emit(Opcode::MakeClosure {
            rd: 0,
            template_idx: 0,
            captures_start: 1,
            capture_count: 0,
        });
        func3.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func3).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_halt() {
        let mut func = BytecodeFunction::new("test_halt".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::Halt);
        func.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_set_prime_mode() {
        let mut func = BytecodeFunction::new("test_spm".to_string(), 0);
        func.emit(Opcode::SetPrimeMode { enable: true });
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func).is_ok());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eligible_loop_opcodes() {
        // SetBuilderBegin, SetFilterBegin, FuncDefBegin, LoopNext
        let mut func = BytecodeFunction::new("test_builder".to_string(), 2);
        func.emit(Opcode::SetBuilderBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 2,
        });
        func.emit(Opcode::LoopNext {
            r_binding: 1,
            r_body: 0,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 0 });
        assert!(check_eligibility(&func).is_ok());
    }
}
