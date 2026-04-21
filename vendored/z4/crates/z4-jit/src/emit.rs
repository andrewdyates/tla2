// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause-to-machine-code generation for propagation functions.
//!
//! Generates one native function per (variable, polarity) pair. Each function
//! processes all clauses containing the literal that becomes false when the
//! variable is assigned. Uses the platform-specific assembler (aarch64 or
//! x86_64) to emit native instructions.

#[cfg(target_arch = "aarch64")]
use crate::aarch64::*;

#[cfg(target_arch = "x86_64")]
use crate::x86_64::*;

/// Emit a complete propagation function for a list of clauses.
/// Each clause is `(clause_id, other_lits)` where `other_lits` are the
/// remaining literals after the trigger literal.
///
/// Returns the assembled function bytes.
pub(crate) fn emit_propagation_function(clauses: &[(u32, &[u32])]) -> Vec<u8> {
    let mut asm = Assembler::new();

    // Function prologue.
    asm.prologue();

    // Load context struct fields into fixed registers.
    #[cfg(target_arch = "aarch64")]
    {
        asm.ldr_x_uimm(VALS, CTX, crate::context::OFFSET_VALS as u32);
        asm.ldr_x_uimm(TRAIL, CTX, crate::context::OFFSET_TRAIL as u32);
        asm.ldr_x_uimm(TRAIL_LEN_PTR, CTX, crate::context::OFFSET_TRAIL_LEN as u32);
        asm.ldr_x_uimm(GUARDS, CTX, crate::context::OFFSET_GUARDS as u32);
        asm.ldr_x_uimm(REASONS, CTX, crate::context::OFFSET_REASONS as u32);
        // Load current trail_len value.
        asm.ldr_w_uimm(TRAIL_LEN, TRAIL_LEN_PTR, 0);
        // Pre-load constant 1 for enqueue and EOR operations.
        asm.movz_w(CONST_ONE, 1);
    }

    #[cfg(target_arch = "x86_64")]
    {
        asm.load_context_fields();
    }

    // Emit code for each clause.
    for (i, &(clause_id, other_lits)) in clauses.iter().enumerate() {
        let is_last = i == clauses.len() - 1;

        // Label for the next clause (skip target for guard/blocker/satisfied).
        let next_clause = if is_last {
            None
        } else {
            Some(asm.label())
        };

        // We need a label to jump to when skipping. For the last clause,
        // we jump to the function epilogue instead.
        let skip_label = if let Some(l) = next_clause {
            l
        } else {
            let l = asm.label();
            emit_clause_body(&mut asm, clause_id, other_lits, l);
            // Bind the skip label at the return-OK position.
            asm.bind(l);
            // Return 0 (no conflict). On aarch64, return is in x0 (Reg(0)).
            // On x86_64, return is in RAX (Reg(0)).
            asm.movz_w(Reg(0), 0);
            asm.epilogue();
            break;
        };

        emit_clause_body(&mut asm, clause_id, other_lits, skip_label);

        // Bind the next_clause label.
        if let Some(l) = next_clause {
            asm.bind(l);
        }
    }

    // If no clauses were emitted (shouldn't happen in practice), emit return.
    if clauses.is_empty() {
        asm.movz_w(Reg(0), 0);
        asm.epilogue();
    }

    asm.finalize()
}

/// Emit the body of a single clause: guard check, blocker check, then
/// type-specific propagation logic.
fn emit_clause_body(asm: &mut Assembler, clause_id: u32, other_lits: &[u32], skip: Label) {
    // Guard check: if guards[clause_id] == 0, skip this clause.
    asm.load_guard(T0, clause_id);
    asm.cbz_w(T0, skip);

    // Blocker check: for non-binary clauses, check if the first other
    // literal (sorted by var index for early-exit) is already satisfied.
    if other_lits.len() >= 2 {
        asm.load_val(T0, other_lits[0]);
        asm.cmp_w_imm(T0, 0);
        asm.b_cond(Cond::Gt, skip);
    }

    match other_lits.len() {
        1 => emit_binary(asm, clause_id, other_lits[0], skip),
        2 => emit_ternary(asm, clause_id, other_lits, skip),
        _ => emit_general(asm, clause_id, other_lits, skip),
    }
}

/// Binary clause: one other literal. Check satisfied/unassigned/falsified.
fn emit_binary(asm: &mut Assembler, clause_id: u32, other_lit: u32, skip: Label) {
    // Load value (binary doesn't have a blocker check, so we load here).
    asm.load_val(T0, other_lit);
    asm.cmp_w_imm(T0, 0);

    // val > 0: satisfied, skip
    asm.b_cond(Cond::Gt, skip);

    // val == 0: unassigned, propagate
    let propagate = asm.label();
    asm.b_cond(Cond::Eq, propagate);

    // val < 0: conflict
    asm.emit_conflict(clause_id);

    // Propagate: enqueue other_lit
    asm.bind(propagate);
    asm.emit_enqueue_const(other_lit, clause_id);
    asm.b(skip);
}

/// Ternary clause: two other literals.
fn emit_ternary(asm: &mut Assembler, clause_id: u32, other_lits: &[u32], skip: Label) {
    let [lit_a, lit_b] = [other_lits[0], other_lits[1]];

    // Load both values. Reload lit_a even though blocker may have loaded it
    // (the value is in L1 cache from the blocker check).
    asm.load_val(T0, lit_a);
    asm.load_val(T1, lit_b);

    // Check lit_a satisfied.
    asm.cmp_w_imm(T0, 0);
    asm.b_cond(Cond::Gt, skip);

    // Check lit_b satisfied.
    asm.cmp_w_imm(T1, 0);
    asm.b_cond(Cond::Gt, skip);

    // Neither satisfied. Determine unassigned vs false.
    let a_unassigned = asm.label();
    let a_false = asm.label();

    asm.cmp_w_imm(T0, 0);
    asm.b_cond(Cond::Eq, a_unassigned);
    asm.b(a_false);

    // a is unassigned
    asm.bind(a_unassigned);
    {
        // If b is also unassigned, no unit propagation (2 unassigned).
        asm.cmp_w_imm(T1, 0);
        asm.b_cond(Cond::Eq, skip);
        // b is false, a is unassigned -> propagate a.
        asm.emit_enqueue_const(lit_a, clause_id);
        asm.b(skip);
    }

    // a is false
    asm.bind(a_false);
    {
        let propagate_b = asm.label();
        asm.cmp_w_imm(T1, 0);
        asm.b_cond(Cond::Eq, propagate_b);
        // Both false -> conflict.
        asm.emit_conflict(clause_id);

        // b unassigned, a false -> propagate b.
        asm.bind(propagate_b);
        asm.emit_enqueue_const(lit_b, clause_id);
        asm.b(skip);
    }
}

/// General clause: 3+ other literals. Unrolled scan with false_count
/// and last_unasgn tracking via CSEL.
fn emit_general(asm: &mut Assembler, clause_id: u32, other_lits: &[u32], skip: Label) {
    let n = other_lits.len();

    // Platform-specific scratch register access.
    // On aarch64, T0-T7 are consecutive (Reg(7)..Reg(14)), so Reg(T0.0 + i) works.
    // On x86_64, T0-T7 are non-consecutive; use the SCRATCH array.
    #[cfg(target_arch = "aarch64")]
    let max_cached: usize = 8;
    #[cfg(target_arch = "x86_64")]
    let max_cached: usize = MAX_CACHED;

    // Helper to get the i-th scratch register.
    #[cfg(target_arch = "aarch64")]
    let scratch_reg = |i: usize| -> Reg { Reg(T0.0 + i as u8) };
    #[cfg(target_arch = "x86_64")]
    let scratch_reg = |i: usize| -> Reg { SCRATCH[i] };

    // Registers for false_count and last_unasgn tracking.
    // On aarch64: T8 (Reg(16)) and T9 (Reg(17)) are dedicated.
    // On x86_64: reuse T5 (R9) and T6 (R10) for count/tracking,
    // reducing max_cached but avoiding register conflicts.
    #[cfg(target_arch = "aarch64")]
    let (false_count_reg, last_unasgn_reg) = (T8, T9);
    #[cfg(target_arch = "x86_64")]
    let (false_count_reg, last_unasgn_reg) = (T5, T6);

    if n <= max_cached {
        // Phase 1: Load all values into scratch registers.
        let val_regs: Vec<Reg> = (0..n).map(|i| scratch_reg(i)).collect();
        for (i, &lit) in other_lits.iter().enumerate() {
            asm.load_val(val_regs[i], lit);
        }

        // Early-exit on any satisfied literal.
        for i in 0..n {
            asm.cmp_w_imm(val_regs[i], 0);
            asm.b_cond(Cond::Gt, skip);
        }

        // Phase 2: Count false, track last unassigned (as encoded literal).
        asm.movz_w(false_count_reg, 0);
        asm.mov_imm32(last_unasgn_reg, other_lits[0]); // sentinel

        for (i, &lit) in other_lits.iter().enumerate() {
            // CMP sets flags, MOV does NOT affect flags on either arch.
            asm.cmp_w_imm(val_regs[i], 0);
            let lit_reg = val_regs[i]; // reuse val_reg (overwrite with lit constant)
            asm.mov_imm32(lit_reg, lit);
            asm.csel_w(last_unasgn_reg, lit_reg, last_unasgn_reg, Cond::Eq);

            // false_count increment: if val != 0 (false), increment.
            // Need a temp register for false_count + 1. Use a register past
            // the val range if available, otherwise compute in place.
            #[cfg(target_arch = "aarch64")]
            {
                let tmp_inc = Reg(T0.0 + n as u8);
                if T0.0 + n as u8 > 14 {
                    asm.add_w_imm(T0, false_count_reg, 1);
                    asm.csel_w(false_count_reg, T0, false_count_reg, Cond::Ne);
                } else {
                    asm.add_w_imm(tmp_inc, false_count_reg, 1);
                    asm.csel_w(false_count_reg, tmp_inc, false_count_reg, Cond::Ne);
                }
            }
            #[cfg(target_arch = "x86_64")]
            {
                // Use T7 (R11) as temp for increment — it's not in val_regs
                // when n <= MAX_CACHED (5), and not used as false_count or
                // last_unasgn (those are T5/T6).
                asm.add_w_imm(T7, false_count_reg, 1);
                asm.csel_w(false_count_reg, T7, false_count_reg, Cond::Ne);
            }
        }

        // Phase 3: Analyze results.
        let n_const = n as u32;

        // All false -> conflict.
        asm.cmp_w_imm(false_count_reg, n_const);
        let not_conflict = asm.label();
        asm.b_cond(Cond::Ne, not_conflict);
        asm.emit_conflict(clause_id);

        asm.bind(not_conflict);

        // Exactly one unassigned -> propagate.
        let not_unit = asm.label();
        asm.add_w_imm(T0, false_count_reg, 1);
        asm.cmp_w_imm(T0, n_const);
        asm.b_cond(Cond::Ne, not_unit);

        asm.emit_enqueue_runtime(last_unasgn_reg, clause_id);
        asm.b(skip);

        // 2+ unassigned: skip.
        asm.bind(not_unit);
        asm.b(skip);
    } else {
        // Large clause (> max_cached remaining lits). Single-pass: load,
        // check satisfied, update counts.
        asm.movz_w(false_count_reg, 0);
        asm.mov_imm32(last_unasgn_reg, other_lits[0]);

        for &lit in other_lits {
            asm.load_val(T0, lit);
            asm.cmp_w_imm(T0, 0);
            asm.b_cond(Cond::Gt, skip); // satisfied -> early exit

            // Count phase (flags still set from CMP).
            asm.mov_imm32(T1, lit);
            asm.csel_w(last_unasgn_reg, T1, last_unasgn_reg, Cond::Eq);
            asm.add_w_imm(T2, false_count_reg, 1);
            asm.csel_w(false_count_reg, T2, false_count_reg, Cond::Ne);
        }

        // All false -> conflict.
        let n_const = n as u32;
        asm.cmp_w_imm(false_count_reg, n_const);
        let not_conflict = asm.label();
        asm.b_cond(Cond::Ne, not_conflict);
        asm.emit_conflict(clause_id);

        asm.bind(not_conflict);

        // Exactly one unassigned -> propagate.
        let not_unit = asm.label();
        asm.add_w_imm(T0, false_count_reg, 1);
        asm.cmp_w_imm(T0, n_const);
        asm.b_cond(Cond::Ne, not_unit);

        asm.emit_enqueue_runtime(last_unasgn_reg, clause_id);
        asm.b(skip);

        asm.bind(not_unit);
        asm.b(skip);
    }
}
