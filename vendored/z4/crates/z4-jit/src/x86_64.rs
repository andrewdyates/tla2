// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal x86_64 assembler for SAT clause propagation functions.
//!
//! Supports only the instruction subset needed for BCP: load/store (byte,
//! dword, qword), compare/branch, integer arithmetic, and the System V
//! AMD64 calling convention. No floating-point, SIMD, or atomics.
//!
//! x86_64 uses variable-length instructions (1-15 bytes). Branch targets
//! use a label + fixup system for forward references, resolved in `finalize()`.
//!
//! # Testing status
//!
//! This backend cross-compiles cleanly on aarch64 but has NOT been execution-
//! tested on an actual x86_64 machine. Instruction encoding correctness
//! (REX prefixes, ModRM, SIB, RBP/R13 base edge cases) needs validation
//! on x86_64 hardware. See GitHub issue for testing plan.

/// General-purpose register (0-15).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Reg(pub u8);

// System V AMD64 calling convention:
//   Args: rdi, rsi, rdx, rcx, r8, r9
//   Callee-saved: rbx, rbp, r12-r15
//   Caller-saved: rax, rcx, rdx, rsi, rdi, r8-r11
//   Return: rax

// Register encoding.
pub(crate) const RAX: Reg = Reg(0);
pub(crate) const RCX: Reg = Reg(1);
pub(crate) const RDX: Reg = Reg(2);
pub(crate) const RBX: Reg = Reg(3);
#[allow(dead_code)]
pub(crate) const RSP: Reg = Reg(4);
pub(crate) const RBP: Reg = Reg(5);
pub(crate) const RSI: Reg = Reg(6);
pub(crate) const RDI: Reg = Reg(7);
pub(crate) const R8: Reg = Reg(8);
pub(crate) const R9: Reg = Reg(9);
pub(crate) const R10: Reg = Reg(10);
pub(crate) const R11: Reg = Reg(11);
pub(crate) const R12: Reg = Reg(12);
pub(crate) const R13: Reg = Reg(13);
pub(crate) const R14: Reg = Reg(14);
pub(crate) const R15: Reg = Reg(15);

// Fixed register assignments for propagation functions.
// We save CTX (rdi) into a callee-saved register and use callee-saved
// registers for all context pointers so they survive across the function.

/// Context pointer (saved from rdi argument).
pub(crate) const CTX: Reg = RBX;    // callee-saved
/// vals pointer.
pub(crate) const VALS: Reg = R12;   // callee-saved
/// trail pointer.
pub(crate) const TRAIL: Reg = R13;  // callee-saved
/// trail_len pointer.
pub(crate) const TRAIL_LEN_PTR: Reg = R14; // callee-saved
/// guards pointer.
pub(crate) const GUARDS: Reg = R15; // callee-saved
/// reasons pointer.
pub(crate) const REASONS: Reg = RBP; // callee-saved
/// Current trail_len value (updated on enqueue). Caller-saved, but we
/// control all code so this is fine.
pub(crate) const TRAIL_LEN: Reg = RSI;

// Scratch registers for clause bodies.
pub(crate) const T0: Reg = RAX;
pub(crate) const T1: Reg = RCX;
pub(crate) const T2: Reg = RDX;
pub(crate) const T3: Reg = RDI;
pub(crate) const T4: Reg = R8;
pub(crate) const T5: Reg = R9;
pub(crate) const T6: Reg = R10;
pub(crate) const T7: Reg = R11;
// T8/T9 — we reuse T0/T1 when needed in high-level helpers, which
// is safe because the helpers own their scratch register usage.

/// Scratch registers array for indexed access (non-consecutive hardware regs).
/// On x86_64, T0-T7 map to non-consecutive register numbers, so
/// `Reg(T0.0 + i)` does NOT work. Use `SCRATCH[i]` instead.
pub(crate) const SCRATCH: [Reg; 8] = [T0, T1, T2, T3, T4, T5, T6, T7];

/// Maximum number of scratch registers available for the cached-values
/// path in emit_general. On x86_64 we have 8 scratch registers but
/// the count/tracking phase needs T0-T2, so limit cached to 5.
pub(crate) const MAX_CACHED: usize = 5;

/// Condition codes for Jcc and CMOVcc.
#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum Cond {
    Eq = 0x4,   // ZF=1 (JE/CMOVE)
    Ne = 0x5,   // ZF=0 (JNE/CMOVNE)
    Gt = 0xF,   // ZF=0 && SF=OF (JG/CMOVG) — signed greater
    #[allow(dead_code)]
    Ge = 0xD,   // SF=OF (JGE/CMOVGE)
    #[allow(dead_code)]
    Lt = 0xC,   // SF!=OF (JL/CMOVL)
    #[allow(dead_code)]
    Le = 0xE,   // ZF=1 || SF!=OF (JLE/CMOVLE)
}

/// A branch target label.
#[derive(Clone, Copy)]
pub(crate) struct Label(u32);

/// Pending branch fixup.
struct Fixup {
    /// Byte offset in `code` where the rel32 displacement starts.
    offset: u32,
    /// Target label.
    label: Label,
}

/// Minimal x86_64 assembler.
pub(crate) struct Assembler {
    code: Vec<u8>,
    labels: Vec<Option<u32>>,
    fixups: Vec<Fixup>,
}

#[allow(dead_code)]
impl Assembler {
    pub fn new() -> Self {
        Self {
            code: Vec::with_capacity(1024),
            labels: Vec::new(),
            fixups: Vec::new(),
        }
    }

    /// Create a new unbound label.
    pub fn label(&mut self) -> Label {
        let id = self.labels.len() as u32;
        self.labels.push(None);
        Label(id)
    }

    /// Bind a label to the current code position.
    pub fn bind(&mut self, label: Label) {
        let offset = self.code.len() as u32;
        debug_assert!(
            self.labels[label.0 as usize].is_none(),
            "label already bound"
        );
        self.labels[label.0 as usize] = Some(offset);
    }

    fn emit_byte(&mut self, b: u8) {
        self.code.push(b);
    }

    fn emit_bytes(&mut self, bytes: &[u8]) {
        self.code.extend_from_slice(bytes);
    }

    fn emit_u32_le(&mut self, v: u32) {
        self.code.extend_from_slice(&v.to_le_bytes());
    }

    fn emit_i32_le(&mut self, v: i32) {
        self.code.extend_from_slice(&v.to_le_bytes());
    }

    /// REX prefix byte. W=1 for 64-bit operand size.
    fn rex(&self, w: bool, r: Reg, rm: Reg) -> u8 {
        let mut rex = 0x40u8;
        if w {
            rex |= 0x08;
        }
        if r.0 >= 8 {
            rex |= 0x04; // R
        }
        if rm.0 >= 8 {
            rex |= 0x01; // B
        }
        rex
    }

    /// REX prefix byte with SIB index register.
    fn rex_sib(&self, w: bool, r: Reg, index: Reg, base: Reg) -> u8 {
        let mut rex = 0x40u8;
        if w {
            rex |= 0x08;
        }
        if r.0 >= 8 {
            rex |= 0x04; // R
        }
        if index.0 >= 8 {
            rex |= 0x02; // X
        }
        if base.0 >= 8 {
            rex |= 0x01; // B
        }
        rex
    }

    /// ModRM byte: mod=11 (register-register).
    fn modrm_rr(r: Reg, rm: Reg) -> u8 {
        0xC0 | ((r.0 & 7) << 3) | (rm.0 & 7)
    }

    /// ModRM byte: mod=00 (register-indirect, no displacement).
    fn modrm_ind(r: Reg, rm: Reg) -> u8 {
        ((r.0 & 7) << 3) | (rm.0 & 7)
    }

    /// ModRM byte: mod=10 (register-indirect, disp32).
    fn modrm_disp32(r: Reg, rm: Reg) -> u8 {
        0x80 | ((r.0 & 7) << 3) | (rm.0 & 7)
    }

    /// ModRM byte: mod=01 (register-indirect, disp8).
    fn modrm_disp8(r: Reg, rm: Reg) -> u8 {
        0x40 | ((r.0 & 7) << 3) | (rm.0 & 7)
    }

    /// SIB byte for [base + index*scale].
    fn sib(scale: u8, index: Reg, base: Reg) -> u8 {
        let ss = match scale {
            1 => 0,
            2 => 1,
            4 => 2,
            8 => 3,
            _ => panic!("invalid SIB scale: {scale}"),
        };
        (ss << 6) | ((index.0 & 7) << 3) | (base.0 & 7)
    }

    /// Emit ModRM + SIB for [base + index*scale] addressing.
    /// Handles the RBP/R13 base encoding edge case: when (base & 7) == 5,
    /// mod=00 + SIB with base=101 means [disp32 + index*scale] (no base),
    /// so we must use mod=01 with disp8=0 to encode [base + index*scale].
    fn emit_sib_indexed(&mut self, reg: Reg, scale: u8, index: Reg, base: Reg) {
        if (base.0 & 7) == 5 {
            // RBP/R13 base: use mod=01 + disp8=0
            self.emit_byte(Self::modrm_disp8(reg, Reg(4)));
            self.emit_byte(Self::sib(scale, index, base));
            self.emit_byte(0); // disp8 = 0
        } else {
            self.emit_byte(Self::modrm_ind(reg, Reg(4)));
            self.emit_byte(Self::sib(scale, index, base));
        }
    }

    // ---- Function prologue/epilogue ----

    /// Push callee-saved registers + save CTX.
    pub fn prologue(&mut self) {
        // push rbx
        self.emit_rex_if_needed(false, Reg(0), RBX);
        self.emit_byte(0x50 + (RBX.0 & 7));
        // push rbp
        self.emit_byte(0x55);
        // push r12
        self.emit_byte(0x41);
        self.emit_byte(0x54);
        // push r13
        self.emit_byte(0x41);
        self.emit_byte(0x55);
        // push r14
        self.emit_byte(0x41);
        self.emit_byte(0x56);
        // push r15
        self.emit_byte(0x41);
        self.emit_byte(0x57);
        // mov rbx, rdi  (save context pointer)
        self.mov_r64(CTX, RDI);
    }

    /// Pop callee-saved registers + return.
    pub fn epilogue(&mut self) {
        // pop r15
        self.emit_byte(0x41);
        self.emit_byte(0x5F);
        // pop r14
        self.emit_byte(0x41);
        self.emit_byte(0x5E);
        // pop r13
        self.emit_byte(0x41);
        self.emit_byte(0x5D);
        // pop r12
        self.emit_byte(0x41);
        self.emit_byte(0x5C);
        // pop rbp
        self.emit_byte(0x5D);
        // pop rbx
        self.emit_byte(0x5B);
        // ret
        self.emit_byte(0xC3);
    }

    fn emit_rex_if_needed(&mut self, w: bool, r: Reg, rm: Reg) {
        let rex = self.rex(w, r, rm);
        if rex != 0x40 || w {
            self.emit_byte(rex);
        }
    }

    // ---- Load/Store ----

    /// MOV r64, [base + disp32] — 64-bit load.
    pub fn mov_r64_mem(&mut self, dst: Reg, base: Reg, disp: i32) {
        let rex = self.rex(true, dst, base);
        self.emit_byte(rex);
        self.emit_byte(0x8B);
        // If base is rsp/r12, need SIB byte
        if (base.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(dst, base));
            self.emit_byte(Self::sib(1, Reg(4), base)); // SIB: no index
        } else {
            self.emit_byte(Self::modrm_disp32(dst, base));
        }
        self.emit_i32_le(disp);
    }

    /// MOV r32, [base + disp32] — 32-bit load.
    pub fn mov_r32_mem(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.emit_rex_if_needed(false, dst, base);
        self.emit_byte(0x8B);
        if (base.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(dst, base));
            self.emit_byte(Self::sib(1, Reg(4), base));
        } else {
            self.emit_byte(Self::modrm_disp32(dst, base));
        }
        self.emit_i32_le(disp);
    }

    /// MOV [base + disp32], r32 — 32-bit store.
    pub fn mov_mem_r32(&mut self, base: Reg, disp: i32, src: Reg) {
        self.emit_rex_if_needed(false, src, base);
        self.emit_byte(0x89);
        if (base.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(src, base));
            self.emit_byte(Self::sib(1, Reg(4), base));
        } else {
            self.emit_byte(Self::modrm_disp32(src, base));
        }
        self.emit_i32_le(disp);
    }

    /// MOVSX r32, byte [base + disp32] — sign-extending byte load.
    pub fn movsx_r32_byte_mem(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.emit_rex_if_needed(false, dst, base);
        self.emit_byte(0x0F);
        self.emit_byte(0xBE);
        if (base.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(dst, base));
            self.emit_byte(Self::sib(1, Reg(4), base));
        } else {
            self.emit_byte(Self::modrm_disp32(dst, base));
        }
        self.emit_i32_le(disp);
    }

    /// MOVSX r32, byte [base + index*1] — sign-extending byte load, register offset.
    pub fn movsx_r32_byte_indexed(&mut self, dst: Reg, base: Reg, index: Reg) {
        let rex = self.rex_sib(false, dst, index, base);
        if rex != 0x40 {
            self.emit_byte(rex);
        }
        self.emit_byte(0x0F);
        self.emit_byte(0xBE);
        self.emit_sib_indexed(dst, 1, index, base);
    }

    /// MOVZX r32, byte [base + disp32] — zero-extending byte load.
    pub fn movzx_r32_byte_mem(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.emit_rex_if_needed(false, dst, base);
        self.emit_byte(0x0F);
        self.emit_byte(0xB6);
        if (base.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(dst, base));
            self.emit_byte(Self::sib(1, Reg(4), base));
        } else {
            self.emit_byte(Self::modrm_disp32(dst, base));
        }
        self.emit_i32_le(disp);
    }

    /// MOVZX r32, byte [base + index*1] — zero-extending byte load, register offset.
    pub fn movzx_r32_byte_indexed(&mut self, dst: Reg, base: Reg, index: Reg) {
        let rex = self.rex_sib(false, dst, index, base);
        if rex != 0x40 {
            self.emit_byte(rex);
        }
        self.emit_byte(0x0F);
        self.emit_byte(0xB6);
        self.emit_sib_indexed(dst, 1, index, base);
    }

    /// MOV byte [base + disp32], imm8 — byte store immediate.
    pub fn mov_byte_mem_imm(&mut self, base: Reg, disp: i32, imm: u8) {
        self.emit_rex_if_needed(false, Reg(0), base);
        self.emit_byte(0xC6);
        if (base.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(Reg(0), base));
            self.emit_byte(Self::sib(1, Reg(4), base));
        } else {
            self.emit_byte(Self::modrm_disp32(Reg(0), base));
        }
        self.emit_i32_le(disp);
        self.emit_byte(imm);
    }

    /// MOV byte [base + index*1], imm8 — byte store with register offset.
    pub fn mov_byte_indexed_imm(&mut self, base: Reg, index: Reg, imm: u8) {
        let rex = self.rex_sib(false, Reg(0), index, base);
        if rex != 0x40 {
            self.emit_byte(rex);
        }
        self.emit_byte(0xC6);
        self.emit_sib_indexed(Reg(0), 1, index, base);
        self.emit_byte(imm);
    }

    /// MOV byte [base + index*1], r8 — byte store register.
    pub fn mov_byte_indexed_r8(&mut self, base: Reg, index: Reg, src: Reg) {
        let rex = self.rex_sib(false, src, index, base);
        // Always emit REX if src/index/base >= 4 to access r8-r15
        // and to ensure correct encoding for sil/dil/bpl/spl
        if rex != 0x40 || src.0 >= 4 {
            self.emit_byte(rex);
        }
        self.emit_byte(0x88);
        self.emit_sib_indexed(src, 1, index, base);
    }

    /// MOV [base + index*4], r32 — 32-bit store with scaled index.
    pub fn mov_mem_indexed_r32(&mut self, base: Reg, index: Reg, src: Reg) {
        let rex = self.rex_sib(false, src, index, base);
        if rex != 0x40 {
            self.emit_byte(rex);
        }
        self.emit_byte(0x89);
        self.emit_sib_indexed(src, 4, index, base);
    }

    /// MOV r32, [base + index*4] — 32-bit load with scaled index.
    #[allow(dead_code)]
    pub fn mov_r32_indexed(&mut self, dst: Reg, base: Reg, index: Reg) {
        let rex = self.rex_sib(false, dst, index, base);
        if rex != 0x40 {
            self.emit_byte(rex);
        }
        self.emit_byte(0x8B);
        self.emit_sib_indexed(dst, 4, index, base);
    }

    // ---- Move / Immediate ----

    /// MOV r32, imm32 — load 32-bit immediate.
    pub fn mov_r32_imm(&mut self, rd: Reg, imm: u32) {
        self.emit_rex_if_needed(false, Reg(0), rd);
        self.emit_byte(0xB8 + (rd.0 & 7));
        self.emit_u32_le(imm);
    }

    /// MOV r64, r64 — register-to-register move (64-bit).
    pub fn mov_r64(&mut self, dst: Reg, src: Reg) {
        let rex = self.rex(true, src, dst);
        self.emit_byte(rex);
        self.emit_byte(0x89);
        self.emit_byte(Self::modrm_rr(src, dst));
    }

    /// MOV r32, r32 — register-to-register move (32-bit).
    pub fn mov_r32(&mut self, dst: Reg, src: Reg) {
        self.emit_rex_if_needed(false, src, dst);
        self.emit_byte(0x89);
        self.emit_byte(Self::modrm_rr(src, dst));
    }

    /// XOR r32, r32 — zero a register (smaller encoding than MOV r32, 0).
    pub fn xor_r32(&mut self, dst: Reg, src: Reg) {
        self.emit_rex_if_needed(false, dst, src);
        self.emit_byte(0x31);
        self.emit_byte(Self::modrm_rr(src, dst));
    }

    // ---- Arithmetic ----

    /// ADD r32, imm32.
    pub fn add_r32_imm(&mut self, rd: Reg, imm: i32) {
        if imm >= -128 && imm <= 127 {
            // ADD r32, imm8 (sign-extended)
            self.emit_rex_if_needed(false, Reg(0), rd);
            self.emit_byte(0x83);
            self.emit_byte(Self::modrm_rr(Reg(0), rd)); // /0 = ADD
            self.emit_byte(imm as u8);
        } else {
            self.emit_rex_if_needed(false, Reg(0), rd);
            self.emit_byte(0x81);
            self.emit_byte(Self::modrm_rr(Reg(0), rd));
            self.emit_i32_le(imm);
        }
    }

    /// SHR r32, imm8 — logical right shift.
    pub fn shr_r32_imm(&mut self, rd: Reg, shift: u8) {
        debug_assert!(shift > 0 && shift < 32);
        self.emit_rex_if_needed(false, Reg(0), rd);
        if shift == 1 {
            self.emit_byte(0xD1);
            self.emit_byte(Self::modrm_rr(Reg(5), rd)); // /5 = SHR
        } else {
            self.emit_byte(0xC1);
            self.emit_byte(Self::modrm_rr(Reg(5), rd));
            self.emit_byte(shift);
        }
    }

    /// XOR r32, r32 (arithmetic).
    pub fn xor_r32_r32(&mut self, dst: Reg, src: Reg) {
        self.emit_rex_if_needed(false, dst, src);
        self.emit_byte(0x33);
        self.emit_byte(Self::modrm_rr(dst, src));
    }

    /// XOR r32, imm8/32.
    pub fn xor_r32_imm(&mut self, rd: Reg, imm: i32) {
        if imm >= -128 && imm <= 127 {
            self.emit_rex_if_needed(false, Reg(0), rd);
            self.emit_byte(0x83);
            self.emit_byte(Self::modrm_rr(Reg(6), rd)); // /6 = XOR
            self.emit_byte(imm as u8);
        } else {
            self.emit_rex_if_needed(false, Reg(0), rd);
            self.emit_byte(0x81);
            self.emit_byte(Self::modrm_rr(Reg(6), rd));
            self.emit_i32_le(imm);
        }
    }

    /// LEA r32, [base + disp32] — compute address.
    pub fn lea_r32(&mut self, dst: Reg, base: Reg, disp: i32) {
        self.emit_rex_if_needed(false, dst, base);
        self.emit_byte(0x8D);
        if (base.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(dst, base));
            self.emit_byte(Self::sib(1, Reg(4), base));
        } else {
            self.emit_byte(Self::modrm_disp32(dst, base));
        }
        self.emit_i32_le(disp);
    }

    // ---- Compare ----

    /// CMP r32, imm32.
    pub fn cmp_r32_imm(&mut self, rn: Reg, imm: i32) {
        if imm >= -128 && imm <= 127 {
            self.emit_rex_if_needed(false, Reg(0), rn);
            self.emit_byte(0x83);
            self.emit_byte(Self::modrm_rr(Reg(7), rn)); // /7 = CMP
            self.emit_byte(imm as u8);
        } else {
            self.emit_rex_if_needed(false, Reg(0), rn);
            self.emit_byte(0x81);
            self.emit_byte(Self::modrm_rr(Reg(7), rn));
            self.emit_i32_le(imm);
        }
    }

    /// TEST r32, r32 — set flags based on AND.
    pub fn test_r32(&mut self, rn: Reg, rm: Reg) {
        self.emit_rex_if_needed(false, rm, rn);
        self.emit_byte(0x85);
        self.emit_byte(Self::modrm_rr(rm, rn));
    }

    // ---- Conditional select ----

    /// CMOV r32, r32, cond — conditional move.
    pub fn cmov_r32(&mut self, dst: Reg, src: Reg, cond: Cond) {
        self.emit_rex_if_needed(false, dst, src);
        self.emit_byte(0x0F);
        self.emit_byte(0x40 + cond as u8);
        self.emit_byte(Self::modrm_rr(dst, src));
    }

    // ---- Branches ----

    /// JMP rel32 — unconditional near jump.
    pub fn jmp(&mut self, label: Label) {
        self.emit_byte(0xE9);
        self.fixups.push(Fixup {
            offset: self.code.len() as u32,
            label,
        });
        self.emit_i32_le(0); // placeholder
    }

    /// Jcc rel32 — conditional near jump.
    pub fn jcc(&mut self, cond: Cond, label: Label) {
        self.emit_byte(0x0F);
        self.emit_byte(0x80 + cond as u8);
        self.fixups.push(Fixup {
            offset: self.code.len() as u32,
            label,
        });
        self.emit_i32_le(0); // placeholder
    }

    // ---- Finalization ----

    /// Resolve all branch fixups and return the code as a byte vector.
    pub fn finalize(mut self) -> Vec<u8> {
        for fixup in &self.fixups {
            let target = self.labels[fixup.label.0 as usize]
                .unwrap_or_else(|| panic!("unbound label L{}", fixup.label.0));
            // rel32 displacement is relative to the instruction AFTER the displacement.
            // The displacement field is 4 bytes at fixup.offset, so the next instruction
            // starts at fixup.offset + 4.
            let next_ip = fixup.offset + 4;
            let delta = target as i32 - next_ip as i32;
            self.code[fixup.offset as usize..fixup.offset as usize + 4]
                .copy_from_slice(&delta.to_le_bytes());
        }
        self.code
    }

    // ---- High-level helpers for propagation codegen ----

    /// Load context struct fields into fixed registers.
    pub fn load_context_fields(&mut self) {
        // CTX = RBX (already set in prologue from RDI)
        self.mov_r64_mem(VALS, CTX, crate::context::OFFSET_VALS);
        self.mov_r64_mem(TRAIL, CTX, crate::context::OFFSET_TRAIL);
        self.mov_r64_mem(TRAIL_LEN_PTR, CTX, crate::context::OFFSET_TRAIL_LEN);
        self.mov_r64_mem(GUARDS, CTX, crate::context::OFFSET_GUARDS);
        self.mov_r64_mem(REASONS, CTX, crate::context::OFFSET_REASONS);
        // Load current trail_len value (32-bit).
        self.mov_r32_mem(TRAIL_LEN, TRAIL_LEN_PTR, 0);
    }

    /// Load a sign-extended byte from vals[lit_encoded] into `dst`.
    pub fn load_val(&mut self, dst: Reg, lit_encoded: u32) {
        self.movsx_r32_byte_mem(dst, VALS, lit_encoded as i32);
    }

    /// Load a guard byte from guards[clause_id] into `dst`.
    pub fn load_guard(&mut self, dst: Reg, clause_id: u32) {
        self.movzx_r32_byte_mem(dst, GUARDS, clause_id as i32);
    }

    /// CMP r32, #imm — wrapper matching aarch64 API.
    pub fn cmp_w_imm(&mut self, rn: Reg, imm: u32) {
        self.cmp_r32_imm(rn, imm as i32);
    }

    /// Branch if register == 0.
    pub fn cbz_w(&mut self, rt: Reg, label: Label) {
        self.test_r32(rt, rt);
        self.jcc(Cond::Eq, label);
    }

    /// Conditional branch.
    pub fn b_cond(&mut self, cond: Cond, label: Label) {
        self.jcc(cond, label);
    }

    /// Unconditional branch.
    pub fn b(&mut self, label: Label) {
        self.jmp(label);
    }

    /// MOVZ equivalent — load immediate into 32-bit register (clears upper bits).
    pub fn movz_w(&mut self, rd: Reg, imm: u16) {
        self.mov_r32_imm(rd, imm as u32);
    }

    /// Load 32-bit immediate.
    pub fn mov_imm32(&mut self, rd: Reg, value: u32) {
        self.mov_r32_imm(rd, value);
    }

    /// CSEL equivalent using CMOV: if cond then rd=rn else rd=rm.
    /// On x86_64, CMOV is two-operand: CMOVcc dst, src.
    /// This emulates CSEL by: mov rd, rm; cmovcc rd, rn.
    /// (If rd is already rm, skip the mov.)
    pub fn csel_w(&mut self, rd: Reg, rn: Reg, rm: Reg, cond: Cond) {
        if rd != rm {
            self.mov_r32(rd, rm);
        }
        self.cmov_r32(rd, rn, cond);
    }

    /// ADD Wd, Wn, #imm — three-operand add emulated via LEA or MOV+ADD.
    pub fn add_w_imm(&mut self, rd: Reg, rn: Reg, imm: u32) {
        if rd == rn {
            self.add_r32_imm(rd, imm as i32);
        } else {
            self.lea_r32(rd, rn, imm as i32);
        }
    }

    /// Emit enqueue of a compile-time literal with a given clause_id as reason.
    pub fn emit_enqueue_const(&mut self, lit_encoded: u32, clause_id: u32) {
        let var = lit_encoded >> 1;
        let neg_lit = lit_encoded ^ 1;

        // trail[trail_len] = lit_encoded
        self.mov_r32_imm(T0, lit_encoded);
        self.mov_mem_indexed_r32(TRAIL, TRAIL_LEN, T0);

        // trail_len++
        self.add_r32_imm(TRAIL_LEN, 1);
        self.mov_mem_r32(TRAIL_LEN_PTR, 0, TRAIL_LEN);

        // reasons[var] = clause_id
        self.mov_r32_imm(T0, clause_id);
        self.mov_r32_imm(T1, var);
        self.mov_mem_indexed_r32(REASONS, T1, T0);

        // vals[lit_encoded] = 1
        self.mov_byte_mem_imm(VALS, lit_encoded as i32, 1);

        // vals[neg_lit] = 0xFF (-1 as i8)
        self.mov_byte_mem_imm(VALS, neg_lit as i32, 0xFF);
    }

    /// Emit enqueue of a runtime literal (in register `lit_reg`) with
    /// a compile-time clause_id. Uses T0-T1 as scratch.
    /// Caller must ensure lit_reg is not T0 or T1.
    pub fn emit_enqueue_runtime(&mut self, lit_reg: Reg, clause_id: u32) {
        debug_assert!(lit_reg != T0 && lit_reg != T1, "lit_reg must not be T0 or T1");

        // trail[trail_len] = lit_reg
        self.mov_mem_indexed_r32(TRAIL, TRAIL_LEN, lit_reg);

        // trail_len++
        self.add_r32_imm(TRAIL_LEN, 1);
        self.mov_mem_r32(TRAIL_LEN_PTR, 0, TRAIL_LEN);

        // reasons[var(lit)] = clause_id; var = lit >> 1
        self.mov_r32(T0, lit_reg);
        self.shr_r32_imm(T0, 1);       // T0 = var
        self.mov_r32_imm(T1, clause_id);
        self.mov_mem_indexed_r32(REASONS, T0, T1);

        // vals[lit] = 1
        self.mov_byte_indexed_imm(VALS, lit_reg, 1);

        // vals[lit ^ 1] = 0xFF (-1)
        self.mov_r32(T0, lit_reg);
        self.xor_r32_imm(T0, 1);       // T0 = lit ^ 1
        self.mov_byte_indexed_imm(VALS, T0, 0xFF);
    }

    /// Emit conflict: store clause_id to *conflict_ptr, return 1.
    pub fn emit_conflict(&mut self, clause_id: u32) {
        // Load conflict pointer from context.
        self.mov_r64_mem(T0, CTX, crate::context::OFFSET_CONFLICT);
        self.mov_r32_imm(T1, clause_id);
        self.mov_mem_r32(T0, 0, T1);
        // return 1
        self.mov_r32_imm(RAX, 1);
        self.epilogue();
    }

    /// LSR equivalent.
    pub fn lsr_w_imm(&mut self, rd: Reg, rn: Reg, shift: u32) {
        if rd != rn {
            self.mov_r32(rd, rn);
        }
        self.shr_r32_imm(rd, shift as u8);
    }

    /// EOR equivalent.
    pub fn eor_w_reg(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        if rd != rn {
            self.mov_r32(rd, rn);
        }
        self.xor_r32_r32(rd, rm);
    }

    /// STR Wt, [Xn, #0] equivalent — write r32 to memory at base.
    pub fn str_w_uimm(&mut self, rt: Reg, rn: Reg, _offset: u32) {
        self.mov_mem_r32(rn, 0, rt);
    }

    /// STR Wt, [Xn, Xm, LSL #2] equivalent — write r32 with scaled index.
    pub fn str_w_reg_lsl2(&mut self, rt: Reg, rn: Reg, rm: Reg) {
        self.mov_mem_indexed_r32(rn, rm, rt);
    }

    /// STRB byte store via register offset.
    pub fn strb_w_reg(&mut self, rt: Reg, rn: Reg, rm: Reg) {
        self.mov_byte_indexed_r8(rn, rm, rt);
    }

    /// STRB byte store via immediate offset.
    ///
    /// NOTE: Currently dead code on x86_64 — the x86_64 `emit_enqueue_const`
    /// uses `mov_byte_mem_imm` (immediate store) instead of this register-based
    /// path. If this function is ever used, the REX prefix logic needs fixing
    /// for byte-register access: registers 4-7 (RSP/RBP/RSI/RDI) encode as
    /// AH/CH/DH/BH in byte ops without REX, but SPL/BPL/SIL/DIL with REX.
    /// The current `emit_rex_if_needed` omits REX for registers 0-7, which
    /// would produce incorrect byte stores for rt in {4,5,6,7}.
    pub fn strb_w_uimm(&mut self, rt: Reg, rn: Reg, offset: u32) {
        // For byte stores with constant 1, we can use mov byte [rn+offset], imm8
        // But rt contains the value. We need to store the byte from rt.
        // On x86_64, we need a REX prefix to access the low byte of any register.
        self.emit_rex_if_needed(false, rt, rn);
        self.emit_byte(0x88); // MOV r/m8, r8
        if (rn.0 & 7) == 4 {
            self.emit_byte(Self::modrm_disp32(rt, rn));
            self.emit_byte(Self::sib(1, Reg(4), rn));
        } else {
            self.emit_byte(Self::modrm_disp32(rt, rn));
        }
        self.emit_i32_le(offset as i32);
    }

    /// LDR Xt, [Xn, #imm] equivalent — 64-bit load from context.
    pub fn ldr_x_uimm(&mut self, rt: Reg, rn: Reg, offset: u32) {
        self.mov_r64_mem(rt, rn, offset as i32);
    }

    /// LDR Wt, [Xn, #0] equivalent — 32-bit load.
    pub fn ldr_w_uimm(&mut self, rt: Reg, rn: Reg, _offset: u32) {
        self.mov_r32_mem(rt, rn, 0);
    }
}
