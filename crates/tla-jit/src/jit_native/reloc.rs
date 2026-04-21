// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Vendored from cranelift-jit 0.112.3, src/compiled_blob.rs
// Original: Copyright (c) Bytecode Alliance. Apache-2.0 WITH LLVM-exception.
// Modified: Stripped s390x/riscv64/pulley relocations. Kept aarch64 + x86-64.

use cranelift_codegen::binemit::Reloc;

use super::{ModuleReloc, ModuleRelocTarget};

/// Reads a 32-bit instruction at `iptr`, modifies it, and writes it back.
unsafe fn modify_inst32(iptr: *mut u32, modifier: impl FnOnce(u32) -> u32) {
    let inst = iptr.read_unaligned();
    let new_inst = modifier(inst);
    iptr.write_unaligned(new_inst);
}

#[derive(Clone)]
pub(crate) struct CompiledBlob {
    pub(crate) ptr: *mut u8,
    pub(crate) size: usize,
    pub(crate) relocs: Vec<ModuleReloc>,
}

unsafe impl Send for CompiledBlob {}

impl CompiledBlob {
    pub(crate) fn perform_relocations(
        &self,
        get_address: impl Fn(&ModuleRelocTarget) -> *const u8,
        get_got_entry: impl Fn(&ModuleRelocTarget) -> *const u8,
        _get_plt_entry: impl Fn(&ModuleRelocTarget) -> *const u8,
    ) {
        use std::ptr::write_unaligned;

        for &ModuleReloc {
            kind,
            offset,
            ref name,
            addend,
        } in &self.relocs
        {
            debug_assert!((offset as usize) < self.size);
            let at = unsafe { self.ptr.offset(isize::try_from(offset).unwrap()) };
            match kind {
                // --- Absolute relocations ---
                Reloc::Abs4 => {
                    let base = get_address(name);
                    let what = unsafe { base.offset(isize::try_from(addend).unwrap()) };
                    unsafe {
                        write_unaligned(at as *mut u32, u32::try_from(what as usize).unwrap())
                    };
                }
                Reloc::Abs8 => {
                    let base = get_address(name);
                    let what = unsafe { base.offset(isize::try_from(addend).unwrap()) };
                    unsafe {
                        write_unaligned(at as *mut u64, u64::try_from(what as usize).unwrap())
                    };
                }

                // --- x86-64 PC-relative ---
                Reloc::X86PCRel4 | Reloc::X86CallPCRel4 => {
                    let base = get_address(name);
                    let what = unsafe { base.offset(isize::try_from(addend).unwrap()) };
                    let pcrel = i32::try_from((what as isize) - (at as isize)).unwrap();
                    unsafe { write_unaligned(at as *mut i32, pcrel) };
                }
                Reloc::X86GOTPCRel4 => {
                    let base = get_got_entry(name);
                    let what = unsafe { base.offset(isize::try_from(addend).unwrap()) };
                    let pcrel = i32::try_from((what as isize) - (at as isize)).unwrap();
                    unsafe { write_unaligned(at as *mut i32, pcrel) };
                }
                Reloc::X86CallPLTRel4 => {
                    // In non-PIC mode we resolve PLT calls directly to the target.
                    let base = get_address(name);
                    let what = unsafe { base.offset(isize::try_from(addend).unwrap()) };
                    let pcrel = i32::try_from((what as isize) - (at as isize)).unwrap();
                    unsafe { write_unaligned(at as *mut i32, pcrel) };
                }

                // --- aarch64 ---
                Reloc::Arm64Call => {
                    let base = get_address(name);
                    let iptr = at as *mut u32;
                    // The offset encoded in `bl` is the byte distance divided by 4.
                    let diff = ((base as isize) - (at as isize)) >> 2;
                    // Verify the offset fits in the signed 26-bit immediate.
                    assert!(
                        (diff >> 26 == -1) || (diff >> 26 == 0),
                        "Arm64Call relocation out of range: target is {diff} instructions away \
                         (max ±33554432). This means JIT code and runtime helpers are too far apart \
                         in memory."
                    );
                    let chop = 32 - 26;
                    let imm26 = (diff as u32) << chop >> chop;
                    unsafe { modify_inst32(iptr, |inst| inst | imm26) };
                }
                Reloc::Aarch64AdrGotPage21 => {
                    // Set ADRP immediate to bits [32:12] of the GOT entry page offset.
                    assert_eq!(addend, 0, "addend must be 0 for Aarch64AdrGotPage21");
                    let what = get_got_entry(name);
                    let what_page = (what as usize) & !0xfff;
                    let at_page = (at as usize) & !0xfff;
                    let pcrel = (what_page as isize).checked_sub(at_page as isize).unwrap();
                    assert!(
                        (-1i64 << 32) <= pcrel as i64 && (pcrel as i64) < (1i64 << 32),
                        "can't reach GOT page with ±4GB `adrp` instruction"
                    );
                    let val = pcrel >> 12;
                    let immlo = ((val as u32) & 0b11) << 29;
                    let immhi = (((val as u32) >> 2) & 0x7ffff) << 5;
                    let mask = !((0x7ffff << 5) | (0b11 << 29));
                    unsafe { modify_inst32(at as *mut u32, |adrp| (adrp & mask) | immlo | immhi) };
                }
                Reloc::Aarch64Ld64GotLo12Nc => {
                    // Set LD/ST immediate field to bits 11:3 of the GOT entry address.
                    assert_eq!(addend, 0);
                    let base = get_got_entry(name);
                    let what = base as u32;
                    assert_eq!(what & 0b111, 0, "GOT entry not 8-byte aligned");
                    let val = what >> 3;
                    let imm9 = (val & 0x1ff) << 10;
                    let mask = !(0x1ff << 10);
                    unsafe { modify_inst32(at as *mut u32, |ldr| (ldr & mask) | imm9) };
                }

                other => {
                    panic!(
                        "unsupported relocation type {other:?} — only x86-64 and aarch64 \
                         relocations are supported by the vendored JIT backend"
                    );
                }
            }
        }
    }
}
