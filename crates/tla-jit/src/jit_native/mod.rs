// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Vendored and optimized Cranelift JIT backend.
//!
//! Forked from `cranelift-jit` 0.112.3 and `cranelift-module` 0.112.3.
//!
//! ## What changed
//!
//! - **Dropped `unwind` feature** on cranelift-codegen → removes gimli (~48K LOC).
//! - **Dropped `region` crate** → direct `libc::mprotect` / `libc::mmap`.
//! - **Dropped `wasmtime-jit-icache-coherence`** → direct `sys_icache_invalidate` / `__clear_cache`.
//! - **Dropped `cranelift-native`** → inlined host ISA detection (trivial).
//! - **Dropped `cranelift-control`** → use `cranelift_codegen::control::ControlPlane` re-export.
//! - **Removed:** Windows, SELinux, hotswap, PLT/GOT, perf map, s390x/riscv64/pulley relocs.
//! - **Removed:** Data object support (never used by tla-jit).
//!
//! ## What's kept
//!
//! - Full `Module` trait with `declare_function`, `define_function`, `finalize_definitions`.
//! - Symbol resolution: internal table + `dlsym` fallback.
//! - Relocation patching: aarch64 (`Arm64Call`, `AdrGotPage21`, `Ld64GotLo12Nc`) + x86-64 (`PCRel4`, `CallPCRel4`, `GOTPCRel4`, `CallPLTRel4`, `Abs4`, `Abs8`).
//! - Memory management: bump allocator with `mprotect` RW→RX transition.
//! - icache coherence: `sys_icache_invalidate` (macOS) / `__clear_cache` (Linux) / no-op (x86-64).
//!
//! Original Cranelift source: <https://github.com/bytecodealliance/wasmtime>
//! License: Apache-2.0 WITH LLVM-exception

mod backend;
mod data_context;
mod memory;
mod module_types;
mod reloc;

pub use backend::{JITBuilder, JITModule};
pub use data_context::{DataDescription, Init};
pub use module_types::{
    DataDeclaration, DataId, FuncId, FuncOrDataId, FunctionDeclaration, Linkage, Module,
    ModuleDeclarations, ModuleError, ModuleReloc, ModuleRelocTarget, ModuleResult,
};

use cranelift_codegen::ir;

/// Default names for `ir::LibCall`s. Used when creating a `JITBuilder`.
pub fn default_libcall_names() -> Box<dyn Fn(ir::LibCall) -> String + Send + Sync> {
    Box::new(move |libcall| match libcall {
        ir::LibCall::Probestack => "__cranelift_probestack".to_string(),
        ir::LibCall::CeilF32 => "ceilf".to_string(),
        ir::LibCall::CeilF64 => "ceil".to_string(),
        ir::LibCall::FloorF32 => "floorf".to_string(),
        ir::LibCall::FloorF64 => "floor".to_string(),
        ir::LibCall::TruncF32 => "truncf".to_string(),
        ir::LibCall::TruncF64 => "trunc".to_string(),
        ir::LibCall::NearestF32 => "nearbyintf".to_string(),
        ir::LibCall::NearestF64 => "nearbyint".to_string(),
        ir::LibCall::FmaF32 => "fmaf".to_string(),
        ir::LibCall::FmaF64 => "fma".to_string(),
        ir::LibCall::Memcpy => "memcpy".to_string(),
        ir::LibCall::Memset => "memset".to_string(),
        ir::LibCall::Memmove => "memmove".to_string(),
        ir::LibCall::Memcmp => "memcmp".to_string(),
        ir::LibCall::ElfTlsGetAddr => "__tls_get_addr".to_string(),
        ir::LibCall::ElfTlsGetOffset => "__tls_get_offset".to_string(),
        ir::LibCall::X86Pshufb => "__cranelift_x86_pshufb".to_string(),
    })
}

/// Detect the host ISA and return an `isa::Builder` configured for it.
///
/// Inlined from `cranelift-native` 0.112.3. Supports aarch64 (macOS/Linux) and x86-64.
pub fn native_isa_builder() -> Result<cranelift_codegen::isa::Builder, &'static str> {
    use cranelift_codegen::isa;
    use cranelift_codegen::settings::Configurable;

    #[cfg(target_arch = "aarch64")]
    let mut isa_builder = isa::lookup_by_name("aarch64").map_err(|err| match err {
        isa::LookupError::SupportDisabled => "support for architecture disabled at compile time",
        isa::LookupError::Unsupported => "unsupported architecture",
    })?;
    #[cfg(target_arch = "x86_64")]
    let mut isa_builder = isa::lookup_by_name("x86_64").map_err(|err| match err {
        isa::LookupError::SupportDisabled => "support for architecture disabled at compile time",
        isa::LookupError::Unsupported => "unsupported architecture",
    })?;
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    return Err("unsupported architecture: only aarch64 and x86_64 are supported");

    #[cfg(target_arch = "x86_64")]
    {
        if !std::is_x86_feature_detected!("sse2") {
            return Err("x86 support requires SSE2");
        }
        if std::is_x86_feature_detected!("sse3") {
            isa_builder.enable("has_sse3").unwrap();
        }
        if std::is_x86_feature_detected!("ssse3") {
            isa_builder.enable("has_ssse3").unwrap();
        }
        if std::is_x86_feature_detected!("sse4.1") {
            isa_builder.enable("has_sse41").unwrap();
        }
        if std::is_x86_feature_detected!("sse4.2") {
            isa_builder.enable("has_sse42").unwrap();
        }
        if std::is_x86_feature_detected!("popcnt") {
            isa_builder.enable("has_popcnt").unwrap();
        }
        if std::is_x86_feature_detected!("avx") {
            isa_builder.enable("has_avx").unwrap();
        }
        if std::is_x86_feature_detected!("avx2") {
            isa_builder.enable("has_avx2").unwrap();
        }
        if std::is_x86_feature_detected!("fma") {
            isa_builder.enable("has_fma").unwrap();
        }
        if std::is_x86_feature_detected!("bmi1") {
            isa_builder.enable("has_bmi1").unwrap();
        }
        if std::is_x86_feature_detected!("bmi2") {
            isa_builder.enable("has_bmi2").unwrap();
        }
        if std::is_x86_feature_detected!("avx512bitalg") {
            isa_builder.enable("has_avx512bitalg").unwrap();
        }
        if std::is_x86_feature_detected!("avx512dq") {
            isa_builder.enable("has_avx512dq").unwrap();
        }
        if std::is_x86_feature_detected!("avx512f") {
            isa_builder.enable("has_avx512f").unwrap();
        }
        if std::is_x86_feature_detected!("avx512vl") {
            isa_builder.enable("has_avx512vl").unwrap();
        }
        if std::is_x86_feature_detected!("avx512vbmi") {
            isa_builder.enable("has_avx512vbmi").unwrap();
        }
        if std::is_x86_feature_detected!("lzcnt") {
            isa_builder.enable("has_lzcnt").unwrap();
        }
    }

    #[cfg(target_arch = "aarch64")]
    {
        if std::arch::is_aarch64_feature_detected!("lse") {
            isa_builder.enable("has_lse").unwrap();
        }
        if std::arch::is_aarch64_feature_detected!("paca") {
            isa_builder.enable("has_pauth").unwrap();
        }
        if std::arch::is_aarch64_feature_detected!("fp16") {
            isa_builder.enable("has_fp16").unwrap();
        }
        if cfg!(target_os = "macos") {
            // Pointer authentication is always available on Apple Silicon.
            isa_builder.enable("sign_return_address").unwrap();
            isa_builder.enable("sign_return_address_with_bkey").unwrap();
        }
    }

    Ok(isa_builder)
}
