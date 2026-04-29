// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Top-level compilation API: tMIR Module -> native code via LLVM2.
//!
//! This module provides the primary entry point for compiling a tMIR module
//! (produced by [`tla_tmir`]) into executable native code via the LLVM2
//! verified compiler backend. Zero C dependencies — everything is pure Rust.
//!
//! # Pipeline
//!
//! ```text
//! tmir::Module
//!     |
//!     v
//! validate_module()       -- structural checks
//!     |
//!     v
//! lower_module()          -- count instructions, emit LLVM IR text (debug)
//!     |
//!     v
//! translate_module()      -- tMIR -> llvm2_lower::Function (ISel input)
//!     |
//!     v
//! JitCompiler::compile_raw() -- ISel -> RegAlloc -> Encode -> JIT
//!     |
//!     v
//! NativeLibrary           -- executable memory with symbol lookup
//! ```
//!
//! # Optimization Levels
//!
//! [`OptLevel`] controls LLVM2 optimization when compiling to native code:
//! - **O1**: Fast compilation (~50-200ms). Used during interpreter warmup (Tier 1).
//! - **O3**: Peak throughput (~0.5-2s). Full optimization pipeline (Tier 2).

use crate::bfs_level::{
    ActionDescriptor, InvariantDescriptor, Llvm2BfsLevelNative, Llvm2BfsLevelNativeMetadata,
};
use crate::lower::{self, LoweringStats};
use crate::native_bfs::{
    build_native_bfs_level_module_with_state_constraints, NativeBfsInvariantTarget,
    NativeBfsStateConstraintTarget, LLVM2_BFS_LEVEL_NATIVE_SYMBOL,
};
use crate::Llvm2Error;
use tla_tir::bytecode::BytecodeChunk;
use tmir::Module;

#[cfg(feature = "native")]
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
#[cfg(feature = "native")]
use std::sync::{Arc, Mutex, OnceLock};

#[cfg(feature = "native")]
use crate::artifact_cache::{ArtifactCache, CacheKey};

const NATIVE_FUSED_ENABLE_LOCAL_DEDUP_ENV: &str = "TLA2_LLVM2_NATIVE_FUSED_ENABLE_LOCAL_DEDUP";
const NATIVE_FUSED_DISABLE_LOCAL_DEDUP_ENV: &str = "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP";
const NATIVE_DISABLE_POST_RA_OPT_ENV: &str = "TLA2_LLVM2_DISABLE_POST_RA_OPT";
#[cfg(feature = "native")]
const LLVM2_JIT_PC_MAP_ENV: &str = "TLA2_LLVM2_JIT_PC_MAP";

fn native_fused_local_dedup_enabled() -> bool {
    native_fused_local_dedup_enabled_for_env(
        std::env::var_os(NATIVE_FUSED_DISABLE_LOCAL_DEDUP_ENV).as_deref(),
        std::env::var_os(NATIVE_FUSED_ENABLE_LOCAL_DEDUP_ENV).as_deref(),
    )
}

fn native_fused_local_dedup_enabled_for_env(
    disable_env: Option<&std::ffi::OsStr>,
    enable_env: Option<&std::ffi::OsStr>,
) -> bool {
    if disable_env.is_some_and(env_flag_set) {
        return false;
    }
    enable_env.is_some_and(env_flag_set)
}

fn env_flag_set(value: &std::ffi::OsStr) -> bool {
    let value = value.to_string_lossy();
    let value = value.trim().to_ascii_lowercase();
    !matches!(value.as_str(), "0" | "false" | "no" | "off")
}

fn native_post_ra_opt_enabled(opt_level: OptLevel) -> bool {
    native_post_ra_opt_enabled_for_env(
        opt_level,
        std::env::var_os(NATIVE_DISABLE_POST_RA_OPT_ENV).as_deref(),
    )
}

fn native_post_ra_opt_enabled_for_env(
    opt_level: OptLevel,
    disable_env: Option<&std::ffi::OsStr>,
) -> bool {
    if opt_level == OptLevel::O1 {
        return false;
    }
    match disable_env {
        None => true,
        Some(value) => value == std::ffi::OsStr::new("0"),
    }
}

/// Optimization level for LLVM2 compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OptLevel {
    /// Fast compilation for warmup. Minimal optimization.
    O1,
    /// Peak throughput. Full optimization pipeline (DCE, GVN, LICM, unrolling).
    O3,
}

impl OptLevel {
    /// Stable short string used in cache keys and diagnostics. Keep these
    /// values stable — they feed into on-disk cache digests.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            OptLevel::O1 => "O1",
            OptLevel::O3 => "O3",
        }
    }
}

/// Explicit extern symbols supplied by a caller for native JIT linking.
///
/// The default [`compile_module_native`] path supplies only the built-in
/// runtime helpers. Modules that declare bodyless external call targets can add
/// those addresses through this overlay. The overlay is folded into the JIT
/// cache key by symbol name and pointer value so a module linked against one
/// set of native function addresses cannot be reused for another.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NativeExternSymbolOverlay {
    symbols: Vec<NativeExternSymbol>,
}

impl NativeExternSymbolOverlay {
    /// Create an empty overlay.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Build an overlay from `(symbol_name, address)` entries.
    ///
    /// Symbol names must be non-empty and addresses must be non-null. Duplicate
    /// names are rejected after deterministic sorting.
    pub fn from_symbols<I, S>(symbols: I) -> Result<Self, Llvm2Error>
    where
        I: IntoIterator<Item = (S, *const u8)>,
        S: Into<String>,
    {
        let mut overlay = Self::default();
        for (name, addr) in symbols {
            overlay.push(name, addr)?;
        }
        overlay.sort_and_validate_unique()?;
        Ok(overlay)
    }

    /// Add one symbol to this overlay.
    pub fn push(&mut self, name: impl Into<String>, addr: *const u8) -> Result<(), Llvm2Error> {
        let name = name.into();
        if name.is_empty() {
            return Err(Llvm2Error::Loading(
                "extern symbol overlay contains an empty symbol name".to_string(),
            ));
        }
        if addr.is_null() {
            return Err(Llvm2Error::Loading(format!(
                "extern symbol overlay entry '{name}' has a null address"
            )));
        }
        if self.symbols.iter().any(|symbol| symbol.name == name) {
            return Err(Llvm2Error::Loading(format!(
                "extern symbol overlay contains duplicate symbol '{name}'"
            )));
        }
        self.symbols.push(NativeExternSymbol { name, addr });
        self.sort_and_validate_unique()
    }

    /// Number of explicitly supplied symbols.
    #[must_use]
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Whether no symbols were supplied.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    /// Iterate over `(symbol_name, address)` entries in deterministic order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, *const u8)> {
        self.symbols
            .iter()
            .map(|symbol| (symbol.name.as_str(), symbol.addr))
    }

    fn sort_and_validate_unique(&mut self) -> Result<(), Llvm2Error> {
        self.symbols.sort_by(|a, b| a.name.cmp(&b.name));
        if let Some(duplicate) = self
            .symbols
            .windows(2)
            .find(|pair| pair[0].name == pair[1].name)
            .map(|pair| pair[0].name.clone())
        {
            return Err(Llvm2Error::Loading(format!(
                "extern symbol overlay contains duplicate symbol '{duplicate}'"
            )));
        }
        Ok(())
    }

    #[cfg(feature = "native")]
    fn cache_discriminator_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.symbols.len().saturating_mul(40));
        bytes.extend_from_slice(b"native-extern-symbol-overlay-v1\0");
        for symbol in &self.symbols {
            bytes.extend_from_slice(symbol.name.as_bytes());
            bytes.push(0);
            bytes.extend_from_slice(&(symbol.addr as usize).to_le_bytes());
            bytes.push(0);
        }
        bytes
    }

    #[cfg(feature = "native")]
    fn overlay_into(&self, extern_symbols: &mut HashMap<String, *const u8>) {
        for symbol in &self.symbols {
            extern_symbols.insert(symbol.name.clone(), symbol.addr);
            #[cfg(any(target_os = "macos", target_os = "ios"))]
            if !symbol.name.starts_with('_') {
                let alias = format!("_{}", symbol.name);
                if !self.symbols.iter().any(|explicit| explicit.name == alias) {
                    extern_symbols.insert(alias, symbol.addr);
                }
            }
        }
    }
}

/// One explicit native extern symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeExternSymbol {
    /// Symbol name as emitted by tMIR/LLVM2 lowering.
    pub name: String,
    /// Raw function/data address supplied to LLVM2 JIT linking.
    pub addr: *const u8,
}

/// Result of compiling a tMIR module to LLVM IR (and eventually native code).
///
/// Holds the emitted LLVM IR text and compilation statistics. The LLVM IR text
/// is retained for debugging and introspection; native compilation now goes
/// through the LLVM2 pipeline directly (bypassing text IR entirely).
#[derive(Debug)]
pub struct CompiledModule {
    /// Name of the source module.
    pub name: String,
    /// Lowering statistics.
    pub stats: LoweringStats,
    /// Emitted LLVM IR text (`.ll` format).
    ///
    /// Retained for debugging/introspection. The native compilation path
    /// (`compile_and_link`) bypasses this text entirely — it translates
    /// tMIR directly to LLVM2's internal representation.
    pub llvm_ir: String,
}

/// Check whether the LLVM2 native compilation backend is available.
///
/// Returns `true` when the `native` feature is enabled (LLVM2 is compiled-in).
/// Unlike the old llc/clang pipeline, this needs no system LLVM installation.
pub fn is_native_available() -> bool {
    cfg!(feature = "native")
}

/// Runtime flag for the LLVM2 entry-counter dispatch demonstration.
///
/// When set to a positive integer, native compilation emits LLVM2 function-entry
/// counters and TLA2's BFS dispatch can use those counters as a per-symbol
/// native-dispatch limit. Unset, empty, `0`, and unparsable values keep the
/// default zero-overhead path.
pub const LLVM2_ENTRY_COUNTER_DISPATCH_GATE_ENV: &str = "TLA2_LLVM2_ENTRY_COUNTER_GATE";

pub fn llvm2_entry_counter_dispatch_gate_limit() -> Option<u64> {
    let value = std::env::var(LLVM2_ENTRY_COUNTER_DISPATCH_GATE_ENV).ok()?;
    let value = value.trim();
    if value.is_empty() || value == "0" {
        return None;
    }
    value.parse::<u64>().ok().filter(|limit| *limit > 0)
}

fn llvm2_entry_counter_dispatch_gate_enabled() -> bool {
    llvm2_entry_counter_dispatch_gate_limit().is_some()
}

fn maybe_dump_tmir_on_failure(stage: &str, module: &Module, err: &Llvm2Error) {
    if std::env::var_os("TLA2_LLVM2_DUMP_TMIR_ON_FAILURE").is_none() {
        return;
    }
    eprintln!(
        "[llvm2][tmir-dump] stage={stage} module='{}' error={err}\n{module:#?}",
        module.name
    );
}

fn maybe_dump_tmir(stage: &str, module: &Module) {
    let Ok(value) = std::env::var("TLA2_LLVM2_DUMP_TMIR") else {
        return;
    };
    if should_dump_tmir(&value, &module.name) {
        eprintln!(
            "[llvm2][tmir-dump] stage={stage} module='{}'\n{module:#?}",
            module.name
        );
    }
}

fn should_dump_tmir(value: &str, module_name: &str) -> bool {
    let value = value.trim();
    !value.is_empty()
        && (value == "1"
            || value.eq_ignore_ascii_case("all")
            || module_name.contains(value)
            || value.split(',').any(|part| {
                let part = part.trim();
                !part.is_empty() && module_name.contains(part)
            }))
}

#[cfg(feature = "native")]
fn jit_pc_map_filter_matches(value: &str, module_name: &str, func_name: &str) -> bool {
    let value = value.trim();
    !value.is_empty()
        && (value == "1"
            || value.eq_ignore_ascii_case("all")
            || module_name.contains(value)
            || func_name.contains(value)
            || value.split(',').any(|part| {
                let part = part.trim();
                !part.is_empty() && (module_name.contains(part) || func_name.contains(part))
            }))
}

#[cfg(feature = "native")]
fn maybe_dump_jit_pc_map(
    module_name: &str,
    funcs: &[llvm2_ir::MachFunction],
    buffer: &llvm2_codegen::ExecutableBuffer,
) {
    let Ok(filter) = std::env::var(LLVM2_JIT_PC_MAP_ENV) else {
        return;
    };

    let symbol_offsets: HashMap<String, u64> = buffer
        .symbols()
        .map(|(name, offset)| (name.to_string(), offset))
        .collect();

    eprintln!(
        "[llvm2][jit-pc-map] module='{module_name}' allocated_size={} filter='{}'",
        buffer.allocated_size(),
        filter
    );

    for func in funcs {
        if !jit_pc_map_filter_matches(&filter, module_name, &func.name) {
            continue;
        }

        let symbol_offset = symbol_offsets.get(func.name.as_str()).copied();
        let runtime_start = buffer
            .get_fn_ptr_bound(&func.name)
            .map(|ptr| ptr.as_ptr() as usize);

        let (code, _fixups, block_offsets) =
            match llvm2_codegen::pipeline::encode_function_with_fixups_and_blocks(func) {
                Ok(encoded) => encoded,
                Err(err) => {
                    eprintln!(
                        "[llvm2][jit-pc-map] function='{}' encode_error={err}",
                        func.name
                    );
                    continue;
                }
            };

        eprintln!(
            "[llvm2][jit-pc-map] function='{}' symbol_offset={} runtime_start={} code_len={}",
            func.name,
            symbol_offset
                .map(|offset| format!("0x{offset:x}"))
                .unwrap_or_else(|| "none".to_string()),
            runtime_start
                .map(|addr| format!("0x{addr:x}"))
                .unwrap_or_else(|| "none".to_string()),
            code.len()
        );

        let mut sorted_blocks: Vec<_> = block_offsets.iter().collect();
        sorted_blocks.sort_by_key(|(_, offset)| **offset);
        for (block_id, offset) in sorted_blocks {
            let abs = runtime_start.map(|start| start.saturating_add(*offset as usize));
            eprintln!(
                "[llvm2][jit-pc-map]   block={block_id} offset=0x{offset:x} pc={}",
                abs.map(|addr| format!("0x{addr:x}"))
                    .unwrap_or_else(|| "none".to_string())
            );
        }

        for &block_id in &func.block_order {
            let Some(&block_start) = block_offsets.get(&block_id) else {
                continue;
            };
            let mut offset = block_start as usize;
            let block = func.block(block_id);
            for &inst_id in &block.insts {
                let inst = func.inst(inst_id);
                if inst.is_pseudo() {
                    continue;
                }

                let word = code
                    .get(offset..offset.saturating_add(4))
                    .and_then(|bytes| <[u8; 4]>::try_from(bytes).ok())
                    .map(u32::from_le_bytes);
                let abs = runtime_start.map(|start| start.saturating_add(offset));
                eprintln!(
                    "[llvm2][jit-pc-map]     offset=0x{offset:04x} pc={} block={block_id} inst={inst_id} word={} opcode={:?} operands={:?} source_loc={:?}",
                    abs.map(|addr| format!("0x{addr:x}"))
                        .unwrap_or_else(|| "none".to_string()),
                    word.map(|word| format!("0x{word:08x}"))
                        .unwrap_or_else(|| "none".to_string()),
                    inst.opcode,
                    inst.operands,
                    inst.source_loc
                );
                offset = offset.saturating_add(4);
            }
        }

        if code.len() > 0 {
            let last_inst_end = func
                .block_order
                .iter()
                .filter_map(|block_id| {
                    let block_start = *block_offsets.get(block_id)? as usize;
                    let emitted = func
                        .block(*block_id)
                        .insts
                        .iter()
                        .filter(|&&inst_id| !func.inst(inst_id).is_pseudo())
                        .count();
                    Some(block_start + emitted * 4)
                })
                .max()
                .unwrap_or(0);
            if last_inst_end < code.len() {
                eprintln!(
                    "[llvm2][jit-pc-map]     data_range offset=0x{last_inst_end:04x}..0x{:04x} bytes={}",
                    code.len(),
                    code.len() - last_inst_end
                );
            }
        }
    }
}

/// Legacy: locate system `llc` binary.
///
/// Retained for backwards compatibility / diagnostics. The native compilation
/// pipeline no longer uses `llc` — it goes through LLVM2 directly.
pub fn find_llc() -> Option<PathBuf> {
    use std::process::Command;
    if let Ok(output) = Command::new("which").arg("llc").output() {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return Some(PathBuf::from(path));
            }
        }
    }
    None
}

/// Compile a tMIR module to native code (deprecated text-based API).
///
/// This function previously invoked system `llc` and `clang`. It now returns
/// an error directing callers to use [`compile_module_native`] which goes
/// through LLVM2's pure-Rust pipeline directly.
///
/// Requires the `native` feature.
#[cfg(feature = "native")]
pub fn compile_and_link(
    _ir_text: &str,
    module_name: &str,
    _opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    Err(Llvm2Error::BackendUnavailable(format!(
        "compile_and_link() with raw IR text is deprecated. \
         Use compile_module_native() to compile a tMIR module directly \
         through LLVM2's native pipeline. Module: {module_name}"
    )))
}

/// Stub for when native feature is disabled.
#[cfg(not(feature = "native"))]
pub fn compile_and_link(
    _ir_text: &str,
    _module_name: &str,
    _opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    Err(Llvm2Error::BackendUnavailable(
        "LLVM2 native compilation requires the 'native' feature".to_string(),
    ))
}

/// Compile a tMIR module to native executable code via LLVM2.
///
/// This is the new primary API that replaces the old llc/clang pipeline.
/// It takes a tMIR module directly and produces a [`NativeLibrary`] backed
/// by LLVM2's in-memory JIT.
///
/// # Caching (design doc §7)
///
/// Wired into two layers of the artifact cache:
///
/// 1. **Process-local JIT cache.** The first call for a given
///    `(module, opt_level, target-triple)` pays the compilation cost;
///    subsequent calls return an [`Arc`]-shared executable buffer in
///    sub-microsecond time. This is the path that matters for BFS step
///    compilation — the same action's next-state / invariant functions
///    are invoked from several sites in one run.
/// 2. **On-disk observability sidecar** ([`crate::artifact_cache::ArtifactCache`]).
///    A metadata record (`<digest>.meta.json`, see [`store_on_disk_sidecar`])
///    is written per `(module, opt_level, target-triple)` the first
///    time we compile it so external tooling (`tla2 cache list`) can see
///    what the process has produced. Real `.dylib` / `.so` bytes are not
///    yet written because LLVM2's [`llvm2_codegen::ExecutableBuffer`]
///    does not expose a serialisable representation; when it does,
///    [`store_on_disk_sidecar`] is the one place to extend.
///
/// `TLA2_DISABLE_ARTIFACT_CACHE=1` suppresses both layers, forcing a
/// fresh compile. See [`clear_jit_cache`] for programmatic flushing in
/// tests / benchmarks.
///
/// # Arguments
///
/// * `module` - A tMIR module produced by [`tla_tmir::lower`].
/// * `opt_level` - Optimization level for the LLVM2 pipeline.
///
/// # Errors
///
/// Returns [`Llvm2Error::CodeGen`] if any compilation phase fails.
/// Returns [`Llvm2Error::BackendUnavailable`] if the `native` feature is disabled.
#[cfg(feature = "native")]
pub fn compile_module_native(
    module: &Module,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    compile_module_native_with_extern_symbols(
        module,
        opt_level,
        &NativeExternSymbolOverlay::empty(),
    )
}

/// Compile a tMIR module with an explicit extern symbol overlay.
///
/// Overlay entries are merged on top of the built-in LLVM2 runtime helper map
/// before JIT linking. The overlay identity is part of the process-local cache
/// key, including raw pointer values, because LLVM2 patches external call
/// addresses into the generated machine code.
///
/// Callers must keep the owners of every overlay address alive for at least as
/// long as the returned [`NativeLibrary`] can execute code that calls them.
#[cfg(feature = "native")]
pub fn compile_module_native_with_extern_symbols(
    module: &Module,
    opt_level: OptLevel,
    extern_overlay: &NativeExternSymbolOverlay,
) -> Result<NativeLibrary, Llvm2Error> {
    // Deterministic key once; reused for both cache layers.
    let cache_key = native_cache_key(module, opt_level, extern_overlay);
    let cache_disabled = std::env::var_os("TLA2_DISABLE_ARTIFACT_CACHE").is_some();

    // Layer 1: in-process JIT cache.
    if !cache_disabled {
        if let Some(hit) = jit_cache_lookup(&cache_key) {
            return Ok(NativeLibrary {
                buffer: hit,
                name: module.name.clone(),
            });
        }
    }

    // Miss → run the real compilation pipeline.
    let buffer = match compile_module_native_uncached(module, opt_level, extern_overlay) {
        Ok(buffer) => buffer,
        Err(err) => {
            maybe_dump_tmir_on_failure("compile_module_native", module, &err);
            return Err(err);
        }
    };
    let shared = Arc::new(buffer);

    // Layer 2: on-disk observability sidecar. Non-fatal on error.
    if !cache_disabled {
        store_on_disk_sidecar(&cache_key);
        jit_cache_store(&cache_key, Arc::clone(&shared));
    }

    Ok(NativeLibrary {
        buffer: shared,
        name: module.name.clone(),
    })
}

/// Uncached compilation path — factored out so [`compile_module_native`]
/// can wrap it with cache lookup/store without duplicating pipeline setup.
#[cfg(feature = "native")]
fn compile_module_native_uncached(
    module: &Module,
    opt_level: OptLevel,
    extern_overlay: &NativeExternSymbolOverlay,
) -> Result<llvm2_codegen::ExecutableBuffer, Llvm2Error> {
    use llvm2_codegen::jit::{JitCompiler, JitConfig};
    use llvm2_codegen::pipeline::OptLevel as Llvm2OptLevel;
    use llvm2_lower::adapter::translate_module;

    // Run module-level passes on a local clone. See [`compile_module`]
    // for rationale — the native path mirrors the text path so the
    // prefetch pass runs on every production compile.
    let mut working = module.clone();
    run_module_passes(&mut working);
    maybe_dump_tmir("compile_module_native", &working);

    // Phase 1: Translate tMIR -> llvm2_lower::Function (ISel input format).
    let mut functions_with_proofs = translate_module(&working)
        .map_err(|e| Llvm2Error::CodeGen(format!("tMIR -> LLVM2 adapter failed: {e}")))?;
    seed_native_lir_value_types(&mut functions_with_proofs);
    filter_bodyless_external_declarations(&working, &mut functions_with_proofs);

    if functions_with_proofs.is_empty() {
        return Err(Llvm2Error::CodeGen(
            "module contains no functions to compile".to_string(),
        ));
    }

    // Phase 2: Run each function through LLVM2's full pipeline (ISel -> RegAlloc
    // -> Frame Lowering -> AArch64 Encoding) to get MachFunctions.
    let llvm2_opt = match opt_level {
        OptLevel::O1 => Llvm2OptLevel::O1,
        OptLevel::O3 => Llvm2OptLevel::O3,
    };

    let config = JitConfig {
        opt_level: llvm2_opt,
        verify: false,
        emit_entry_counters: llvm2_entry_counter_dispatch_gate_enabled(),
        ..JitConfig::default()
    };
    let jit = JitCompiler::new(config);

    // Compile each function through the pipeline to get post-regalloc IR.
    //
    // NOTE: We opt into the struct-update syntax (`..Default::default()`) so
    // forward-compatible additions to `PipelineConfig` (e.g. LLVM2#395's
    // `target_triple` CEGIS cache key) pick up the upstream-blessed default
    // without requiring a simultaneous TLA2 edit. The fields we override
    // above encode TLA2's ABI contract; anything else stays on the default
    // path until we have a reason to diverge.
    let pipeline = llvm2_codegen::Pipeline::new(llvm2_codegen::PipelineConfig {
        opt_level: llvm2_opt,
        emit_debug: false,
        verify_dispatch: llvm2_codegen::DispatchVerifyMode::Off,
        verify: false,
        target_triple: target_triple_static().to_owned(),
        enable_post_ra_opt: native_post_ra_opt_enabled(opt_level),
        use_pressure_aware_scheduler: matches!(opt_level, OptLevel::O3),
        // CEGIS superoptimiser pass (LLVM2#395) — off by default. Turning
        // it on would gate native compilation on a budgeted SMT-driven
        // pass; we defer enabling until we have a need and a latency
        // budget to match.
        cegis_superopt_budget_sec: None,
        ..Default::default()
    });

    let mut ir_functions = Vec::new();
    for (func, proof_ctx) in &functions_with_proofs {
        let ir_func = pipeline
            .prepare_function_with_proofs(func, Some(proof_ctx))
            .map_err(|e| {
                Llvm2Error::CodeGen(format!("LLVM2 pipeline failed for '{}': {e}", func.name))
            })?;
        ir_functions.push(ir_func);
    }

    // Phase 3: JIT-compile all functions to executable memory.
    // Provide runtime helper addresses for extern symbol resolution.
    let mut extern_symbols = build_extern_symbol_map();
    extern_overlay.overlay_into(&mut extern_symbols);

    let buffer = jit
        .compile_raw(&ir_functions, &extern_symbols)
        .map_err(|e| Llvm2Error::CodeGen(format!("LLVM2 JIT compilation failed: {e}")))?;
    maybe_dump_jit_pc_map(&working.name, &ir_functions, &buffer);

    Ok(buffer)
}

#[cfg(feature = "native")]
fn bodyless_external_declaration_names(module: &Module) -> HashSet<String> {
    module
        .functions
        .iter()
        .filter(|func| func.blocks.is_empty() && matches!(func.linkage, tmir::Linkage::External))
        .map(|func| func.name.clone())
        .collect()
}

#[cfg(feature = "native")]
fn filter_bodyless_external_declarations(
    module: &Module,
    functions_with_proofs: &mut Vec<(llvm2_lower::Function, llvm2_lower::adapter::ProofContext)>,
) {
    let declarations = bodyless_external_declaration_names(module);
    if declarations.is_empty() {
        return;
    }
    functions_with_proofs.retain(|(func, _)| !declarations.contains(func.name.as_str()));
}

#[cfg(feature = "native")]
fn seed_native_lir_value_types(
    functions_with_proofs: &mut [(llvm2_lower::Function, llvm2_lower::adapter::ProofContext)],
) {
    for (func, _) in functions_with_proofs {
        seed_native_lir_function_value_types(func);
    }
}

#[cfg(feature = "native")]
fn seed_native_lir_function_value_types(func: &mut llvm2_lower::Function) {
    use llvm2_lower::instructions::Value;

    let mut types = func.value_types.clone();
    for (idx, ty) in func.signature.params.iter().enumerate() {
        types.entry(Value(idx as u32)).or_insert_with(|| ty.clone());
    }
    for block in func.blocks.values() {
        for (value, ty) in &block.params {
            types.entry(*value).or_insert_with(|| ty.clone());
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in func.blocks.values() {
            for inst in &block.instructions {
                for (value, ty) in infer_native_lir_instruction_value_types(inst, &types) {
                    if types.get(&value) != Some(&ty) {
                        types.insert(value, ty);
                        changed = true;
                    }
                }
            }
        }
    }

    func.value_types = types;
}

#[cfg(feature = "native")]
fn infer_native_lir_instruction_value_types(
    inst: &llvm2_lower::instructions::Instruction,
    types: &std::collections::HashMap<llvm2_lower::instructions::Value, llvm2_lower::Type>,
) -> Vec<(llvm2_lower::instructions::Value, llvm2_lower::Type)> {
    use llvm2_lower::instructions::Opcode;
    use llvm2_lower::Type;

    let Some(result) = inst.results.first().copied() else {
        return Vec::new();
    };

    let first_arg_ty = || inst.args.first().and_then(|arg| types.get(arg)).cloned();
    let typed_result = |ty: Type| vec![(result, ty)];

    match &inst.opcode {
        Opcode::Iconst { ty, .. } | Opcode::Fconst { ty, .. } => typed_result(ty.clone()),
        Opcode::Load { ty } | Opcode::AtomicLoad { ty, .. } | Opcode::AtomicRmw { ty, .. } => {
            typed_result(ty.clone())
        }
        Opcode::CmpXchg { ty, .. } => {
            let mut out = typed_result(ty.clone());
            if let Some(success) = inst.results.get(1).copied() {
                out.push((success, Type::B1));
            }
            out
        }
        Opcode::Sextend { to_ty, .. }
        | Opcode::Uextend { to_ty, .. }
        | Opcode::Trunc { to_ty }
        | Opcode::Bitcast { to_ty }
        | Opcode::FcvtToInt { dst_ty: to_ty }
        | Opcode::FcvtToUint { dst_ty: to_ty } => typed_result(to_ty.clone()),
        Opcode::Icmp { .. } | Opcode::Fcmp { .. } => typed_result(Type::B1),
        Opcode::CheckedSadd
        | Opcode::CheckedSsub
        | Opcode::CheckedSmul
        | Opcode::CheckedUadd
        | Opcode::CheckedUsub
        | Opcode::CheckedUmul => {
            let mut out = Vec::new();
            if let Some(ty) = first_arg_ty() {
                out.push((result, ty));
            }
            if let Some(overflow) = inst.results.get(1).copied() {
                out.push((overflow, Type::B1));
            }
            out
        }
        Opcode::GlobalRef { .. }
        | Opcode::ExternRef { .. }
        | Opcode::TlsRef { .. }
        | Opcode::StackAddr { .. }
        | Opcode::StructGep { .. }
        | Opcode::ArrayGep { .. }
        | Opcode::LandingPad { .. } => typed_result(Type::I64),
        Opcode::Iadd | Opcode::Isub | Opcode::Imul => {
            let Some(lhs_ty) = inst.args.first().and_then(|arg| types.get(arg)).cloned() else {
                return Vec::new();
            };
            let Some(rhs_ty) = inst.args.get(1).and_then(|arg| types.get(arg)).cloned() else {
                return Vec::new();
            };
            typed_result(native_lir_integer_binop_result_type(&lhs_ty, &rhs_ty))
        }
        Opcode::Copy
        | Opcode::Udiv
        | Opcode::Sdiv
        | Opcode::Urem
        | Opcode::Srem
        | Opcode::Ineg
        | Opcode::Bnot
        | Opcode::Ishl
        | Opcode::Ushr
        | Opcode::Sshr
        | Opcode::Band
        | Opcode::Bor
        | Opcode::Bxor
        | Opcode::BandNot
        | Opcode::BorNot
        | Opcode::Fadd
        | Opcode::Fsub
        | Opcode::Fmul
        | Opcode::Fdiv
        | Opcode::Fneg
        | Opcode::Fabs
        | Opcode::Fsqrt
        | Opcode::ExtractBits { .. }
        | Opcode::SextractBits { .. }
        | Opcode::InsertBits { .. } => first_arg_ty().map(typed_result).unwrap_or_default(),
        Opcode::Select { .. } => inst
            .args
            .get(1)
            .and_then(|arg| types.get(arg))
            .cloned()
            .map(typed_result)
            .unwrap_or_default(),
        _ => Vec::new(),
    }
}

#[cfg(feature = "native")]
fn native_lir_integer_binop_result_type(
    lhs: &llvm2_lower::Type,
    rhs: &llvm2_lower::Type,
) -> llvm2_lower::Type {
    use llvm2_lower::Type;

    if (native_lir_is_int32ish(lhs) && matches!(rhs, Type::I64))
        || (matches!(lhs, Type::I64) && native_lir_is_int32ish(rhs))
    {
        Type::I64
    } else {
        lhs.clone()
    }
}

#[cfg(feature = "native")]
fn native_lir_is_int32ish(ty: &llvm2_lower::Type) -> bool {
    matches!(
        ty,
        llvm2_lower::Type::B1
            | llvm2_lower::Type::I8
            | llvm2_lower::Type::I16
            | llvm2_lower::Type::I32
    )
}

/// Stub for when native feature is disabled.
#[cfg(not(feature = "native"))]
pub fn compile_module_native(
    _module: &Module,
    _opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    Err(Llvm2Error::BackendUnavailable(
        "LLVM2 native compilation requires the 'native' feature".to_string(),
    ))
}

/// Stub for when native feature is disabled.
#[cfg(not(feature = "native"))]
pub fn compile_module_native_with_extern_symbols(
    _module: &Module,
    _opt_level: OptLevel,
    _extern_overlay: &NativeExternSymbolOverlay,
) -> Result<NativeLibrary, Llvm2Error> {
    Err(Llvm2Error::BackendUnavailable(
        "LLVM2 native compilation requires the 'native' feature".to_string(),
    ))
}

// =============================================================================
// Artifact cache wiring (design doc §7)
// =============================================================================

/// Return the target triple baked into this build.
///
/// This is constant per-binary — compilation is always for the host we're
/// running on — so making it a `'static` string keeps the cache key
/// construction free of allocation. When LLVM2 grows cross-compilation
/// support this becomes a pipeline parameter.
#[cfg(feature = "native")]
fn target_triple_static() -> &'static str {
    // Match the triples rustc reports for the supported LLVM2 hosts.
    // We do not yet cross-compile; callers pass this to `CacheKey` so it
    // must differ across hosts to prevent cross-host cache pollution.
    if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        "aarch64-apple-darwin"
    } else if cfg!(all(target_os = "macos", target_arch = "x86_64")) {
        "x86_64-apple-darwin"
    } else if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
        "aarch64-unknown-linux-gnu"
    } else if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        "x86_64-unknown-linux-gnu"
    } else if cfg!(all(target_os = "windows", target_arch = "x86_64")) {
        "x86_64-pc-windows-msvc"
    } else {
        // Unknown host — use a stable sentinel so cache keys remain
        // deterministic but do not collide with a supported host's entries.
        "unknown-host"
    }
}

#[cfg(feature = "native")]
fn native_cache_key(
    module: &Module,
    opt_level: OptLevel,
    extern_overlay: &NativeExternSymbolOverlay,
) -> CacheKey {
    let mut discriminator = if extern_overlay.is_empty() {
        Vec::new()
    } else {
        extern_overlay.cache_discriminator_bytes()
    };
    if llvm2_entry_counter_dispatch_gate_enabled() {
        discriminator.extend_from_slice(b"llvm2-entry-counters-v1\0");
    }

    if discriminator.is_empty() {
        CacheKey::for_module(module, opt_level.as_str(), target_triple_static())
    } else {
        CacheKey::for_module_with_discriminator(
            module,
            opt_level.as_str(),
            target_triple_static(),
            &discriminator,
        )
    }
}

/// Process-local JIT cache. Keyed by [`CacheKey::digest_hex`] so two
/// callers with the same tMIR+opt+target tuple hit the same entry without
/// recompiling.
///
/// Using `OnceLock<Mutex<HashMap<...>>>` instead of `lazy_static`/`once_cell`
/// keeps the dependency surface minimal and works in const contexts if we
/// ever need a `pub const` handle.
#[cfg(feature = "native")]
fn jit_cache() -> &'static Mutex<HashMap<String, Arc<llvm2_codegen::ExecutableBuffer>>> {
    static CACHE: OnceLock<Mutex<HashMap<String, Arc<llvm2_codegen::ExecutableBuffer>>>> =
        OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Look up a cached executable buffer by key. `None` on miss.
#[cfg(feature = "native")]
fn jit_cache_lookup(key: &CacheKey) -> Option<Arc<llvm2_codegen::ExecutableBuffer>> {
    let guard = jit_cache().lock().ok()?;
    guard.get(&key.digest_hex).cloned()
}

/// Insert a compiled buffer into the process-local cache.
#[cfg(feature = "native")]
fn jit_cache_store(key: &CacheKey, buffer: Arc<llvm2_codegen::ExecutableBuffer>) {
    if let Ok(mut guard) = jit_cache().lock() {
        guard.insert(key.digest_hex.clone(), buffer);
    }
}

/// Drop every entry from the process-local JIT cache. Intended for tests
/// and benchmarks that need a clean slate between runs — production code
/// should rely on `TLA2_DISABLE_ARTIFACT_CACHE=1` instead.
#[cfg(feature = "native")]
pub fn clear_jit_cache() {
    if let Ok(mut guard) = jit_cache().lock() {
        guard.clear();
    }
}

/// Write the on-disk observability sidecar for `key`. Non-fatal on error
/// — a failure to persist the sidecar never blocks compilation, it only
/// means `tla2 cache list` won't see this entry.
///
/// LLVM2 `ExecutableBuffer` does not expose a serialisable byte
/// representation yet (see `llvm2-codegen/src/jit.rs`). Until it does we
/// write a zero-byte placeholder artifact alongside the metadata record
/// so existing cache-listing tooling continues to see the entry. When the
/// upstream serializer lands, swap the placeholder for real machine code.
#[cfg(feature = "native")]
fn store_on_disk_sidecar(key: &CacheKey) {
    // Best-effort: any error here is silently ignored. The in-process
    // cache is still populated; on-disk is observability-only today.
    let Ok(cache) = ArtifactCache::open_default() else {
        return;
    };
    // Empty placeholder keeps the atomic-write path exercised end-to-end
    // and prevents list_entries from silently skipping this hash.
    let _ = cache.store(key, &[], None);
}

/// Build the extern symbol map for JIT linking.
///
/// Populates `(symbol_name -> function_pointer)` for every runtime helper
/// referenced by LLVM2-compiled IR. Pointers are taken directly from each
/// helper's `#[no_mangle] pub extern "C" fn` site (no `dlsym`, no libc).
/// On Mach-O targets we also insert an `_`-prefixed alias because Mach-O
/// symbol lookups go through the underscored C-ABI name.
///
/// Two helper families are registered, each in its own function:
///
/// - [`register_jit_symbols`] — `jit_*` helpers (Fixes #4314). Covers the
///   compound/scalar ops and xxh3 fingerprint entries declared in
///   [`crate::runtime::RUNTIME_HELPERS`]. Resolution is fail-fast: the
///   registration panics if any declared helper is missing.
/// - [`register_tla_ops_symbols`] — handle-based `tla_*` helpers
///   (Part of #4318, R27 Option B).
///
/// Keeping the two tables separate is intentional — if one regresses,
/// the other surface still resolves cleanly.
#[cfg(feature = "native")]
fn build_extern_symbol_map() -> HashMap<String, *const u8> {
    let mut symbols = HashMap::new();
    register_jit_symbols(&mut symbols);
    register_tla_ops_symbols(&mut symbols);
    register_fp_symbols(&mut symbols);

    // Fail-fast: verify every declared runtime helper has an entry in the
    // combined compile-time table. A missing helper would silently leave the
    // JIT with an unresolvable extern at compile time (#4314/#4318).
    for helper in crate::runtime::RUNTIME_HELPERS {
        assert!(
            symbols.contains_key(helper.symbol),
            "runtime helper '{}' declared in RUNTIME_HELPERS is missing from \
             build_extern_symbol_map's compile-time tables (see #4314/#4318)",
            helper.symbol,
        );
    }

    symbols
}

/// Register the `jit_*` runtime helper family (Fixes #4314).
///
/// Inserts `(symbol_name -> function_pointer)` for every helper declared in
/// [`crate::runtime::RUNTIME_HELPERS`] so that LLVM2-compiled IR can resolve
/// extern calls via [`llvm2_codegen::jit::JitCompiler::compile_raw`].
/// Without this, any compiled action whose lowered tMIR emits a
/// `Call @jit_*` reference (set / record / seq / func operators, xxh3
/// fingerprint) would fail the final link step with `UnresolvedSymbol` and
/// be permanently routed to the interpreter.
///
/// # How it works
///
/// This uses a **compile-time function-pointer table** — no `dlsym`, no
/// platform-specific code. Each helper is a `#[no_mangle] pub extern "C" fn`
/// defined in [`crate::runtime_abi`] and linked into the tla-llvm2 rlib. We
/// take function pointers by path and cast them to `*const u8`.
///
/// On Mach-O targets (macOS / iOS) we also insert an underscored mirror
/// (`_jit_xxh3_fingerprint_64`) because the Mach-O ABI prefixes global
/// symbols with `_`. Emitted IR may reference either form depending on
/// which platform the relocation was written for.
///
/// # Fail-fast contract
///
/// The combined map builder validates that every helper listed in
/// [`crate::runtime::RUNTIME_HELPERS`] is covered after both helper families
/// are registered.
#[cfg(feature = "native")]
fn register_jit_symbols(symbols: &mut HashMap<String, *const u8>) {
    use crate::runtime_abi as rt;

    // Compile-time table of (symbol name, function pointer). Each symbol is a
    // `#[no_mangle] pub extern "C"` helper defined in `crate::runtime_abi`.
    // Must cover every entry in [`crate::runtime::RUNTIME_HELPERS`]; the
    // post-loop assertion below verifies this.
    let table: &[(&'static str, *const u8)] = &[
        ("jit_pow_i64", rt::jit_pow_i64 as *const u8),
        (
            "jit_set_contains_i64",
            rt::jit_set_contains_i64 as *const u8,
        ),
        ("jit_record_get_i64", rt::jit_record_get_i64 as *const u8),
        ("jit_func_apply_i64", rt::jit_func_apply_i64 as *const u8),
        ("jit_compound_count", rt::jit_compound_count as *const u8),
        ("jit_seq_get_i64", rt::jit_seq_get_i64 as *const u8),
        (
            "jit_func_set_membership_check",
            rt::jit_func_set_membership_check as *const u8,
        ),
        (
            "jit_record_new_scalar",
            rt::jit_record_new_scalar as *const u8,
        ),
        ("jit_set_diff_i64", rt::jit_set_diff_i64 as *const u8),
        ("jit_seq_tail", rt::jit_seq_tail as *const u8),
        ("jit_seq_append", rt::jit_seq_append as *const u8),
        ("jit_set_union_i64", rt::jit_set_union_i64 as *const u8),
        (
            "jit_xxh3_fingerprint_64",
            rt::jit_xxh3_fingerprint_64 as *const u8,
        ),
        (
            "jit_xxh3_fingerprint_128",
            rt::jit_xxh3_fingerprint_128 as *const u8,
        ),
    ];

    for (name, addr) in table {
        assert!(
            !addr.is_null(),
            "runtime helper '{name}' resolved to a null function pointer",
        );
        symbols.insert((*name).to_string(), *addr);
        // Mach-O (macOS / iOS) prefixes global symbols with `_`.
        #[cfg(any(target_os = "macos", target_os = "ios"))]
        symbols.insert(format!("_{name}"), *addr);
    }

    // Fail-fast: verify every declared `jit_*` RUNTIME_HELPER has an entry
    // in the compile-time table. A missing helper would silently leave the
    // JIT with an unresolvable extern at compile time (#4314).
    //
    // NOTE: Scoped to the `jit_*` family only. The `tla_*` family is owned
    // by [`register_tla_ops_symbols`] (Part of #4318) — `symbols` at this
    // point only contains `jit_*` entries, so checking every RUNTIME_HELPER
    // would spuriously flag `tla_*` entries as missing. #4318 Step 6 ships
    // a parallel audit for `tla_*` symbols (`debug_assert_tla_symbols_resolve`).
    for helper in crate::runtime::RUNTIME_HELPERS {
        if !helper.symbol.starts_with("jit_") {
            continue;
        }
        assert!(
            symbols.contains_key(helper.symbol),
            "runtime helper '{}' declared in RUNTIME_HELPERS is missing from \
             register_jit_symbols's compile-time table (see #4314)",
            helper.symbol,
        );
    }
}

/// Register handle-based `tla_*` helpers (R27 Option B, #4318).
///
/// Each entry is a `(name, fn_ptr)` pair where the pointer is taken
/// directly from the `#[no_mangle] pub extern "C"` site in
/// `runtime_abi::tla_ops`. On macOS we also insert the `_`-prefixed
/// Mach-O alias so `ld64`-style lookups succeed.
#[cfg(feature = "native")]
fn register_tla_ops_symbols(symbols: &mut HashMap<String, *const u8>) {
    use crate::runtime_abi::tla_ops::{
        clear_tla_arena, clear_tla_iter_arena, tla_cardinality, tla_domain, tla_func_apply,
        tla_handle_nil, tla_is_finite_set, tla_load_const, tla_quantifier_iter_done,
        tla_quantifier_iter_new, tla_quantifier_iter_next, tla_quantifier_runtime_error,
        tla_record_get, tla_seq_append, tla_seq_concat, tla_seq_head, tla_seq_len, tla_seq_new_0,
        tla_seq_new_1, tla_seq_new_2, tla_seq_new_3, tla_seq_new_4, tla_seq_new_5, tla_seq_new_6,
        tla_seq_new_7, tla_seq_new_8, tla_seq_set, tla_seq_subseq, tla_seq_tail, tla_set_big_union,
        tla_set_diff, tla_set_enum_0, tla_set_enum_1, tla_set_enum_2, tla_set_enum_3,
        tla_set_enum_4, tla_set_enum_5, tla_set_enum_6, tla_set_enum_7, tla_set_enum_8, tla_set_in,
        tla_set_intersect, tla_set_ksubset, tla_set_powerset, tla_set_range, tla_set_subseteq,
        tla_set_union, tla_tostring, tla_tuple_get, tla_tuple_new_0, tla_tuple_new_1,
        tla_tuple_new_2, tla_tuple_new_3, tla_tuple_new_4, tla_tuple_new_5, tla_tuple_new_6,
        tla_tuple_new_7, tla_tuple_new_8,
    };

    let table: &[(&str, *const u8)] = &[
        ("tla_handle_nil", tla_handle_nil as *const u8),
        ("clear_tla_arena", clear_tla_arena as *const u8),
        ("clear_tla_iter_arena", clear_tla_iter_arena as *const u8),
        ("tla_set_enum_0", tla_set_enum_0 as *const u8),
        ("tla_set_enum_1", tla_set_enum_1 as *const u8),
        ("tla_set_enum_2", tla_set_enum_2 as *const u8),
        ("tla_set_enum_3", tla_set_enum_3 as *const u8),
        ("tla_set_enum_4", tla_set_enum_4 as *const u8),
        ("tla_set_enum_5", tla_set_enum_5 as *const u8),
        ("tla_set_enum_6", tla_set_enum_6 as *const u8),
        ("tla_set_enum_7", tla_set_enum_7 as *const u8),
        ("tla_set_enum_8", tla_set_enum_8 as *const u8),
        ("tla_set_in", tla_set_in as *const u8),
        ("tla_set_union", tla_set_union as *const u8),
        ("tla_set_intersect", tla_set_intersect as *const u8),
        ("tla_set_diff", tla_set_diff as *const u8),
        ("tla_set_subseteq", tla_set_subseteq as *const u8),
        ("tla_set_powerset", tla_set_powerset as *const u8),
        ("tla_set_big_union", tla_set_big_union as *const u8),
        ("tla_set_range", tla_set_range as *const u8),
        ("tla_set_ksubset", tla_set_ksubset as *const u8),
        // tla_tuple_* — R27 Option B tuple family (#4318). 9 N-arity
        // monomorphs for `<<e_1, …, e_N>>` literals plus `tla_tuple_get`
        // for 1-indexed element access. Keep bundled so JIT linker
        // resolution failures point at a single emit-site family.
        ("tla_tuple_new_0", tla_tuple_new_0 as *const u8),
        ("tla_tuple_new_1", tla_tuple_new_1 as *const u8),
        ("tla_tuple_new_2", tla_tuple_new_2 as *const u8),
        ("tla_tuple_new_3", tla_tuple_new_3 as *const u8),
        ("tla_tuple_new_4", tla_tuple_new_4 as *const u8),
        ("tla_tuple_new_5", tla_tuple_new_5 as *const u8),
        ("tla_tuple_new_6", tla_tuple_new_6 as *const u8),
        ("tla_tuple_new_7", tla_tuple_new_7 as *const u8),
        ("tla_tuple_new_8", tla_tuple_new_8 as *const u8),
        ("tla_tuple_get", tla_tuple_get as *const u8),
        // tla_quantifier_* — Phase 5 quantifier iterator family. Iter handles
        // are raw i64 arena indices (not TlaHandle tag-encoded). The `-> !`
        // runtime_error helper coerces to `*const u8` via `as *const u8`
        // because function-pointer conversion discards the return type.
        (
            "tla_quantifier_iter_new",
            tla_quantifier_iter_new as *const u8,
        ),
        (
            "tla_quantifier_iter_done",
            tla_quantifier_iter_done as *const u8,
        ),
        (
            "tla_quantifier_iter_next",
            tla_quantifier_iter_next as *const u8,
        ),
        (
            "tla_quantifier_runtime_error",
            tla_quantifier_runtime_error as *const u8,
        ),
        // tla_load_const / builtin family — Option B const_builtin (§2.5, #4318).
        ("tla_load_const", tla_load_const as *const u8),
        ("tla_cardinality", tla_cardinality as *const u8),
        ("tla_is_finite_set", tla_is_finite_set as *const u8),
        ("tla_tostring", tla_tostring as *const u8),
        // tla_record_* / tla_func_* / tla_domain — Option B record_func family
        // (§2.4, #4318). Record field access, function application (covers
        // Func/IntFunc/Seq/Tuple/Record), and DOMAIN. NIL_HANDLE on any
        // unsupported path triggers interpreter fallback.
        ("tla_record_get", tla_record_get as *const u8),
        ("tla_func_apply", tla_func_apply as *const u8),
        ("tla_domain", tla_domain as *const u8),
        // tla_seq_* — R27 Option B sequence family (#4318). 9 N-arity
        // monomorphs for `<<e_1, …, e_N>>` literals plus 7 opcode helpers
        // (`concat`, `len`, `head`, `tail`, `append`, `subseq`, `set`).
        // Bundled so JIT linker resolution failures point at a single
        // emit-site family. All helpers fall back to `NIL_HANDLE` on
        // non-sequence / out-of-range operands so tir_lower routes to the
        // interpreter.
        ("tla_seq_new_0", tla_seq_new_0 as *const u8),
        ("tla_seq_new_1", tla_seq_new_1 as *const u8),
        ("tla_seq_new_2", tla_seq_new_2 as *const u8),
        ("tla_seq_new_3", tla_seq_new_3 as *const u8),
        ("tla_seq_new_4", tla_seq_new_4 as *const u8),
        ("tla_seq_new_5", tla_seq_new_5 as *const u8),
        ("tla_seq_new_6", tla_seq_new_6 as *const u8),
        ("tla_seq_new_7", tla_seq_new_7 as *const u8),
        ("tla_seq_new_8", tla_seq_new_8 as *const u8),
        ("tla_seq_concat", tla_seq_concat as *const u8),
        ("tla_seq_len", tla_seq_len as *const u8),
        ("tla_seq_head", tla_seq_head as *const u8),
        ("tla_seq_tail", tla_seq_tail as *const u8),
        ("tla_seq_append", tla_seq_append as *const u8),
        ("tla_seq_subseq", tla_seq_subseq as *const u8),
        ("tla_seq_set", tla_seq_set as *const u8),
    ];

    for (sym, addr) in table {
        symbols.insert((*sym).to_string(), *addr);
        #[cfg(target_os = "macos")]
        symbols.insert(format!("_{sym}"), *addr);
    }
}

/// Register native BFS helper externs that are called directly from generated
/// parent-loop modules.
///
/// Part of #4319 Phase 2. LLVM2 registers an in-crate shim under the stable
/// C-ABI name expected by emitted IR. The shim hashes flat buffers through
/// `xxh3_64_with_seed(buf, FLAT_COMPILED_DOMAIN_SEED)`, matching the
/// Rust-side BFS driver's `fingerprint_flat_compiled` domain without requiring
/// `tla-check` or `tla-jit-runtime` to export the symbol into every
/// `tla-llvm2` integration-test binary.
///
/// Kept in its own `register_*` function (separate from
/// [`register_jit_symbols`] and [`register_tla_ops_symbols`]) so that the
/// three registration surfaces remain independently auditable.
///
/// On Mach-O targets (macOS / iOS) we also insert the `_`-prefixed alias so
/// `ld64`-style lookups resolve — mirrors the pattern TL68 established for
/// `jit_*` and `tla_*` symbols.
#[cfg(feature = "native")]
fn register_fp_symbols(symbols: &mut HashMap<String, *const u8>) {
    // The Rust symbol is intentionally mangled; only the explicit JIT symbol
    // map exposes the stable C-ABI name. This avoids duplicate exported
    // symbols when the final binary also links legacy runtime crates.
    let fp_ptr = crate::runtime_abi::tla2_compiled_fp_u64 as *const u8;
    let resizable_probe_ptr = crate::runtime_abi::resizable_fp_set_probe as *const u8;
    assert!(
        !fp_ptr.is_null(),
        "tla2_compiled_fp_u64 resolved to a null function pointer — link error",
    );
    assert!(
        !resizable_probe_ptr.is_null(),
        "resizable_fp_set_probe resolved to a null function pointer — link error",
    );

    symbols.insert("tla2_compiled_fp_u64".to_string(), fp_ptr);
    symbols.insert("resizable_fp_set_probe".to_string(), resizable_probe_ptr);
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    {
        symbols.insert("_tla2_compiled_fp_u64".to_string(), fp_ptr);
        symbols.insert("_resizable_fp_set_probe".to_string(), resizable_probe_ptr);
    }
}

/// Expose the extern symbol map for tests and audit tooling.
///
/// Thin wrapper around [`build_extern_symbol_map`] so
/// `tests/extern_symbols_present.rs` can validate non-null resolution for
/// every helper on both Linux and macOS without going through
/// `compile_module_native`.
#[cfg(feature = "native")]
#[must_use]
pub fn extern_symbol_map_for_tests() -> HashMap<String, *const u8> {
    build_extern_symbol_map()
}

/// Scan an LLVM-IR text blob for `declare ... @tla_*` lines and return
/// every declared helper symbol that is not present in `extern_symbols`.
///
/// Part of #4318 Step 6 (Option B unused-symbol audit guard). The tir_lower
/// emitter populates a `BTreeSet<String>` of `declare i64 @tla_<op>(...)`
/// strings (see `tla_llvm2::tmir_lower`) which are written verbatim into the
/// output IR. If a future tir_lower emit site invents a new `@tla_*` symbol
/// that is not yet registered in [`build_extern_symbol_map`], the JIT link
/// step in [`compile_module_native`] would silently drift — resolution
/// failures are only surfaced at the point where `compile_raw` actually
/// consumes the extern map. This function catches that drift at its root:
/// the emitter is the single source of truth for declared symbols.
///
/// The matcher is intentionally narrow — it only recognises tokens of the
/// form `@tla_<ident>`. It does not try to parse the full declaration, so
/// callers can feed it raw IR without a separate LLVM parser dependency.
///
/// Returns `Ok(())` when every declared `@tla_*` symbol resolves via the
/// extern map, or `Err(missing)` listing the unresolved symbols.
#[cfg(feature = "native")]
pub(crate) fn audit_declared_tla_symbols(
    ir_text: &str,
    extern_symbols: &HashMap<String, *const u8>,
) -> Result<(), Vec<String>> {
    let mut missing: Vec<String> = Vec::new();
    for line in ir_text.lines() {
        // Only inspect top-level `declare` lines. `declare` always sits at
        // column 0 in the IR emitted by `tmir_lower`.
        let trimmed = line.trim_start();
        if !trimmed.starts_with("declare ") {
            continue;
        }
        // Extract the `@tla_<ident>` token. A declare line looks like:
        //   declare i64 @tla_set_union(i64, i64)
        // We scan past `@` and consume ident characters.
        let Some(at_pos) = trimmed.find("@tla_") else {
            continue;
        };
        let after_at = &trimmed[at_pos + 1..];
        // Ident characters: ASCII alphanumeric plus `_`. Stop at anything
        // else (typically `(` for the param list).
        let end = after_at
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(after_at.len());
        let symbol = &after_at[..end];
        if !extern_symbols.contains_key(symbol) {
            missing.push(symbol.to_string());
        }
    }
    if missing.is_empty() {
        Ok(())
    } else {
        missing.sort();
        missing.dedup();
        Err(missing)
    }
}

/// Debug-only wrapper that panics when a compiled IR blob declares a
/// `@tla_*` helper absent from the extern map.
///
/// Part of #4318 Step 6. The release build path is zero-cost — the wrapper
/// compiles to a no-op when `debug_assertions` is off. In debug builds, the
/// panic message lists every missing symbol so regressions are attributable
/// to the specific emit site.
///
/// Exposed for tests and as a runtime integration point for any future text
/// based compilation flow that wants to enforce symbol-map coverage
/// end-to-end. `compile_module_native` cannot call this directly because it
/// bypasses textual IR and translates tMIR straight into the LLVM2 internal
/// representation; the audit lives at the boundary where IR text *is*
/// produced.
#[cfg(feature = "native")]
pub(crate) fn debug_assert_tla_symbols_resolve(ir_text: &str) {
    if cfg!(debug_assertions) {
        let map = build_extern_symbol_map();
        if let Err(missing) = audit_declared_tla_symbols(ir_text, &map) {
            panic!(
                "LLVM IR declares @tla_* helpers missing from extern map \
                 (Option B drift): {missing:?}. Register them in \
                 register_tla_ops_symbols (compile.rs) and RUNTIME_HELPERS \
                 (runtime.rs)."
            );
        }
    }
}

// =============================================================================
// NativeLibrary — handle to JIT-compiled native code
// =============================================================================

/// Handle to compiled native code.
///
/// When the `native` feature is enabled, wraps LLVM2's [`ExecutableBuffer`]
/// with compiled functions in executable memory. Symbol lookup is by name.
/// The memory is freed on drop (via raw munmap syscall — no libc).
///
/// The buffer is stored in an [`Arc`] so the process-local JIT cache can
/// hand out cheap, cloneable references on cache hits without recompiling.
#[cfg(feature = "native")]
pub struct NativeLibrary {
    /// LLVM2 executable buffer (owns the mmap'd memory). Wrapped in `Arc`
    /// so cache hits can share one buffer across many `NativeLibrary`
    /// handles without copying the machine code.
    buffer: Arc<llvm2_codegen::ExecutableBuffer>,
    /// Module name for diagnostics.
    pub(crate) name: String,
}

/// Stub NativeLibrary when native feature is disabled.
#[cfg(not(feature = "native"))]
pub struct NativeLibrary {
    pub(crate) name: String,
}

#[cfg(feature = "native")]
impl Clone for NativeLibrary {
    fn clone(&self) -> Self {
        Self {
            buffer: Arc::clone(&self.buffer),
            name: self.name.clone(),
        }
    }
}

#[cfg(not(feature = "native"))]
impl Clone for NativeLibrary {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
        }
    }
}

#[cfg(feature = "native")]
unsafe impl Send for NativeLibrary {}
#[cfg(feature = "native")]
unsafe impl Sync for NativeLibrary {}

#[cfg(feature = "native")]
impl NativeLibrary {
    /// Look up a symbol by name and return a raw function pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure the returned pointer is cast to the correct
    /// function signature before calling.
    pub unsafe fn get_symbol(&self, name: &str) -> Result<*mut std::ffi::c_void, Llvm2Error> {
        self.buffer
            .get_fn_ptr_bound(name)
            .map(|p| p.as_ptr() as *mut std::ffi::c_void)
            .ok_or_else(|| {
                Llvm2Error::Loading(format!(
                    "symbol '{name}' not found in compiled module '{}'",
                    self.name
                ))
            })
    }

    /// Read the LLVM2 JIT function-entry counter for `name`, when emitted.
    pub fn entry_count(&self, name: &str) -> Option<u64> {
        self.buffer.entry_count(name)
    }

    /// Get the path (not applicable for JIT — returns a descriptive string).
    pub fn path(&self) -> PathBuf {
        PathBuf::from(format!("<jit:{}>", self.name))
    }
}

#[cfg(not(feature = "native"))]
impl NativeLibrary {
    /// Stub: always errors (native feature disabled).
    pub unsafe fn get_symbol(&self, name: &str) -> Result<*mut std::ffi::c_void, Llvm2Error> {
        Err(Llvm2Error::BackendUnavailable(format!(
            "cannot look up symbol '{name}': native feature disabled"
        )))
    }

    /// Stub: entry counters require the native LLVM2 JIT feature.
    pub fn entry_count(&self, _name: &str) -> Option<u64> {
        None
    }

    /// Get the path (stub).
    pub fn path(&self) -> PathBuf {
        PathBuf::from(format!("<disabled:{}>", self.name))
    }
}

impl std::fmt::Debug for NativeLibrary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeLibrary")
            .field("name", &self.name)
            .finish()
    }
}

/// Compile a tMIR module to LLVM IR.
///
/// This is the primary public API for the IR-text path. It validates the module,
/// lowers it through the text emission pipeline, and returns the emitted LLVM IR.
///
/// For native compilation, use [`compile_module_native`] instead — it bypasses
/// text IR entirely and goes through LLVM2's direct pipeline.
///
/// # Pipeline passes (design doc §6)
///
/// Before lowering, the module is run through [`crate::prefetch::insert_prefetch_pass`]
/// so BFS-frontier-drain loops are annotated with a `[prefetch sites=N ...]`
/// marker on the module name. The pass is detection-only today — real
/// `@llvm.prefetch` emission is gated on LLVM2#390. Wiring the pass into
/// the pipeline now guarantees that every production path (native + text)
/// already runs it, so turning emission on later is a drop-in change.
///
/// # Arguments
///
/// * `module` - A tMIR module produced by [`tla_tmir::lower`].
///
/// # Errors
///
/// Returns [`Llvm2Error`] if the module is invalid, contains unsupported
/// instructions, or compilation fails.
pub fn compile_module(module: &Module) -> Result<CompiledModule, Llvm2Error> {
    // Run module-level passes on a local clone so callers retain the
    // original module. The prefetch pass only annotates `module.name`
    // today; cloning up front keeps the door open for richer passes.
    let mut working = module.clone();
    run_module_passes(&mut working);

    let stats = lower::lower_module(&working)?;
    let llvm_ir = stats.llvm_ir.clone();

    Ok(CompiledModule {
        name: working.name.clone(),
        stats,
        llvm_ir,
    })
}

/// Run tMIR-level passes that must execute before lowering.
///
/// Currently: [`crate::prefetch::insert_prefetch_pass`]. The function is
/// infallible from the pipeline's point of view — the pass reports its
/// own errors via the `PrefetchError` type, and pipeline-level decisions
/// about what to do on `IntrinsicUnavailable` live here. Today that
/// variant is never returned (the pass is detection-only), so we can
/// safely swallow any future upstream errors as a no-op.
pub(crate) fn run_module_passes(module: &mut Module) {
    // Prefetch pass (design doc §6). Detection-only until LLVM2#390.
    let _ =
        crate::prefetch::insert_prefetch_pass(module, &crate::prefetch::PrefetchConfig::default());
}

/// Compile a tMIR module from a bytecode function via tla-tmir lowering.
///
/// Convenience wrapper that chains tla-tmir lowering with LLVM2 compilation.
/// Lowers the bytecode invariant function to tMIR, then compiles via LLVM2.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or other
/// [`Llvm2Error`] variants if LLVM2 compilation fails.
pub fn compile_invariant(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_invariant(func, name)?;
    compile_module(&tmir_module)
}

/// Compile a tMIR module from a bytecode invariant function with constant pool.
///
/// Same as [`compile_invariant`] but accepts a [`ConstantPool`] for resolving
/// `LoadConst` and `Unchanged` opcodes that reference the constant pool.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or other
/// [`Llvm2Error`] variants if LLVM2 compilation fails.
pub fn compile_invariant_with_constants(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    const_pool: &tla_tir::bytecode::ConstantPool,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_invariant_with_constants(func, name, const_pool)?;
    compile_module(&tmir_module)
}

/// Compile a tMIR module from a bytecode next-state function via tla-tmir lowering.
///
/// Convenience wrapper that chains tla-tmir lowering with LLVM2 compilation.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or other
/// [`Llvm2Error`] variants if LLVM2 compilation fails.
pub fn compile_next_state(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_next_state(func, name)?;
    compile_module(&tmir_module)
}

/// Compile a tMIR module from a bytecode next-state function with constant pool.
///
/// Same as [`compile_next_state`] but accepts a [`ConstantPool`] for resolving
/// `LoadConst` and `Unchanged` opcodes that reference the constant pool.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or other
/// [`Llvm2Error`] variants if LLVM2 compilation fails.
pub fn compile_next_state_with_constants(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    const_pool: &tla_tir::bytecode::ConstantPool,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_next_state_with_constants(func, name, const_pool)?;
    compile_module(&tmir_module)
}

// =============================================================================
// Native compilation: BytecodeFunction -> NativeLibrary (no text IR intermediary)
// =============================================================================

/// Compile a bytecode next-state function directly to native code.
///
/// Chains tla-tmir lowering with [`compile_module_native`] to produce a
/// [`NativeLibrary`] containing the compiled function. This bypasses the text
/// LLVM IR intermediary entirely.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or
/// [`Llvm2Error::CodeGen`] / [`Llvm2Error::BackendUnavailable`] if native
/// compilation fails.
pub fn compile_next_state_native(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_next_state(func, name)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a bytecode next-state function with constant pool directly to native code.
///
/// Same as [`compile_next_state_native`] but accepts a [`ConstantPool`] for
/// resolving `LoadConst` and `Unchanged` opcodes.
pub fn compile_next_state_native_with_constants(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    const_pool: &tla_tir::bytecode::ConstantPool,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_next_state_with_constants(func, name, const_pool)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a bytecode next-state function with constant pool and checker
/// state-layout metadata directly to native code.
pub fn compile_next_state_native_with_constants_and_layout(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    const_pool: &tla_tir::bytecode::ConstantPool,
    state_layout: &tla_jit_abi::StateLayout,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_next_state_with_constants_and_layout(
        func,
        name,
        const_pool,
        state_layout,
    )?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a bytecode invariant function directly to native code.
///
/// Chains tla-tmir lowering with [`compile_module_native`] to produce a
/// [`NativeLibrary`] containing the compiled function.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or
/// [`Llvm2Error::CodeGen`] / [`Llvm2Error::BackendUnavailable`] if native
/// compilation fails.
pub fn compile_invariant_native(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_invariant(func, name)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a bytecode invariant function with constant pool directly to native code.
///
/// Same as [`compile_invariant_native`] but accepts a [`ConstantPool`] for
/// resolving `LoadConst` opcodes.
pub fn compile_invariant_native_with_constants(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    const_pool: &tla_tir::bytecode::ConstantPool,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_invariant_with_constants(func, name, const_pool)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a bytecode invariant with constant pool and checker state layout
/// directly to native code.
pub fn compile_invariant_native_with_constants_and_layout(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    const_pool: &tla_tir::bytecode::ConstantPool,
    state_layout: &tla_jit_abi::StateLayout,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_invariant_with_constants_and_layout(
        func,
        name,
        const_pool,
        state_layout,
    )?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a multi-function bytecode chunk (spec) to LLVM IR.
///
/// This is the primary entry point for compiling a complete TLA+ spec through
/// the full pipeline: BytecodeChunk -> tMIR (via tla-tmir) -> LLVM IR text
/// (via tla-llvm2).
///
/// The entrypoint function at `entry_idx` in the chunk is lowered as an
/// invariant function. All transitively reachable callees are included in the
/// output module.
///
/// # Arguments
///
/// * `chunk` - A complete bytecode compilation unit with shared constant pool.
/// * `entry_idx` - Index of the entrypoint function in the chunk.
/// * `name` - Module name for the output.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if bytecode-to-tMIR lowering fails.
/// Returns other [`Llvm2Error`] variants if LLVM IR emission fails.
pub fn compile_spec_invariant(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_module_invariant(chunk, entry_idx, name)?;
    compile_module(&tmir_module)
}

/// Compile a multi-function bytecode chunk for next-state evaluation.
///
/// Same as [`compile_spec_invariant`] but the entrypoint uses the next-state
/// signature: `fn(out, state_in, state_out, state_len) -> void`.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if bytecode-to-tMIR lowering fails.
/// Returns other [`Llvm2Error`] variants if LLVM IR emission fails.
pub fn compile_spec_next_state(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_module_next_state(chunk, entry_idx, name)?;
    compile_module(&tmir_module)
}

/// Compile a multi-function bytecode chunk for invariant evaluation directly
/// to native code.
///
/// Chunk-aware counterpart to [`compile_invariant_native_with_constants`].
/// Lowers the entry function at `entry_idx` together with every transitively
/// reachable callee via [`tla_tmir::lower::lower_module_invariant`], then
/// JIT-compiles the resulting tMIR module through [`compile_module_native`].
///
/// Prefer this over [`compile_invariant_native_with_constants`] whenever a
/// [`BytecodeChunk`] is available: the single-function path emits
/// `__func_N` references for any user-defined-operator `Call` in the entry
/// function without ever defining the target, which fails at link time
/// ("unresolved symbol: __func_1"). Part of #4280 Gap C.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if bytecode-to-tMIR lowering fails, or
/// [`Llvm2Error::CodeGen`] / [`Llvm2Error::BackendUnavailable`] if native
/// compilation fails.
pub fn compile_spec_invariant_native(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_module_invariant(chunk, entry_idx, name)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a multi-function bytecode chunk for next-state evaluation directly
/// to native code.
///
/// Chunk-aware counterpart to [`compile_next_state_native_with_constants`].
/// Lowers the entry function at `entry_idx` together with every transitively
/// reachable callee via [`tla_tmir::lower::lower_module_next_state`], then
/// JIT-compiles the resulting tMIR module through [`compile_module_native`].
///
/// Prefer this over [`compile_next_state_native_with_constants`] whenever a
/// [`BytecodeChunk`] is available: the single-function path emits
/// `__func_N` references for any user-defined-operator `Call` in the entry
/// function without ever defining the target, which fails at link time
/// ("unresolved symbol: __func_1"). Part of #4280 Gap C.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if bytecode-to-tMIR lowering fails, or
/// [`Llvm2Error::CodeGen`] / [`Llvm2Error::BackendUnavailable`] if native
/// compilation fails.
pub fn compile_spec_next_state_native(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_module_next_state(chunk, entry_idx, name)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a standalone invariant entry function to native code, resolving
/// callees from `chunk`.
///
/// Chunk-aware counterpart to [`compile_invariant_native_with_constants`] for
/// callers that hold a [`tla_tir::bytecode::BytecodeFunction`] that is NOT
/// stored inside `chunk.functions` (e.g. specialized arity-0 functions
/// produced by `specialize_bytecode_function`). Lowers via
/// [`tla_tmir::lower::lower_entry_invariant_with_chunk`] so user-defined
/// operator callees reachable from the entry function are fully defined in
/// the output module. Part of #4280 Gap C.
pub fn compile_entry_invariant_native_with_chunk(
    entry_func: &tla_tir::bytecode::BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_entry_invariant_with_chunk(entry_func, chunk, name)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a standalone invariant entry function to native code, resolving
/// callees from `chunk`, with checker state-layout metadata.
pub fn compile_entry_invariant_native_with_chunk_and_layout(
    entry_func: &tla_tir::bytecode::BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
    state_layout: &tla_jit_abi::StateLayout,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_entry_invariant_with_chunk_and_layout(
        entry_func,
        chunk,
        name,
        state_layout,
    )?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a standalone next-state entry function to native code, resolving
/// callees from `chunk`.
///
/// Chunk-aware counterpart to [`compile_next_state_native_with_constants`].
/// Lowers via [`tla_tmir::lower::lower_entry_next_state_with_chunk`] so any
/// user-defined operator callees reachable from `entry_func` are fully
/// defined in the output module. Part of #4280 Gap C.
pub fn compile_entry_next_state_native_with_chunk(
    entry_func: &tla_tir::bytecode::BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_entry_next_state_with_chunk(entry_func, chunk, name)?;
    compile_module_native(&tmir_module, opt_level)
}

/// Compile a standalone next-state entry function to native code, resolving
/// callees from `chunk`, with checker state-layout metadata.
pub fn compile_entry_next_state_native_with_chunk_and_layout(
    entry_func: &tla_tir::bytecode::BytecodeFunction,
    chunk: &BytecodeChunk,
    name: &str,
    state_layout: &tla_jit_abi::StateLayout,
    opt_level: OptLevel,
) -> Result<NativeLibrary, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_entry_next_state_with_chunk_and_layout(
        entry_func,
        chunk,
        name,
        state_layout,
    )?;
    compile_module_native(&tmir_module, opt_level)
}

/// Description of a BFS step compilation output.
///
/// Contains the compiled LLVM IR for the next-state relation and all
/// invariant checks for a single action. Used by the model checker to
/// drive state exploration.
///
/// # Index Stability
///
/// The `invariants` vector maintains positional alignment with the input
/// `invariant_funcs` slice passed to [`compile_bfs_step`]. When an individual
/// invariant fails to compile, its slot is `None` rather than being omitted.
/// This ensures `invariants[i]` always corresponds to `invariant_funcs[i]`,
/// preventing index misalignment bugs when the model checker maps a failed
/// invariant index back to the spec's invariant list.
///
/// Part of #4197: robust invariant index remapping on partial compile failure.
#[derive(Debug)]
pub struct CompiledBfsStep {
    /// Name of the action this step was compiled from.
    pub action_name: String,
    /// Compiled next-state function.
    pub next_state: CompiledModule,
    /// Compiled invariant functions, indexed parallel to the input invariant list.
    /// `invariants[i]` is `Some(module)` when compilation succeeded for invariant `i`,
    /// or `None` when compilation failed. This preserves index alignment with the
    /// spec's invariant list even on partial compilation failure.
    pub invariants: Vec<Option<CompiledModule>>,
    /// Number of invariants that were successfully compiled.
    pub invariants_compiled: usize,
    /// Number of invariants that failed compilation.
    pub invariants_failed: usize,
}

/// LLVM2 fused BFS level foundation.
///
/// This alias gives integration code the expected `tla_llvm2::CompiledBfsLevel`
/// name while the concrete implementation lives in [`crate::bfs_level`]. The
/// current implementation is a compile/testable Rust prototype over LLVM2
/// action and invariant function pointers; [`crate::bfs_level::Llvm2FusedLevelFn`]
/// is the native fused-loop ABI that will replace the Rust parent loop.
pub type CompiledBfsLevel = crate::bfs_level::Llvm2BfsLevelPrototype;

/// A compiled native LLVM2 next-state action that can be linked into a fused
/// BFS level parent loop.
#[derive(Debug, Clone)]
pub struct Llvm2BfsLevelNativeAction {
    /// Descriptor for this specialized action instance.
    pub descriptor: ActionDescriptor,
    /// Native library that owns `symbol_name`.
    pub library: NativeLibrary,
    /// Symbol implementing the stable LLVM2 next-state ABI.
    pub symbol_name: String,
}

impl Llvm2BfsLevelNativeAction {
    /// Create one native action input for [`compile_bfs_level_native`].
    #[must_use]
    pub fn new(
        descriptor: ActionDescriptor,
        library: NativeLibrary,
        symbol_name: impl Into<String>,
    ) -> Self {
        Self {
            descriptor,
            library,
            symbol_name: symbol_name.into(),
        }
    }
}

/// A compiled native LLVM2 invariant that can be linked into a fused BFS level
/// parent loop.
#[derive(Debug, Clone)]
pub struct Llvm2BfsLevelNativeInvariant {
    /// Descriptor for this invariant.
    pub descriptor: InvariantDescriptor,
    /// Native library that owns `symbol_name`.
    pub library: NativeLibrary,
    /// Symbol implementing the stable LLVM2 invariant ABI.
    pub symbol_name: String,
}

impl Llvm2BfsLevelNativeInvariant {
    /// Create one native invariant input for [`compile_bfs_level_native`].
    #[must_use]
    pub fn new(
        descriptor: InvariantDescriptor,
        library: NativeLibrary,
        symbol_name: impl Into<String>,
    ) -> Self {
        Self {
            descriptor,
            library,
            symbol_name: symbol_name.into(),
        }
    }
}

/// A compiled native LLVM2 state constraint that can be linked into a fused
/// BFS level parent loop.
///
/// State constraints use the same native predicate ABI as invariants, but are
/// applied to generated successors before local dedup and successor arena
/// admission. A zero predicate value rejects the successor.
#[derive(Debug, Clone)]
pub struct Llvm2BfsLevelNativeStateConstraint {
    /// Human-readable state-constraint name.
    pub name: String,
    /// Index into the spec's state-constraint list.
    pub constraint_idx: u32,
    /// Native library that owns `symbol_name`.
    pub library: NativeLibrary,
    /// Symbol implementing the stable LLVM2 invariant/state-constraint ABI.
    pub symbol_name: String,
}

impl Llvm2BfsLevelNativeStateConstraint {
    /// Create one native state-constraint input for
    /// [`compile_bfs_level_native_with_state_constraints`].
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        constraint_idx: u32,
        library: NativeLibrary,
        symbol_name: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            constraint_idx,
            library,
            symbol_name: symbol_name.into(),
        }
    }
}

struct NativeBfsCallbackTargets {
    action_addresses: Vec<usize>,
    state_constraints: Vec<NativeBfsStateConstraintTarget>,
    invariants: Vec<NativeBfsInvariantTarget>,
    extern_libraries: Vec<NativeLibrary>,
}

fn build_native_bfs_callback_targets(
    actions: &[Llvm2BfsLevelNativeAction],
    state_constraints: &[Llvm2BfsLevelNativeStateConstraint],
    invariants: &[Llvm2BfsLevelNativeInvariant],
) -> Result<NativeBfsCallbackTargets, Llvm2Error> {
    let mut extern_libraries =
        Vec::with_capacity(actions.len() + state_constraints.len() + invariants.len());
    let mut action_addresses = Vec::with_capacity(actions.len());
    let mut resolved_state_constraints = Vec::with_capacity(state_constraints.len());
    let mut resolved_invariants = Vec::with_capacity(invariants.len());

    for action in actions {
        // SAFETY: this only looks up an address. The generated tMIR declares
        // a raw-address CallIndirect with the stable JitNextStateFn ABI, and
        // the returned fused wrapper keeps a clone of `action.library` alive
        // for the call target.
        let raw = unsafe { action.library.get_symbol(&action.symbol_name)? };
        action_addresses.push(raw as usize);
        extern_libraries.push(action.library.clone());
    }

    for state_constraint in state_constraints {
        // SAFETY: this only looks up an address. The generated tMIR declares
        // a raw-address CallIndirect with the stable JitInvariantFn-compatible
        // predicate ABI, and the returned fused wrapper keeps a clone of
        // `state_constraint.library` alive for the call target.
        let raw = unsafe {
            state_constraint
                .library
                .get_symbol(&state_constraint.symbol_name)?
        };
        resolved_state_constraints.push(NativeBfsStateConstraintTarget {
            constraint_idx: state_constraint.constraint_idx,
            address: raw as usize,
        });
        extern_libraries.push(state_constraint.library.clone());
    }

    for invariant in invariants {
        // SAFETY: this only looks up an address. The generated tMIR declares
        // a raw-address CallIndirect with the stable JitInvariantFn ABI, and
        // the returned fused wrapper keeps a clone of `invariant.library`
        // alive for the call target.
        let raw = unsafe { invariant.library.get_symbol(&invariant.symbol_name)? };
        resolved_invariants.push(NativeBfsInvariantTarget {
            invariant_idx: invariant.descriptor.invariant_idx,
            address: raw as usize,
        });
        extern_libraries.push(invariant.library.clone());
    }

    Ok(NativeBfsCallbackTargets {
        action_addresses,
        state_constraints: resolved_state_constraints,
        invariants: resolved_invariants,
        extern_libraries,
    })
}

/// Compile a native LLVM2 fused BFS level over a flat parent frontier with no
/// fused state constraints.
///
/// This preserves the existing invariant-checking public API while delegating
/// to [`compile_bfs_level_native_with_state_constraints`] with an empty
/// state-constraint list.
pub fn compile_bfs_level_native(
    state_len: usize,
    actions: &[Llvm2BfsLevelNativeAction],
    invariants: &[Llvm2BfsLevelNativeInvariant],
    opt_level: OptLevel,
) -> Result<Llvm2BfsLevelNative, Llvm2Error> {
    compile_bfs_level_native_with_state_constraints(state_len, actions, &[], invariants, opt_level)
}

/// Compile a native LLVM2 fused BFS level over a flat parent frontier.
///
/// The generated module contains the parent loop and calls action,
/// state-constraint, and invariant functions through raw callback addresses.
/// State constraints are checked after each enabled action produces a
/// candidate successor and before local fingerprint dedup, successor arena
/// insertion, and invariant checks. It returns [`Llvm2BfsLevelNative`] only
/// after the fused entry symbol resolves successfully;
/// `metadata().capabilities().native_fused_loop` is therefore accurate. By
/// default the native parent loop leaves local fingerprint dedup off and lets
/// caller-side global/frontier dedup enforce final state uniqueness. Setting
/// `TLA2_LLVM2_NATIVE_FUSED_ENABLE_LOCAL_DEDUP` opts back into the native local
/// filter after the helper path has been proven for a benchmark. Setting
/// `TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP` always forces it off.
pub fn compile_bfs_level_native_with_state_constraints(
    state_len: usize,
    actions: &[Llvm2BfsLevelNativeAction],
    state_constraints: &[Llvm2BfsLevelNativeStateConstraint],
    invariants: &[Llvm2BfsLevelNativeInvariant],
    opt_level: OptLevel,
) -> Result<Llvm2BfsLevelNative, Llvm2Error> {
    if actions.is_empty() {
        return Err(Llvm2Error::InvalidModule(
            "native BFS level requires at least one action".to_string(),
        ));
    }

    let callback_targets =
        build_native_bfs_callback_targets(actions, state_constraints, invariants)?;

    let module = build_native_bfs_level_module_with_state_constraints(
        state_len,
        callback_targets.action_addresses.as_slice(),
        callback_targets.state_constraints.as_slice(),
        callback_targets.invariants.as_slice(),
    )?;
    let library = compile_module_native(&module, opt_level)?;
    let local_dedup = native_fused_local_dedup_enabled();
    let metadata = Llvm2BfsLevelNativeMetadata::new_with_state_constraints(
        actions.len(),
        state_constraints.len(),
        invariants.len(),
        actions.len(),
        local_dedup,
    );
    Llvm2BfsLevelNative::from_library_with_metadata_and_dependencies(
        state_len,
        library,
        LLVM2_BFS_LEVEL_NATIVE_SYMBOL,
        metadata,
        callback_targets.extern_libraries,
    )
}

/// Compile an action-only native LLVM2 fused BFS level.
///
/// This is the production entry point for the first native fused parent loop:
/// native code runs the flat-frontier action loop and writes successors, while
/// callers check invariants afterward using their existing Rust/JIT/interpreter
/// path. The returned metadata therefore reports `invariant_count == 0`.
pub fn compile_bfs_level_native_actions_only(
    state_len: usize,
    actions: &[Llvm2BfsLevelNativeAction],
    opt_level: OptLevel,
) -> Result<Llvm2BfsLevelNative, Llvm2Error> {
    compile_bfs_level_native_with_state_constraints(state_len, actions, &[], &[], opt_level)
}

/// Compile a BFS step: one next-state function and zero or more invariants.
///
/// This is the compilation driver for the model checker integration. Given a
/// next-state bytecode function and a list of invariant bytecode functions,
/// it produces LLVM IR for all of them through the full pipeline.
///
/// Individual invariant compilation failures are tolerated: the corresponding
/// slot in [`CompiledBfsStep::invariants`] will be `None`, and the model
/// checker must fall back to the interpreter for those invariants. The next-state
/// function is required -- if it fails to compile, the entire step fails.
///
/// # Arguments
///
/// * `action_name` - Name of the action (for diagnostics).
/// * `next_state_func` - Bytecode function for the next-state relation.
/// * `invariant_funcs` - Bytecode functions for each invariant to check.
///
/// # Errors
///
/// Returns [`Llvm2Error`] if the next-state function fails to compile.
/// Individual invariant failures do NOT cause an error; check
/// [`CompiledBfsStep::invariants_failed`] for the count.
///
/// Part of #4197: robust invariant index remapping on partial compile failure.
pub fn compile_bfs_step(
    action_name: &str,
    next_state_func: &tla_tir::bytecode::BytecodeFunction,
    invariant_funcs: &[&tla_tir::bytecode::BytecodeFunction],
) -> Result<CompiledBfsStep, Llvm2Error> {
    let next_state_name = format!("{action_name}_next");
    let next_state = compile_next_state(next_state_func, &next_state_name)?;

    let mut invariants = Vec::with_capacity(invariant_funcs.len());
    let mut invariants_compiled = 0usize;
    let mut invariants_failed = 0usize;
    for (i, inv_func) in invariant_funcs.iter().enumerate() {
        let inv_name = format!("{action_name}_inv_{i}");
        match compile_invariant(inv_func, &inv_name) {
            Ok(compiled) => {
                invariants.push(Some(compiled));
                invariants_compiled += 1;
            }
            Err(_) => {
                invariants.push(None);
                invariants_failed += 1;
            }
        }
    }

    Ok(CompiledBfsStep {
        action_name: action_name.to_string(),
        next_state,
        invariants,
        invariants_compiled,
        invariants_failed,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "native")]
    use crate::bfs_level::{Llvm2InvariantStatus, Llvm2SuccessorArena};
    use tla_tir::bytecode::{BytecodeFunction, Opcode};
    use tmir::constant::Constant;
    use tmir::inst::{BinOp, CastOp, Inst};
    use tmir::ty::{FuncTy, Ty};
    use tmir::value::{BlockId, FuncId, StructId, ValueId};
    use tmir::{Block, FieldDef, Function, InstrNode, StructDef};

    fn make_return_42_module() -> Module {
        let mut module = Module::new("ret42");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "main", ft, entry);
        let mut block = Block::new(entry);
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn test_tmir_dump_env_blank_does_not_match_every_module() {
        assert!(!should_dump_tmir("", "ret42"));
        assert!(!should_dump_tmir("   \t\n", "ret42"));
        assert!(should_dump_tmir("ret", "ret42"));
        assert!(should_dump_tmir("foo, ret", "ret42"));
    }

    #[cfg(feature = "native")]
    fn jit_callout_struct(id: StructId) -> StructDef {
        StructDef {
            id,
            name: "JitCallOut".to_string(),
            fields: vec![
                FieldDef {
                    name: "status".to_string(),
                    ty: Ty::U8,
                    offset: None,
                },
                FieldDef {
                    name: "value".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
                FieldDef {
                    name: "err_kind".to_string(),
                    ty: Ty::U8,
                    offset: None,
                },
                FieldDef {
                    name: "err_span_start".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: "err_span_end".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: "err_file_id".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: "conjuncts_passed".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
        }
    }

    #[cfg(feature = "native")]
    fn make_bfs_test_action_module(name: &str, enabled: i64, write_value: Option<i64>) -> Module {
        let mut module = Module::new(name);
        let callout = StructId::new(0);
        module.add_struct(jit_callout_struct(callout));
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), name, ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(0), Ty::Ptr)
            .with_param(ValueId::new(1), Ty::Ptr)
            .with_param(ValueId::new(2), Ty::Ptr)
            .with_param(ValueId::new(3), Ty::U32);

        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(4)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 0,
                value: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(enabled)),
            })
            .with_result(ValueId::new(6)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 1,
                value: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
        );

        if let Some(value) = write_value {
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(8)),
            );
            block.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: ValueId::new(2),
                    indices: vec![ValueId::new(8)],
                })
                .with_result(ValueId::new(9)),
            );
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(i128::from(value)),
                })
                .with_result(ValueId::new(10)),
            );
            block.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(9),
                value: ValueId::new(10),
                volatile: false,
                align: None,
            }));
        }

        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[cfg(feature = "native")]
    fn make_native_action_calls_i32_gep_state_sum_module(name: &str) -> Module {
        let mut module = Module::new(name);
        let callout = StructId::new(0);
        module.add_struct(jit_callout_struct(callout));
        let action_ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
            returns: vec![],
            is_vararg: false,
        });
        let helper_ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

        let action_entry = BlockId::new(0);
        let mut action = Function::new(FuncId::new(0), name, action_ft, action_entry);
        let mut action_block = Block::new(action_entry)
            .with_param(ValueId::new(0), Ty::Ptr)
            .with_param(ValueId::new(1), Ty::Ptr)
            .with_param(ValueId::new(2), Ty::Ptr)
            .with_param(ValueId::new(3), Ty::U32);

        action_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(4)),
        );
        action_block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 0,
                value: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
        );
        action_block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![
                    ValueId::new(0),
                    ValueId::new(1),
                    ValueId::new(2),
                    ValueId::new(3),
                ],
            })
            .with_result(ValueId::new(6)),
        );
        action_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(7)),
        );
        action_block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 1,
                value: ValueId::new(7),
            })
            .with_result(ValueId::new(8)),
        );
        action_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(9)),
        );
        action_block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(2),
                indices: vec![ValueId::new(9)],
            })
            .with_result(ValueId::new(10)),
        );
        action_block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: ValueId::new(10),
            value: ValueId::new(6),
            volatile: false,
            align: None,
        }));
        action_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        action.blocks.push(action_block);
        module.add_function(action);

        let helper_entry = BlockId::new(1);
        let helper_name = format!("{name}_state_sum");
        let mut helper = Function::new(FuncId::new(1), helper_name, helper_ft, helper_entry);
        let mut helper_block = Block::new(helper_entry)
            .with_param(ValueId::new(20), Ty::Ptr)
            .with_param(ValueId::new(21), Ty::Ptr)
            .with_param(ValueId::new(22), Ty::Ptr)
            .with_param(ValueId::new(23), Ty::U32);
        helper_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(24)),
        );
        helper_block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(21),
                indices: vec![ValueId::new(24)],
            })
            .with_result(ValueId::new(25)),
        );
        helper_block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(25),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(26)),
        );
        helper_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(27)),
        );
        helper_block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(21),
                indices: vec![ValueId::new(27)],
            })
            .with_result(ValueId::new(28)),
        );
        helper_block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(28),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(29)),
        );
        helper_block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(26),
                rhs: ValueId::new(29),
            })
            .with_result(ValueId::new(30)),
        );
        helper_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(30)],
        }));
        helper.blocks.push(helper_block);
        module.add_function(helper);
        module
    }

    #[cfg(feature = "native")]
    fn push_const_int(block: &mut Block, next: &mut u32, ty: Ty, value: i128) -> ValueId {
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::Const {
                ty,
                value: Constant::Int(value),
            })
            .with_result(result),
        );
        result
    }

    #[cfg(feature = "native")]
    fn push_i64_gep(block: &mut Block, next: &mut u32, base: ValueId, index: i64) -> ValueId {
        let index_value = push_const_int(block, next, Ty::I64, i128::from(index));
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![index_value],
            })
            .with_result(result),
        );
        result
    }

    #[cfg(feature = "native")]
    fn push_i64_load(block: &mut Block, next: &mut u32, ptr: ValueId) -> ValueId {
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr,
                volatile: false,
                align: None,
            })
            .with_result(result),
        );
        result
    }

    #[cfg(feature = "native")]
    fn push_i64_store(block: &mut Block, ptr: ValueId, value: ValueId) {
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr,
            value,
            volatile: false,
            align: None,
        }));
    }

    #[cfg(feature = "native")]
    fn push_i64_add(block: &mut Block, next: &mut u32, lhs: ValueId, rhs: ValueId) -> ValueId {
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs,
                rhs,
            })
            .with_result(result),
        );
        result
    }

    #[cfg(feature = "native")]
    fn make_native_action_calls_compact_retbuf_helper_module(name: &str, slots: u32) -> Module {
        assert!(slots >= 2);

        let mut module = Module::new(name);
        let callout = StructId::new(0);
        module.add_struct(jit_callout_struct(callout));
        let action_ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
            returns: vec![],
            is_vararg: false,
        });
        let helper_ft = module.add_func_type(FuncTy {
            params: vec![
                Ty::Ptr,
                Ty::Ptr,
                Ty::Ptr,
                Ty::U32,
                Ty::Ptr,
                Ty::I64,
                Ty::I64,
                Ty::I64,
                Ty::I64,
                Ty::I64,
            ],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

        let action_entry = BlockId::new(0);
        let mut action = Function::new(FuncId::new(0), name, action_ft, action_entry);
        let mut action_block = Block::new(action_entry)
            .with_param(ValueId::new(0), Ty::Ptr)
            .with_param(ValueId::new(1), Ty::Ptr)
            .with_param(ValueId::new(2), Ty::Ptr)
            .with_param(ValueId::new(3), Ty::U32);
        let mut next = 4;

        let ok = push_const_int(&mut action_block, &mut next, Ty::U8, 0);
        action_block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 0,
                value: ok,
            })
            .with_result(ValueId::new(next)),
        );
        next += 1;

        let count = push_const_int(&mut action_block, &mut next, Ty::I32, i128::from(slots));
        let retbuf = ValueId::new(next);
        next += 1;
        action_block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(count),
                align: None,
            })
            .with_result(retbuf),
        );

        let state_0_ptr = push_i64_gep(&mut action_block, &mut next, ValueId::new(1), 0);
        let state_0 = push_i64_load(&mut action_block, &mut next, state_0_ptr);
        let state_1_ptr = push_i64_gep(&mut action_block, &mut next, ValueId::new(1), 1);
        let state_1 = push_i64_load(&mut action_block, &mut next, state_1_ptr);
        let seven = push_const_int(&mut action_block, &mut next, Ty::I64, 7);
        let eleven = push_const_int(&mut action_block, &mut next, Ty::I64, 11);
        let thirteen = push_const_int(&mut action_block, &mut next, Ty::I64, 13);

        let encoded_retbuf = ValueId::new(next);
        next += 1;
        action_block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![
                    ValueId::new(0),
                    ValueId::new(1),
                    ValueId::new(2),
                    ValueId::new(3),
                    retbuf,
                    state_0,
                    state_1,
                    seven,
                    eleven,
                    thirteen,
                ],
            })
            .with_result(encoded_retbuf),
        );
        let returned_retbuf = ValueId::new(next);
        next += 1;
        action_block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: encoded_retbuf,
            })
            .with_result(returned_retbuf),
        );

        let first_ptr = push_i64_gep(&mut action_block, &mut next, returned_retbuf, 0);
        let first = push_i64_load(&mut action_block, &mut next, first_ptr);
        let last_ptr = push_i64_gep(
            &mut action_block,
            &mut next,
            returned_retbuf,
            i64::from(slots - 1),
        );
        let last = push_i64_load(&mut action_block, &mut next, last_ptr);
        let out_0_ptr = push_i64_gep(&mut action_block, &mut next, ValueId::new(2), 0);
        push_i64_store(&mut action_block, out_0_ptr, first);
        let out_1_ptr = push_i64_gep(&mut action_block, &mut next, ValueId::new(2), 1);
        push_i64_store(&mut action_block, out_1_ptr, last);

        let enabled = push_const_int(&mut action_block, &mut next, Ty::I64, 1);
        action_block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 1,
                value: enabled,
            })
            .with_result(ValueId::new(next)),
        );
        action_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        action.blocks.push(action_block);
        module.add_function(action);

        let helper_entry = BlockId::new(1);
        let helper_name = format!("{name}_fill_compact_retbuf");
        let mut helper = Function::new(FuncId::new(1), helper_name, helper_ft, helper_entry);
        let mut helper_block = Block::new(helper_entry)
            .with_param(ValueId::new(100), Ty::Ptr)
            .with_param(ValueId::new(101), Ty::Ptr)
            .with_param(ValueId::new(102), Ty::Ptr)
            .with_param(ValueId::new(103), Ty::U32)
            .with_param(ValueId::new(104), Ty::Ptr)
            .with_param(ValueId::new(105), Ty::I64)
            .with_param(ValueId::new(106), Ty::I64)
            .with_param(ValueId::new(107), Ty::I64)
            .with_param(ValueId::new(108), Ty::I64)
            .with_param(ValueId::new(109), Ty::I64);
        let mut helper_next = 110;
        let sum_01 = push_i64_add(
            &mut helper_block,
            &mut helper_next,
            ValueId::new(105),
            ValueId::new(106),
        );
        let sum_012 = push_i64_add(
            &mut helper_block,
            &mut helper_next,
            sum_01,
            ValueId::new(107),
        );
        let sum_0123 = push_i64_add(
            &mut helper_block,
            &mut helper_next,
            sum_012,
            ValueId::new(108),
        );
        let base = push_i64_add(
            &mut helper_block,
            &mut helper_next,
            sum_0123,
            ValueId::new(109),
        );

        for slot in 0..slots {
            let slot_ptr = push_i64_gep(
                &mut helper_block,
                &mut helper_next,
                ValueId::new(104),
                i64::from(slot),
            );
            let value = if slot == 0 {
                base
            } else {
                let offset = push_const_int(
                    &mut helper_block,
                    &mut helper_next,
                    Ty::I64,
                    i128::from(slot),
                );
                push_i64_add(&mut helper_block, &mut helper_next, base, offset)
            };
            push_i64_store(&mut helper_block, slot_ptr, value);
        }

        let ret = ValueId::new(helper_next);
        helper_block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: ValueId::new(104),
            })
            .with_result(ret),
        );
        helper_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![ret] }));
        helper.blocks.push(helper_block);
        module.add_function(helper);
        module
    }

    #[cfg(feature = "native")]
    fn make_bfs_test_invariant_eq_module(name: &str, expected_value: i64) -> Module {
        let mut module = Module::new(name);
        let callout = StructId::new(0);
        module.add_struct(jit_callout_struct(callout));
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::U32],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), name, ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(0), Ty::Ptr)
            .with_param(ValueId::new(1), Ty::Ptr)
            .with_param(ValueId::new(2), Ty::U32);

        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(3)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 0,
                value: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(5)),
        );
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(1),
                indices: vec![ValueId::new(5)],
            })
            .with_result(ValueId::new(6)),
        );
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(6),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(7)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(expected_value)),
            })
            .with_result(ValueId::new(8)),
        );
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: tmir::inst::ICmpOp::Eq,
                ty: Ty::I64,
                lhs: ValueId::new(7),
                rhs: ValueId::new(8),
            })
            .with_result(ValueId::new(9)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(10)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(11)),
        );
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: ValueId::new(9),
                then_val: ValueId::new(10),
                else_val: ValueId::new(11),
            })
            .with_result(ValueId::new(12)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(callout),
                aggregate: ValueId::new(0),
                field: 1,
                value: ValueId::new(12),
            })
            .with_result(ValueId::new(13)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    extern "C" fn overlay_add_one(value: i64) -> i64 {
        value + 1
    }

    extern "C" fn overlay_add_two(value: i64) -> i64 {
        value + 2
    }

    #[test]
    fn test_compile_module_o1() {
        let module = make_return_42_module();
        let compiled = compile_module(&module).expect("should compile");
        assert_eq!(compiled.name, "ret42");
        assert_eq!(compiled.stats.functions, 1);
        // Verify LLVM IR was emitted.
        assert!(compiled.llvm_ir.contains("define i64 @main()"));
        assert!(compiled.llvm_ir.contains("ret i64 %0"));
    }

    #[test]
    fn test_compile_module_ir_has_module_header() {
        let module = make_return_42_module();
        let compiled = compile_module(&module).expect("should compile");
        assert!(compiled.llvm_ir.contains("; ModuleID = 'ret42'"));
        assert!(compiled.llvm_ir.contains("source_filename = \"ret42\""));
    }

    #[test]
    fn test_native_available_matches_feature() {
        // is_native_available() reflects whether the `native` feature is compiled in.
        let expected = cfg!(feature = "native");
        assert_eq!(is_native_available(), expected);
    }

    #[test]
    fn test_native_fused_local_dedup_disable_env_gate() {
        use std::ffi::OsStr;

        assert!(!native_fused_local_dedup_enabled_for_env(None, None));
        assert!(native_fused_local_dedup_enabled_for_env(
            None,
            Some(OsStr::new(""))
        ));
        assert!(native_fused_local_dedup_enabled_for_env(
            None,
            Some(OsStr::new("1"))
        ));
        assert!(!native_fused_local_dedup_enabled_for_env(
            Some(OsStr::new("")),
            Some(OsStr::new("1"))
        ));
        assert!(!native_fused_local_dedup_enabled_for_env(
            Some(OsStr::new("1")),
            Some(OsStr::new("1"))
        ));
        assert!(native_fused_local_dedup_enabled_for_env(
            Some(OsStr::new("0")),
            Some(OsStr::new("1"))
        ));
    }

    #[test]
    fn test_native_post_ra_opt_disable_env_gate() {
        use std::ffi::OsStr;

        assert!(native_post_ra_opt_enabled_for_env(OptLevel::O3, None));
        assert!(!native_post_ra_opt_enabled_for_env(OptLevel::O1, None));
        assert!(native_post_ra_opt_enabled_for_env(
            OptLevel::O3,
            Some(OsStr::new("0"))
        ));
        assert!(!native_post_ra_opt_enabled_for_env(
            OptLevel::O3,
            Some(OsStr::new("1"))
        ));
        assert!(!native_post_ra_opt_enabled_for_env(
            OptLevel::O3,
            Some(OsStr::new(""))
        ));
    }

    // =========================================================================
    // End-to-end pipeline tests: BytecodeFunction -> tMIR -> LLVM IR
    // =========================================================================

    /// Build a bytecode function for the invariant: x > 0
    fn make_x_gt_zero_invariant() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("Inv_x_gt_0".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = state[0] (x)
        func.emit(Opcode::LoadImm { rd: 1, value: 0 }); // r1 = 0
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        }); // r2 = (x > 0)
        func.emit(Opcode::Ret { rs: 2 }); // return r2
        func
    }

    /// Build a bytecode function for the next-state: x' = x + 1
    fn make_x_incr_next_state() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("Next_x_incr".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = state[0] (x)
        func.emit(Opcode::LoadImm { rd: 1, value: 1 }); // r1 = 1
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        }); // r2 = x + 1
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 }); // state_out[0] = r2
        func.emit(Opcode::LoadImm { rd: 3, value: 1 }); // r3 = true
        func.emit(Opcode::Ret { rs: 3 }); // return true
        func
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_requires_action() {
        let err = compile_bfs_level_native_actions_only(1, &[], OptLevel::O1)
            .expect_err("native BFS level must reject empty action set");
        assert!(matches!(err, Llvm2Error::InvalidModule(_)));
    }

    #[cfg(feature = "native")]
    fn assert_compile_bfs_level_native_action_only_runs_fused_parent_loop(
        parent_opt_level: OptLevel,
        action_symbol: &str,
    ) {
        let action_lib = compile_module_native(
            &make_bfs_test_action_module(action_symbol, 1, Some(7)),
            OptLevel::O1,
        )
        .expect("compile native action");
        let action = Llvm2BfsLevelNativeAction::new(
            ActionDescriptor {
                name: "fused".to_string(),
                action_idx: 0,
                binding_values: Vec::new(),
                formal_values: Vec::new(),
                read_vars: vec![0],
                write_vars: vec![0],
            },
            action_lib,
            action_symbol,
        );

        let mut level = compile_bfs_level_native_actions_only(1, &[action], parent_opt_level)
            .expect("compile action-only native BFS level");
        let local_dedup_enabled = native_fused_local_dedup_enabled();
        assert!(level.capabilities().native_fused_loop);
        assert_eq!(level.metadata().local_dedup, local_dedup_enabled);
        assert_eq!(level.capabilities().local_dedup, local_dedup_enabled);
        assert_eq!(level.action_count(), 1);
        assert_eq!(level.state_constraint_count(), 0);
        assert!(!level.capabilities().state_constraints);
        assert_eq!(level.invariant_count(), 0);

        let mut out = Llvm2SuccessorArena::new(1);
        let outcome = level
            .run_level_arena(&[10, 20], 2, &mut out)
            .expect("run native BFS level");
        assert_eq!(outcome.parents_processed, 2);
        assert_eq!(outcome.total_generated, 2);
        let expected_successors: &[i64] = if local_dedup_enabled { &[7] } else { &[7, 7] };
        assert_eq!(outcome.total_new, expected_successors.len() as u64);
        assert_eq!(out.states_flat(), expected_successors);
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_action_only_runs_fused_parent_loop() {
        assert_compile_bfs_level_native_action_only_runs_fused_parent_loop(
            OptLevel::O1,
            "bfs_native_fused_action_o1",
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_action_only_runs_fused_parent_loop_o3() {
        assert_compile_bfs_level_native_action_only_runs_fused_parent_loop(
            OptLevel::O3,
            "bfs_native_fused_action_o3",
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_checks_invariants() {
        let action_lib = compile_module_native(
            &make_bfs_test_action_module("bfs_native_fused_action_for_inv", 1, Some(7)),
            OptLevel::O1,
        )
        .expect("compile native action");
        let invariant_lib = compile_module_native(
            &make_bfs_test_invariant_eq_module("bfs_native_fused_inv_eq_7", 7),
            OptLevel::O1,
        )
        .expect("compile native invariant");
        let action = Llvm2BfsLevelNativeAction::new(
            ActionDescriptor {
                name: "fused".to_string(),
                action_idx: 0,
                binding_values: Vec::new(),
                formal_values: Vec::new(),
                read_vars: vec![0],
                write_vars: vec![0],
            },
            action_lib,
            "bfs_native_fused_action_for_inv",
        );
        let invariant = Llvm2BfsLevelNativeInvariant::new(
            InvariantDescriptor {
                name: "slot0_eq_7".to_string(),
                invariant_idx: 3,
            },
            invariant_lib,
            "bfs_native_fused_inv_eq_7",
        );

        let mut level = compile_bfs_level_native(1, &[action], &[invariant], OptLevel::O1)
            .expect("compile invariant-checking native BFS level");
        let local_dedup_enabled = native_fused_local_dedup_enabled();
        assert!(level.capabilities().native_fused_loop);
        assert_eq!(level.metadata().local_dedup, local_dedup_enabled);
        assert_eq!(level.capabilities().local_dedup, local_dedup_enabled);
        assert_eq!(level.state_constraint_count(), 0);
        assert!(!level.capabilities().state_constraints);
        assert_eq!(level.invariant_count(), 1);

        let mut out = Llvm2SuccessorArena::new(1);
        let outcome = level
            .run_level_arena(&[10, 20], 2, &mut out)
            .expect("run invariant-checking native BFS level");
        assert_eq!(outcome.parents_processed, 2);
        assert_eq!(outcome.total_generated, 2);
        assert_eq!(outcome.total_new, if local_dedup_enabled { 1 } else { 2 });
        assert_eq!(outcome.invariant, Llvm2InvariantStatus::Passed);
        let expected_successors: &[i64] = if local_dedup_enabled { &[7] } else { &[7, 7] };
        assert_eq!(out.states_flat(), expected_successors);
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_reports_invariant_failure() {
        let action_lib = compile_module_native(
            &make_bfs_test_action_module("bfs_native_fused_action_for_inv_fail", 1, Some(7)),
            OptLevel::O1,
        )
        .expect("compile native action");
        let invariant_lib = compile_module_native(
            &make_bfs_test_invariant_eq_module("bfs_native_fused_inv_eq_8", 8),
            OptLevel::O1,
        )
        .expect("compile native invariant");
        let action = Llvm2BfsLevelNativeAction::new(
            ActionDescriptor {
                name: "fused".to_string(),
                action_idx: 0,
                binding_values: Vec::new(),
                formal_values: Vec::new(),
                read_vars: vec![0],
                write_vars: vec![0],
            },
            action_lib,
            "bfs_native_fused_action_for_inv_fail",
        );
        let invariant = Llvm2BfsLevelNativeInvariant::new(
            InvariantDescriptor {
                name: "slot0_eq_8".to_string(),
                invariant_idx: 5,
            },
            invariant_lib,
            "bfs_native_fused_inv_eq_8",
        );

        let mut level = compile_bfs_level_native(1, &[action], &[invariant], OptLevel::O1)
            .expect("compile invariant-checking native BFS level");
        let mut out = Llvm2SuccessorArena::new(1);
        let outcome = level
            .run_level_arena(&[10, 20], 2, &mut out)
            .expect("run invariant-checking native BFS level");

        assert_eq!(outcome.parents_processed, 1);
        assert_eq!(outcome.total_generated, 1);
        assert_eq!(outcome.total_new, 1);
        assert_eq!(out.states_flat(), &[7]);
        assert_eq!(
            outcome.invariant,
            Llvm2InvariantStatus::Failed {
                parent_index: 0,
                invariant_index: 5,
                successor_index: 0,
            }
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_with_state_constraints_filters_successors() {
        let action_7_lib = compile_module_native(
            &make_bfs_test_action_module("bfs_native_constraint_action_7", 1, Some(7)),
            OptLevel::O1,
        )
        .expect("compile rejected native action");
        let action_8_lib = compile_module_native(
            &make_bfs_test_action_module("bfs_native_constraint_action_8", 1, Some(8)),
            OptLevel::O1,
        )
        .expect("compile accepted native action");
        let constraint_lib = compile_module_native(
            &make_bfs_test_invariant_eq_module("bfs_native_state_constraint_eq_8", 8),
            OptLevel::O1,
        )
        .expect("compile native state constraint");
        let invariant_lib = compile_module_native(
            &make_bfs_test_invariant_eq_module("bfs_native_constraint_inv_eq_8", 8),
            OptLevel::O1,
        )
        .expect("compile native invariant");

        let actions = [
            Llvm2BfsLevelNativeAction::new(
                ActionDescriptor {
                    name: "emit7".to_string(),
                    action_idx: 0,
                    binding_values: Vec::new(),
                    formal_values: Vec::new(),
                    read_vars: vec![0],
                    write_vars: vec![0],
                },
                action_7_lib,
                "bfs_native_constraint_action_7",
            ),
            Llvm2BfsLevelNativeAction::new(
                ActionDescriptor {
                    name: "emit8".to_string(),
                    action_idx: 1,
                    binding_values: Vec::new(),
                    formal_values: Vec::new(),
                    read_vars: vec![0],
                    write_vars: vec![0],
                },
                action_8_lib,
                "bfs_native_constraint_action_8",
            ),
        ];
        let state_constraints = [Llvm2BfsLevelNativeStateConstraint::new(
            "slot0_eq_8",
            4,
            constraint_lib,
            "bfs_native_state_constraint_eq_8",
        )];
        let invariants = [Llvm2BfsLevelNativeInvariant::new(
            InvariantDescriptor {
                name: "slot0_eq_8".to_string(),
                invariant_idx: 6,
            },
            invariant_lib,
            "bfs_native_constraint_inv_eq_8",
        )];

        let mut level = compile_bfs_level_native_with_state_constraints(
            1,
            &actions,
            &state_constraints,
            &invariants,
            OptLevel::O1,
        )
        .expect("compile state-constrained native BFS level");
        assert!(level.capabilities().native_fused_loop);
        assert!(level.capabilities().state_constraints);
        assert_eq!(level.action_count(), 2);
        assert_eq!(level.state_constraint_count(), 1);
        assert_eq!(level.invariant_count(), 1);

        let mut out = Llvm2SuccessorArena::new(1);
        let outcome = level
            .run_level_arena(&[100], 1, &mut out)
            .expect("run state-constrained native BFS level");

        assert_eq!(outcome.parents_processed, 1);
        assert_eq!(outcome.total_generated, 1);
        assert_eq!(outcome.total_new, 1);
        assert_eq!(outcome.invariant, Llvm2InvariantStatus::Passed);
        assert_eq!(out.states_flat(), &[8]);
        assert_eq!(out.parent_indices(), &[0]);
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_builds_address_callback_targets() {
        let action_lib = compile_module_native(
            &make_bfs_test_action_module("bfs_native_overlay_action", 1, Some(7)),
            OptLevel::O1,
        )
        .expect("compile native action");
        let constraint_lib = compile_module_native(
            &make_bfs_test_invariant_eq_module("bfs_native_overlay_constraint", 7),
            OptLevel::O1,
        )
        .expect("compile native state constraint");
        let invariant_lib = compile_module_native(
            &make_bfs_test_invariant_eq_module("bfs_native_overlay_invariant", 7),
            OptLevel::O1,
        )
        .expect("compile native invariant");

        let actions = [Llvm2BfsLevelNativeAction::new(
            ActionDescriptor {
                name: "overlay_action".to_string(),
                action_idx: 0,
                binding_values: Vec::new(),
                formal_values: Vec::new(),
                read_vars: vec![0],
                write_vars: vec![0],
            },
            action_lib,
            "bfs_native_overlay_action",
        )];
        let state_constraints = [Llvm2BfsLevelNativeStateConstraint::new(
            "overlay_constraint",
            9,
            constraint_lib,
            "bfs_native_overlay_constraint",
        )];
        let invariants = [Llvm2BfsLevelNativeInvariant::new(
            InvariantDescriptor {
                name: "overlay_invariant".to_string(),
                invariant_idx: 12,
            },
            invariant_lib,
            "bfs_native_overlay_invariant",
        )];

        let targets = build_native_bfs_callback_targets(&actions, &state_constraints, &invariants)
            .expect("build callback address targets");

        assert_eq!(targets.action_addresses.len(), 1);
        assert_ne!(targets.action_addresses[0], 0);
        assert_eq!(targets.state_constraints.len(), 1);
        assert_eq!(targets.state_constraints[0].constraint_idx, 9);
        assert_ne!(targets.state_constraints[0].address, 0);
        assert_eq!(targets.invariants.len(), 1);
        assert_eq!(targets.invariants[0].invariant_idx, 12);
        assert_ne!(targets.invariants[0].address, 0);
        assert_eq!(targets.extern_libraries.len(), 3);
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_compile_bfs_level_native_test_action_direct_call_runs() {
        let action_lib = compile_module_native(
            &make_bfs_test_action_module("bfs_native_direct", 1, Some(7)),
            OptLevel::O1,
        )
        .expect("compile native action");
        let mut callout = crate::runtime_abi::JitCallOut::default();
        let mut direct_out = [0_i64; 1];
        // SAFETY: the symbol was produced by compile_module_native above and
        // uses the test JitNextStateFn-compatible signature.
        let action_fn: crate::runtime_abi::JitNextStateFn =
            unsafe { std::mem::transmute(action_lib.get_symbol("bfs_native_direct").unwrap()) };
        unsafe {
            action_fn(&mut callout, [10_i64].as_ptr(), direct_out.as_mut_ptr(), 1);
        }
        assert_eq!(callout.status, crate::runtime_abi::JitStatus::Ok);
        assert_eq!(callout.value, 1);
        assert_eq!(direct_out, [7]);
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_native_next_state_i32_gep_state_load_preserves_pointer_width() {
        let action_lib = compile_module_native(
            &make_native_action_calls_i32_gep_state_sum_module("bfs_native_i32_gep_state_sum"),
            OptLevel::O1,
        )
        .expect("compile native action with i32-indexed state loads");
        let mut callout = crate::runtime_abi::JitCallOut::default();
        let state = [123_i64, 877_i64];
        let mut direct_out = [0_i64; 2];
        // SAFETY: the symbol was produced by compile_module_native above and
        // uses the JitNextStateFn-compatible native next-state ABI.
        let action_fn: crate::runtime_abi::JitNextStateFn = unsafe {
            std::mem::transmute(
                action_lib
                    .get_symbol("bfs_native_i32_gep_state_sum")
                    .unwrap(),
            )
        };
        unsafe {
            action_fn(&mut callout, state.as_ptr(), direct_out.as_mut_ptr(), 2);
        }
        assert_eq!(callout.status, crate::runtime_abi::JitStatus::Ok);
        assert_eq!(callout.value, 1);
        assert_eq!(direct_out[0], 1000);
    }

    #[cfg(feature = "native")]
    fn run_native_compact_retbuf_helper_call(slots: u32, symbol: &str) {
        let action_lib = compile_module_native(
            &make_native_action_calls_compact_retbuf_helper_module(symbol, slots),
            OptLevel::O1,
        )
        .expect("compile native action with compact return-buffer helper call");
        let mut callout = crate::runtime_abi::JitCallOut::default();
        let state = [3_i64, 5_i64];
        let mut direct_out = [0_i64; 2];
        // SAFETY: the symbol was produced by compile_module_native above and
        // uses the JitNextStateFn-compatible native next-state ABI.
        let action_fn: crate::runtime_abi::JitNextStateFn =
            unsafe { std::mem::transmute(action_lib.get_symbol(symbol).unwrap()) };
        unsafe {
            action_fn(&mut callout, state.as_ptr(), direct_out.as_mut_ptr(), 2);
        }
        assert_eq!(callout.status, crate::runtime_abi::JitStatus::Ok);
        assert_eq!(callout.value, 1);
        assert_eq!(direct_out, [39, 39 + i64::from(slots - 1)]);
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_native_next_state_compact_retbuf_helper_call_2_slots() {
        run_native_compact_retbuf_helper_call(2, "bfs_native_compact_retbuf_2_slots");
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_native_next_state_compact_retbuf_helper_call_21_slots() {
        run_native_compact_retbuf_helper_call(21, "bfs_native_compact_retbuf_21_slots");
    }

    #[test]
    fn test_pipeline_invariant_bytecode_to_llvm_ir() {
        let func = make_x_gt_zero_invariant();
        let compiled = compile_invariant(&func, "inv_x_gt_0").expect("should compile");

        // Module name matches.
        assert_eq!(compiled.name, "inv_x_gt_0");

        // LLVM IR should contain the function definition.
        let ir = &compiled.llvm_ir;
        assert!(
            ir.contains("define void @inv_x_gt_0("),
            "IR should define the invariant function. IR:\n{ir}"
        );

        // Should contain GEP for state variable access (LoadVar -> GEP + Load).
        assert!(
            ir.contains("getelementptr"),
            "IR should contain GEP for state access. IR:\n{ir}"
        );

        // Should contain integer comparison (GtInt -> icmp sgt).
        assert!(
            ir.contains("icmp sgt"),
            "IR should contain signed-greater-than comparison. IR:\n{ir}"
        );

        // Should contain return.
        assert!(
            ir.contains("ret void"),
            "Invariant function should return void (writes to JitCallOut). IR:\n{ir}"
        );

        // Should have the module header.
        assert!(ir.contains("; ModuleID = 'inv_x_gt_0'"));

        // Stats should reflect the content.
        assert_eq!(compiled.stats.functions, 1);
        assert!(compiled.stats.instructions > 0, "should have instructions");
    }

    #[test]
    fn test_pipeline_next_state_bytecode_to_llvm_ir() {
        let func = make_x_incr_next_state();
        let compiled = compile_next_state(&func, "next_x_incr").expect("should compile");

        let ir = &compiled.llvm_ir;

        // Next-state function should have 4 params (out, state_in, state_out, state_len).
        assert!(
            ir.contains("define void @next_x_incr("),
            "IR should define the next-state function. IR:\n{ir}"
        );

        // Should contain overflow-checked addition (AddInt -> sadd.with.overflow).
        assert!(
            ir.contains("sadd.with.overflow"),
            "IR should contain overflow-checked addition. IR:\n{ir}"
        );

        // Should contain store to state_out (StoreVar -> GEP + Store).
        // Count GEPs — should have at least 2 (one for LoadVar read, one for StoreVar write).
        let gep_count = ir.matches("getelementptr").count();
        assert!(
            gep_count >= 2,
            "IR should have at least 2 GEPs (LoadVar + StoreVar), found {gep_count}. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_compile_spec_invariant() {
        // Build a BytecodeChunk with one function.
        let mut chunk = BytecodeChunk::new();
        let func = make_x_gt_zero_invariant();
        chunk.functions.push(func);

        let compiled = compile_spec_invariant(&chunk, 0, "spec_inv").expect("should compile spec");

        assert_eq!(compiled.name, "spec_inv");
        assert!(
            compiled.llvm_ir.contains("define void @spec_inv("),
            "IR should define the entrypoint function"
        );
    }

    #[test]
    fn test_pipeline_compile_spec_next_state() {
        let mut chunk = BytecodeChunk::new();
        let func = make_x_incr_next_state();
        chunk.functions.push(func);

        let compiled =
            compile_spec_next_state(&chunk, 0, "spec_next").expect("should compile spec");

        assert_eq!(compiled.name, "spec_next");
        assert!(
            compiled.llvm_ir.contains("define void @spec_next("),
            "IR should define the next-state function"
        );
    }

    #[test]
    fn test_pipeline_compile_bfs_step() {
        let next_func = make_x_incr_next_state();
        let inv_func = make_x_gt_zero_invariant();

        let bfs_step =
            compile_bfs_step("action0", &next_func, &[&inv_func]).expect("should compile BFS step");

        assert_eq!(bfs_step.action_name, "action0");
        assert_eq!(bfs_step.invariants_compiled, 1);
        assert_eq!(bfs_step.invariants_failed, 0);

        // Next-state IR should reference the action name.
        assert!(
            bfs_step.next_state.llvm_ir.contains("action0_next"),
            "Next-state IR should use the action name"
        );

        // Should have exactly one invariant (Some).
        assert_eq!(bfs_step.invariants.len(), 1);
        assert!(bfs_step.invariants[0].is_some());
        assert!(
            bfs_step.invariants[0]
                .as_ref()
                .unwrap()
                .llvm_ir
                .contains("action0_inv_0"),
            "Invariant IR should use the action name and index"
        );
    }

    #[test]
    fn test_pipeline_bfs_step_multiple_invariants() {
        let next_func = make_x_incr_next_state();
        let inv1 = make_x_gt_zero_invariant();

        // Second invariant: x < 100.
        let mut inv2 = BytecodeFunction::new("Inv_x_lt_100".to_string(), 0);
        inv2.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv2.emit(Opcode::LoadImm { rd: 1, value: 100 });
        inv2.emit(Opcode::LtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inv2.emit(Opcode::Ret { rs: 2 });

        let bfs_step = compile_bfs_step("step1", &next_func, &[&inv1, &inv2])
            .expect("should compile BFS step with 2 invariants");

        assert_eq!(bfs_step.invariants.len(), 2);
        assert_eq!(bfs_step.invariants_compiled, 2);
        assert_eq!(bfs_step.invariants_failed, 0);
        assert!(bfs_step.invariants[0]
            .as_ref()
            .unwrap()
            .llvm_ir
            .contains("step1_inv_0"));
        assert!(bfs_step.invariants[1]
            .as_ref()
            .unwrap()
            .llvm_ir
            .contains("step1_inv_1"));

        // Second invariant should use slt (less-than).
        assert!(
            bfs_step.invariants[1]
                .as_ref()
                .unwrap()
                .llvm_ir
                .contains("icmp slt"),
            "Second invariant should contain signed-less-than comparison"
        );
    }

    #[test]
    fn test_pipeline_bfs_step_no_invariants() {
        let next_func = make_x_incr_next_state();

        let bfs_step = compile_bfs_step("no_inv", &next_func, &[])
            .expect("should compile BFS step with no invariants");

        assert_eq!(bfs_step.action_name, "no_inv");
        assert!(bfs_step.invariants.is_empty());
        assert_eq!(bfs_step.invariants_compiled, 0);
        assert_eq!(bfs_step.invariants_failed, 0);
        assert!(!bfs_step.next_state.llvm_ir.is_empty());
    }

    #[test]
    fn test_pipeline_state_access_produces_gep_load_pattern() {
        // Verify that LoadVar produces the expected GEP + Load pattern in LLVM IR,
        // which is critical for correct state buffer access.
        let mut func = BytecodeFunction::new("state_access".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 3 }); // Load slot 3
        func.emit(Opcode::Ret { rs: 0 });

        let compiled = compile_invariant(&func, "state_access").expect("should compile");
        let ir = &compiled.llvm_ir;

        // The GEP index should be 3 (the var_idx).
        assert!(
            ir.contains("getelementptr i64"),
            "Should GEP into i64 state array. IR:\n{ir}"
        );
        assert!(
            ir.contains("load i64"),
            "Should load i64 from state buffer. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_store_var_produces_gep_store_pattern() {
        // Verify that StoreVar produces the expected GEP + Store pattern.
        let mut func = BytecodeFunction::new("state_store".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::StoreVar { var_idx: 2, rs: 0 }); // Store to slot 2
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Ret { rs: 1 });

        let compiled = compile_next_state(&func, "state_store").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should have a store instruction writing to the state buffer.
        assert!(
            ir.contains("store i64"),
            "Should store i64 to state buffer. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_branching_produces_condbr() {
        // Verify that JumpFalse produces a conditional branch in LLVM IR.
        let mut func = BytecodeFunction::new("branch_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // pc 0
        func.emit(Opcode::JumpFalse { rs: 0, offset: 2 }); // pc 1 -> jump to pc 3
        func.emit(Opcode::LoadImm { rd: 1, value: 42 }); // pc 2 (fallthrough)
        func.emit(Opcode::Ret { rs: 1 }); // pc 3 (target: either from fallthrough or jump)

        let compiled = compile_invariant(&func, "branch_test").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain conditional branch.
        assert!(
            ir.contains("br i1"),
            "Should contain conditional branch. IR:\n{ir}"
        );

        // Should have multiple basic blocks (entry + branch targets).
        let bb_count = ir.matches("bb").count();
        assert!(
            bb_count >= 1,
            "Should have multiple basic blocks. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_set_enum_produces_alloca() {
        // Verify that SetEnum produces aggregate allocation in LLVM IR.
        let mut func = BytecodeFunction::new("set_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let compiled = compile_invariant(&func, "set_test").expect("should compile");
        let ir = &compiled.llvm_ir;

        // SetEnum should produce an alloca for the aggregate.
        assert!(
            ir.contains("alloca i64, i32"),
            "SetEnum should produce dynamic alloca for the aggregate. IR:\n{ir}"
        );

        // Should contain ptrtoint (aggregate pointer stored as i64 in register file).
        assert!(
            ir.contains("ptrtoint"),
            "Aggregate pointer should be stored as i64 via ptrtoint. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Boolean/Logic operations
    // =========================================================================

    #[test]
    fn test_pipeline_boolean_and() {
        // And lowers to BinOp::And on i64 values.
        let mut func = BytecodeFunction::new("bool_and".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::And {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "bool_and").expect("should compile");
        let ir = &compiled.llvm_ir;

        // And on i64 emits `and i64` in LLVM IR.
        assert!(
            ir.contains("and i64"),
            "Boolean And should produce `and i64` instruction. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_boolean_or() {
        let mut func = BytecodeFunction::new("bool_or".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Or {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "bool_or").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("or i64"),
            "Boolean Or should produce `or i64` instruction. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_boolean_not() {
        // Not lowers to: icmp eq i64 value, 0 then zext.
        let mut func = BytecodeFunction::new("bool_not".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::Not { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });

        let compiled = compile_invariant(&func, "bool_not").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Not checks value == 0, so we expect icmp eq.
        assert!(
            ir.contains("icmp eq"),
            "Boolean Not should produce `icmp eq` for zero-check. IR:\n{ir}"
        );
        // Result is zero-extended from i1 to i64.
        assert!(
            ir.contains("zext"),
            "Boolean Not should zext the i1 result to i64. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_implies() {
        // Implies lowers to: !lhs || rhs (icmp eq + icmp ne + or + zext).
        let mut func = BytecodeFunction::new("implies".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::Implies {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "implies").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain both eq and ne comparisons for !lhs and rhs bool checks.
        assert!(
            ir.contains("icmp eq"),
            "Implies should contain `icmp eq` for !lhs. IR:\n{ir}"
        );
        assert!(
            ir.contains("icmp ne"),
            "Implies should contain `icmp ne` for rhs bool. IR:\n{ir}"
        );
        // Should produce a boolean or for the final result.
        assert!(
            ir.contains("or i1"),
            "Implies should produce `or i1` for !lhs || rhs. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_equiv() {
        // Equiv lowers to: icmp eq on i64 values + zext.
        let mut func = BytecodeFunction::new("equiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Equiv {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "equiv").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp eq"),
            "Equiv should produce `icmp eq` for equality check. IR:\n{ir}"
        );
        assert!(
            ir.contains("zext"),
            "Equiv should zext the i1 result. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Comparison operations
    // =========================================================================

    #[test]
    fn test_pipeline_comparison_eq() {
        let mut func = BytecodeFunction::new("cmp_eq".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 5 });
        func.emit(Opcode::Eq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "cmp_eq").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp eq"),
            "Eq should produce `icmp eq`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_comparison_neq() {
        let mut func = BytecodeFunction::new("cmp_neq".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 3 });
        func.emit(Opcode::LoadImm { rd: 1, value: 7 });
        func.emit(Opcode::Neq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "cmp_neq").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp ne"),
            "Neq should produce `icmp ne`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_comparison_le() {
        let mut func = BytecodeFunction::new("cmp_le".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 10 });
        func.emit(Opcode::LeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "cmp_le").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp sle"),
            "LeInt should produce `icmp sle`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_comparison_ge() {
        let mut func = BytecodeFunction::new("cmp_ge".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "cmp_ge").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp sge"),
            "GeInt should produce `icmp sge`. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Division and Modulo
    // =========================================================================

    #[test]
    fn test_pipeline_intdiv() {
        // IntDiv lowers to: div-by-zero check + sdiv.
        let mut func = BytecodeFunction::new("intdiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::IntDiv {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "intdiv").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain sdiv for the actual division.
        assert!(
            ir.contains("sdiv"),
            "IntDiv should produce `sdiv` instruction. IR:\n{ir}"
        );
        // Should contain a conditional branch for div-by-zero check.
        assert!(
            ir.contains("br i1"),
            "IntDiv should have conditional branch for zero check. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_modint() {
        // ModInt lowers to: div-by-zero check + srem.
        let mut func = BytecodeFunction::new("modint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::ModInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "modint").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("srem"),
            "ModInt should produce `srem` instruction. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_real_division() {
        // DivInt (real division) lowers to: zero check + exactness check + sdiv.
        let mut func = BytecodeFunction::new("realdiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 12 });
        func.emit(Opcode::LoadImm { rd: 1, value: 4 });
        func.emit(Opcode::DivInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "realdiv").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain both srem (exactness check) and sdiv (actual division).
        assert!(
            ir.contains("srem"),
            "Real division should check exactness with `srem`. IR:\n{ir}"
        );
        assert!(
            ir.contains("sdiv"),
            "Real division should produce `sdiv`. IR:\n{ir}"
        );
        // Should have at least 2 conditional branches (zero check + exactness check).
        let br_count = ir.matches("br i1").count();
        assert!(
            br_count >= 2,
            "Real division should have >=2 conditional branches (zero + exact), found {br_count}. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Negation
    // =========================================================================

    #[test]
    fn test_pipeline_negint() {
        // NegInt lowers to: 0 - value with overflow check (ssub.with.overflow).
        let mut func = BytecodeFunction::new("negint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::NegInt { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });

        let compiled = compile_invariant(&func, "negint").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Negation via 0 - value uses ssub.with.overflow.
        assert!(
            ir.contains("ssub.with.overflow"),
            "NegInt should use `ssub.with.overflow` for overflow-checked negation. IR:\n{ir}"
        );
        // Should have overflow error branch.
        assert!(
            ir.contains("br i1"),
            "NegInt should branch on overflow flag. IR:\n{ir}"
        );
    }

    // =========================================================================
    // CondMove (select instruction)
    // =========================================================================

    #[test]
    fn test_pipeline_condmove() {
        // CondMove lowers to: icmp ne (cond, 0) then select.
        let mut func = BytecodeFunction::new("condmove".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // cond = true
        func.emit(Opcode::LoadImm { rd: 1, value: 99 }); // rd initial
        func.emit(Opcode::LoadImm { rd: 2, value: 42 }); // source value
        func.emit(Opcode::CondMove {
            rd: 1,
            cond: 0,
            rs: 2,
        }); // rd = if cond then source else rd
        func.emit(Opcode::Ret { rs: 1 });

        let compiled = compile_invariant(&func, "condmove").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("select"),
            "CondMove should produce a `select` instruction. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Quantifiers: ForAll and Exists
    // =========================================================================

    #[test]
    fn test_pipeline_forall_quantifier() {
        // ForAll quantifier: \A x \in {1,2}: x > 0
        // Build set {1, 2}, then ForallBegin/ForallNext loop.
        let mut func = BytecodeFunction::new("forall".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // pc 0
        func.emit(Opcode::LoadImm { rd: 1, value: 2 }); // pc 1
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        }); // pc 2: domain = {1,2}
        func.emit(Opcode::ForallBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 5,
        }); // pc 3 -> exit at pc 8
            // body: x > 0
        func.emit(Opcode::LoadImm { rd: 5, value: 0 }); // pc 4
        func.emit(Opcode::GtInt {
            rd: 6,
            r1: 4,
            r2: 5,
        }); // pc 5: binding > 0
        func.emit(Opcode::ForallNext {
            rd: 3,
            r_binding: 4,
            r_body: 6,
            loop_begin: -3,
        }); // pc 6 -> back to pc 3
            // After loop, pc 7 is unreachable but we need a valid instruction.
        func.emit(Opcode::Ret { rs: 3 }); // pc 7: return result
                                          // pc 8 = exit block from ForallBegin
        func.emit(Opcode::Ret { rs: 3 }); // pc 8: return result

        let compiled = compile_invariant(&func, "forall").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Quantifier loops produce multiple basic blocks with br instructions.
        let br_count = ir.matches("br ").count();
        assert!(
            br_count >= 3,
            "ForAll quantifier should produce multiple branches (header, body, back-edge), found {br_count}. IR:\n{ir}"
        );

        // Should have GEP for domain element access.
        assert!(
            ir.contains("getelementptr"),
            "ForAll should access domain elements via GEP. IR:\n{ir}"
        );

        // Should have icmp for loop bound check and body comparison.
        let icmp_count = ir.matches("icmp").count();
        assert!(
            icmp_count >= 2,
            "ForAll should have >=2 icmp instructions (bound check + body comparison), found {icmp_count}. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_exists_quantifier() {
        // Exists quantifier: \E x \in {1,2}: x = 2
        let mut func = BytecodeFunction::new("exists".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // pc 0
        func.emit(Opcode::LoadImm { rd: 1, value: 2 }); // pc 1
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        }); // pc 2: domain = {1,2}
        func.emit(Opcode::ExistsBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 5,
        }); // pc 3 -> exit at pc 8
            // body: x = 2
        func.emit(Opcode::LoadImm { rd: 5, value: 2 }); // pc 4
        func.emit(Opcode::Eq {
            rd: 6,
            r1: 4,
            r2: 5,
        }); // pc 5: binding == 2
        func.emit(Opcode::ExistsNext {
            rd: 3,
            r_binding: 4,
            r_body: 6,
            loop_begin: -3,
        }); // pc 6 -> back to pc 3
        func.emit(Opcode::Ret { rs: 3 }); // pc 7: return result
        func.emit(Opcode::Ret { rs: 3 }); // pc 8: exit block return

        let compiled = compile_invariant(&func, "exists").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Similar structure to ForAll: multiple branches, GEP, icmp.
        let br_count = ir.matches("br ").count();
        assert!(
            br_count >= 3,
            "Exists quantifier should produce multiple branches, found {br_count}. IR:\n{ir}"
        );
        assert!(
            ir.contains("getelementptr"),
            "Exists should access domain elements via GEP. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Sequence operations
    // =========================================================================

    #[test]
    fn test_pipeline_seq_new() {
        // SeqNew allocates an aggregate: slot[0] = length, slot[1..] = elements.
        let mut func = BytecodeFunction::new("seq_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::LoadImm { rd: 2, value: 30 });
        func.emit(Opcode::SeqNew {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let compiled = compile_invariant(&func, "seq_new").expect("should compile");
        let ir = &compiled.llvm_ir;

        // SeqNew uses the same aggregate layout as SetEnum: alloca + ptrtoint.
        assert!(
            ir.contains("alloca i64, i32"),
            "SeqNew should produce dynamic alloca for aggregate. IR:\n{ir}"
        );
        assert!(
            ir.contains("ptrtoint"),
            "SeqNew aggregate pointer should be stored as i64. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Tuple operations
    // =========================================================================

    #[test]
    fn test_pipeline_tuple_new_and_get() {
        // TupleNew + TupleGet: build <<1, 2>> then access element 1.
        let mut func = BytecodeFunction::new("tuple_ops".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 100 });
        func.emit(Opcode::LoadImm { rd: 1, value: 200 });
        func.emit(Opcode::TupleNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::TupleGet {
            rd: 3,
            rs: 2,
            idx: 1,
        }); // 1-indexed: get first element
        func.emit(Opcode::Ret { rs: 3 });

        let compiled = compile_invariant(&func, "tuple_ops").expect("should compile");
        let ir = &compiled.llvm_ir;

        // TupleNew uses same alloca pattern.
        assert!(
            ir.contains("alloca i64, i32"),
            "TupleNew should produce alloca. IR:\n{ir}"
        );
        // TupleGet accesses via GEP (inttoptr + GEP + load).
        assert!(
            ir.contains("inttoptr"),
            "TupleGet should convert i64 back to pointer via inttoptr. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Inter-function calls via BytecodeChunk
    // =========================================================================

    #[test]
    fn test_pipeline_multi_function_chunk() {
        // Build a chunk with two functions: main calls helper.
        // helper(x) = x + 1
        // main: call helper(state[0])
        let mut chunk = BytecodeChunk::new();

        // Function 0 (main): load state var, call func 1, return result.
        let mut main_func = BytecodeFunction::new("main".to_string(), 0);
        main_func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = state[0]
        main_func.emit(Opcode::Call {
            rd: 1,
            op_idx: 1, // call function at index 1
            args_start: 0,
            argc: 1,
        });
        main_func.emit(Opcode::Ret { rs: 1 });
        chunk.functions.push(main_func);

        // Function 1 (helper): r0 = arg, r0 + 1.
        let mut helper_func = BytecodeFunction::new("helper".to_string(), 1);
        helper_func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        helper_func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        helper_func.emit(Opcode::Ret { rs: 2 });
        chunk.functions.push(helper_func);

        let compiled = compile_spec_invariant(&chunk, 0, "multi_func")
            .expect("should compile multi-function chunk");
        let ir = &compiled.llvm_ir;

        // Should define at least 2 functions.
        let define_count = ir.matches("define ").count();
        assert!(
            define_count >= 2,
            "Multi-function chunk should define >=2 functions, found {define_count}. IR:\n{ir}"
        );

        // Should contain a call instruction.
        assert!(
            ir.contains("call "),
            "Main function should call the helper. IR:\n{ir}"
        );

        // Both functions should appear.
        assert!(
            ir.contains("@multi_func"),
            "Entrypoint function should be named. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Subtraction and Multiplication (overflow-checked)
    // =========================================================================

    #[test]
    fn test_pipeline_subint() {
        let mut func = BytecodeFunction::new("subint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::SubInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "subint").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("ssub.with.overflow"),
            "SubInt should use `ssub.with.overflow`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_mulint() {
        let mut func = BytecodeFunction::new("mulint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 7 });
        func.emit(Opcode::LoadImm { rd: 1, value: 6 });
        func.emit(Opcode::MulInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = compile_invariant(&func, "mulint").expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("smul.with.overflow"),
            "MulInt should use `smul.with.overflow`. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Combined pipeline: multiple opcode categories in one function
    // =========================================================================

    #[test]
    fn test_pipeline_combined_arithmetic_and_logic() {
        // Invariant: (state[0] + state[1] > 0) /\ (state[0] >= 0)
        let mut func = BytecodeFunction::new("combined".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = x
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 }); // r1 = y
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        }); // r2 = x + y
        func.emit(Opcode::LoadImm { rd: 3, value: 0 }); // r3 = 0
        func.emit(Opcode::GtInt {
            rd: 4,
            r1: 2,
            r2: 3,
        }); // r4 = (x + y > 0)
        func.emit(Opcode::GeInt {
            rd: 5,
            r1: 0,
            r2: 3,
        }); // r5 = (x >= 0)
        func.emit(Opcode::And {
            rd: 6,
            r1: 4,
            r2: 5,
        }); // r6 = r4 /\ r5
        func.emit(Opcode::Ret { rs: 6 });

        let compiled = compile_invariant(&func, "combined").expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain all expected patterns.
        assert!(
            ir.contains("sadd.with.overflow"),
            "Should have overflow-checked add. IR:\n{ir}"
        );
        assert!(
            ir.contains("icmp sgt"),
            "Should have signed-greater-than comparison. IR:\n{ir}"
        );
        assert!(
            ir.contains("icmp sge"),
            "Should have signed-greater-or-equal comparison. IR:\n{ir}"
        );
        assert!(ir.contains("and i64"), "Should have boolean And. IR:\n{ir}");
        // Should access 2 state variables via GEP.
        let gep_count = ir.matches("getelementptr").count();
        assert!(
            gep_count >= 2,
            "Should GEP for 2 state variables, found {gep_count}. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Native compilation tests: LLVM IR -> object -> dylib -> execute
    // =========================================================================

    #[test]
    fn test_find_llc_available() {
        // Verify that find_llc() locates the LLVM toolchain on this system.
        // If llc is not installed, this test passes trivially (no assertion).
        if let Some(path) = find_llc() {
            assert!(
                path.exists(),
                "find_llc() returned non-existent path: {}",
                path.display()
            );
        }
    }

    #[test]
    fn test_native_compile_and_link_pure_scalar() {
        // End-to-end: hand-written LLVM IR -> llc -> clang -> dlopen -> dlsym -> call.
        // This is a standalone function that takes (i64, i64) -> i64 and returns a + b.
        // No runtime helpers needed.
        if !is_native_available() {
            return; // llc not installed, skip gracefully
        }

        let ir = r#"; ModuleID = 'e2e_scalar'
source_filename = "e2e_scalar"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

define i64 @add_two(i64 %0, i64 %1) {
entry:
  %2 = add i64 %0, %1
  ret i64 %2
}
"#;

        let lib =
            compile_and_link(ir, "e2e_scalar", OptLevel::O1).expect("should compile and link");

        // Load the symbol and call it.
        type AddTwoFn = unsafe extern "C" fn(i64, i64) -> i64;
        let func_ptr = unsafe {
            lib.get_symbol("add_two")
                .expect("should find add_two symbol")
        };
        let add_two: AddTwoFn = unsafe { std::mem::transmute(func_ptr) };

        // Execute and verify.
        let result = unsafe { add_two(17, 25) };
        assert_eq!(result, 42, "add_two(17, 25) should return 42");

        let result2 = unsafe { add_two(-10, 3) };
        assert_eq!(result2, -7, "add_two(-10, 3) should return -7");

        let result3 = unsafe { add_two(0, 0) };
        assert_eq!(result3, 0, "add_two(0, 0) should return 0");
    }

    #[test]
    fn test_native_compile_and_link_comparison() {
        // End-to-end: function that computes (a > b) as i64 (0 or 1).
        if !is_native_available() {
            return;
        }

        let ir = r#"; ModuleID = 'e2e_cmp'
source_filename = "e2e_cmp"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

define i64 @gt_check(i64 %0, i64 %1) {
entry:
  %2 = icmp sgt i64 %0, %1
  %3 = zext i1 %2 to i64
  ret i64 %3
}
"#;

        let lib = compile_and_link(ir, "e2e_cmp", OptLevel::O1).expect("should compile and link");

        type GtCheckFn = unsafe extern "C" fn(i64, i64) -> i64;
        let gt_check: GtCheckFn = unsafe {
            let ptr = lib.get_symbol("gt_check").expect("should find gt_check");
            std::mem::transmute(ptr)
        };

        assert_eq!(unsafe { gt_check(5, 3) }, 1, "5 > 3 should be true (1)");
        assert_eq!(unsafe { gt_check(3, 5) }, 0, "3 > 5 should be false (0)");
        assert_eq!(unsafe { gt_check(5, 5) }, 0, "5 > 5 should be false (0)");
    }

    #[test]
    fn test_native_compile_and_link_state_buffer_access() {
        // End-to-end: function that reads from a state buffer (ptr + GEP + load).
        // Simulates the invariant ABI: fn(state: *const i64, idx: i64) -> i64
        if !is_native_available() {
            return;
        }

        let ir = r#"; ModuleID = 'e2e_state'
source_filename = "e2e_state"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

define i64 @read_state(ptr %0, i64 %1) {
entry:
  %2 = getelementptr i64, ptr %0, i64 %1
  %3 = load i64, ptr %2
  ret i64 %3
}
"#;

        let lib = compile_and_link(ir, "e2e_state", OptLevel::O1).expect("should compile and link");

        type ReadStateFn = unsafe extern "C" fn(*const i64, i64) -> i64;
        let read_state: ReadStateFn = unsafe {
            let ptr = lib
                .get_symbol("read_state")
                .expect("should find read_state");
            std::mem::transmute(ptr)
        };

        let state: [i64; 4] = [100, 200, 300, 400];
        assert_eq!(unsafe { read_state(state.as_ptr(), 0) }, 100);
        assert_eq!(unsafe { read_state(state.as_ptr(), 1) }, 200);
        assert_eq!(unsafe { read_state(state.as_ptr(), 2) }, 300);
        assert_eq!(unsafe { read_state(state.as_ptr(), 3) }, 400);
    }

    #[test]
    fn test_native_compile_tmir_module_return_42() {
        // End-to-end: tMIR Module -> LLVM IR -> native -> execute.
        // Uses the existing make_return_42_module() which goes through emit.rs.
        if !is_native_available() {
            return;
        }

        let module = make_return_42_module();
        let compiled = compile_module(&module).expect("should compile");

        let lib = compile_and_link(&compiled.llvm_ir, &compiled.name, OptLevel::O1)
            .expect("should compile and link tMIR module");

        type MainFn = unsafe extern "C" fn() -> i64;
        let main_fn: MainFn = unsafe {
            let ptr = lib.get_symbol("main").expect("should find main");
            std::mem::transmute(ptr)
        };

        let result = unsafe { main_fn() };
        assert_eq!(
            result, 42,
            "tMIR return-42 should produce 42 when executed natively"
        );
    }

    #[test]
    fn test_native_compile_opt_level_o3() {
        // Verify that O3 optimization produces a valid, callable binary.
        if !is_native_available() {
            return;
        }

        let ir = r#"; ModuleID = 'e2e_o3'
source_filename = "e2e_o3"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

define i64 @mul_add(i64 %0, i64 %1, i64 %2) {
entry:
  %3 = mul i64 %0, %1
  %4 = add i64 %3, %2
  ret i64 %4
}
"#;

        let lib = compile_and_link(ir, "e2e_o3", OptLevel::O3).expect("should compile at O3");

        type MulAddFn = unsafe extern "C" fn(i64, i64, i64) -> i64;
        let mul_add: MulAddFn = unsafe {
            let ptr = lib.get_symbol("mul_add").expect("should find mul_add");
            std::mem::transmute(ptr)
        };

        assert_eq!(unsafe { mul_add(3, 4, 5) }, 17, "3*4+5 = 17");
        assert_eq!(unsafe { mul_add(0, 100, 7) }, 7, "0*100+7 = 7");
    }

    #[test]
    fn test_native_compile_missing_llc_graceful_error() {
        // Verify that compile_and_link fails gracefully when llc is not found.
        // We fake this by trying to compile with a module name but intercepting
        // the result. This test just verifies the error path when llc IS available
        // by checking that invalid IR produces a useful error.
        if !is_native_available() {
            // When llc is genuinely not available, compile_and_link should error.
            let result = compile_and_link("invalid ir", "bad", OptLevel::O1);
            assert!(result.is_err());
            let err = result.unwrap_err();
            assert!(
                matches!(err, Llvm2Error::BackendUnavailable(_)),
                "Should return BackendUnavailable when llc missing, got: {err}"
            );
            return;
        }

        // When llc IS available but IR is invalid, should get CodeGen error.
        let result = compile_and_link("this is not valid LLVM IR", "bad_ir", OptLevel::O1);
        assert!(result.is_err(), "Invalid IR should fail compilation");
        let err = result.unwrap_err();
        assert!(
            matches!(err, Llvm2Error::CodeGen(_)),
            "Invalid IR should produce CodeGen error, got: {err}"
        );
    }

    #[test]
    fn test_native_compile_branching_function() {
        // End-to-end: function with conditional branch (if a > 0 then a else -a).
        if !is_native_available() {
            return;
        }

        let ir = r#"; ModuleID = 'e2e_branch'
source_filename = "e2e_branch"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

define i64 @abs_val(i64 %0) {
entry:
  %1 = icmp sgt i64 %0, 0
  br i1 %1, label %positive, label %negative

positive:
  ret i64 %0

negative:
  %2 = sub i64 0, %0
  ret i64 %2
}
"#;

        let lib = compile_and_link(ir, "e2e_branch", OptLevel::O1)
            .expect("should compile branching function");

        type AbsFn = unsafe extern "C" fn(i64) -> i64;
        let abs_val: AbsFn = unsafe {
            let ptr = lib.get_symbol("abs_val").expect("should find abs_val");
            std::mem::transmute(ptr)
        };

        assert_eq!(unsafe { abs_val(42) }, 42);
        assert_eq!(unsafe { abs_val(-42) }, 42);
        assert_eq!(unsafe { abs_val(0) }, 0);
    }

    // =========================================================================
    // Partial invariant compilation failure tests (Part of #4197)
    // =========================================================================

    /// Build a bytecode function that uses an unsupported opcode (PowInt),
    /// guaranteeing a compilation failure through the tMIR lowering path.
    fn make_uncompilable_invariant() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("Inv_uncompilable".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 2 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        // PowInt is not supported by the tMIR lowering pipeline.
        func.emit(Opcode::PowInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    #[test]
    fn test_bfs_step_partial_invariant_failure_preserves_index_alignment() {
        // Regression test for #4197: when invariant compilation fails mid-sequence,
        // the indices of successfully compiled invariants must still correspond
        // to their original positions in the input list.
        //
        // Setup: 3 invariants where index 1 fails. The result should be:
        //   invariants[0] = Some(...)  -- corresponds to original inv 0
        //   invariants[1] = None       -- original inv 1 failed
        //   invariants[2] = Some(...)  -- corresponds to original inv 2
        let next_func = make_x_incr_next_state();
        let inv0 = make_x_gt_zero_invariant(); // x > 0 -- compiles fine
        let inv1_bad = make_uncompilable_invariant(); // uses FuncExcept -- fails
        let mut inv2 = BytecodeFunction::new("Inv_x_lt_100".to_string(), 0);
        inv2.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv2.emit(Opcode::LoadImm { rd: 1, value: 100 });
        inv2.emit(Opcode::LtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inv2.emit(Opcode::Ret { rs: 2 });

        let bfs_step = compile_bfs_step("partial_fail", &next_func, &[&inv0, &inv1_bad, &inv2])
            .expect("BFS step should succeed even with partial invariant failure");

        // Verify the step itself compiled (next-state function is mandatory).
        assert_eq!(bfs_step.action_name, "partial_fail");
        assert!(!bfs_step.next_state.llvm_ir.is_empty());

        // Index alignment: 3 slots, one None in the middle.
        assert_eq!(bfs_step.invariants.len(), 3);
        assert_eq!(bfs_step.invariants_compiled, 2);
        assert_eq!(bfs_step.invariants_failed, 1);

        // Index 0: successfully compiled (x > 0).
        assert!(
            bfs_step.invariants[0].is_some(),
            "Invariant 0 should compile successfully"
        );
        assert!(
            bfs_step.invariants[0]
                .as_ref()
                .unwrap()
                .llvm_ir
                .contains("partial_fail_inv_0"),
            "Invariant 0 should have the correct name"
        );

        // Index 1: failed (unsupported opcode).
        assert!(
            bfs_step.invariants[1].is_none(),
            "Invariant 1 should be None (compilation failed)"
        );

        // Index 2: successfully compiled (x < 100).
        assert!(
            bfs_step.invariants[2].is_some(),
            "Invariant 2 should compile successfully"
        );
        assert!(
            bfs_step.invariants[2]
                .as_ref()
                .unwrap()
                .llvm_ir
                .contains("partial_fail_inv_2"),
            "Invariant 2 should have the correct name (index 2, not 1)"
        );
        assert!(
            bfs_step.invariants[2]
                .as_ref()
                .unwrap()
                .llvm_ir
                .contains("icmp slt"),
            "Invariant 2 should contain the less-than comparison"
        );
    }

    #[test]
    fn test_bfs_step_all_invariants_fail_still_succeeds() {
        // When ALL invariants fail, the BFS step should still succeed
        // (the next-state function compiled, invariants are optional for native).
        let next_func = make_x_incr_next_state();
        let bad1 = make_uncompilable_invariant();
        let bad2 = make_uncompilable_invariant();

        let bfs_step = compile_bfs_step("all_fail", &next_func, &[&bad1, &bad2])
            .expect("BFS step should succeed even with all invariants failing");

        assert_eq!(bfs_step.invariants.len(), 2);
        assert_eq!(bfs_step.invariants_compiled, 0);
        assert_eq!(bfs_step.invariants_failed, 2);
        assert!(bfs_step.invariants[0].is_none());
        assert!(bfs_step.invariants[1].is_none());
        // Next-state function is still compiled.
        assert!(!bfs_step.next_state.llvm_ir.is_empty());
    }

    #[test]
    fn test_bfs_step_first_invariant_fails_preserves_second() {
        // Verify that a failure at index 0 does not shift index 1.
        let next_func = make_x_incr_next_state();
        let bad = make_uncompilable_invariant();
        let good = make_x_gt_zero_invariant();

        let bfs_step = compile_bfs_step("first_fails", &next_func, &[&bad, &good])
            .expect("should compile with first invariant failing");

        assert_eq!(bfs_step.invariants.len(), 2);
        assert_eq!(bfs_step.invariants_compiled, 1);
        assert_eq!(bfs_step.invariants_failed, 1);
        assert!(bfs_step.invariants[0].is_none());
        assert!(bfs_step.invariants[1].is_some());
        // The second invariant should be named inv_1 (preserving original index).
        assert!(
            bfs_step.invariants[1]
                .as_ref()
                .unwrap()
                .llvm_ir
                .contains("first_fails_inv_1"),
            "Second invariant should preserve its original index in the name"
        );
    }

    // =========================================================================
    // Stream 3 integration tests (#4251): ArtifactCache + PrefetchPass wiring
    // =========================================================================

    /// Build a minimal tMIR module whose name hints at a BFS-frontier-drain
    /// loop. The prefetch pass uses textual inspection of `Module` Debug +
    /// `Module.name`, so naming the module `bfs_step_*` is sufficient to
    /// trigger detection without depending on tMIR's still-evolving
    /// function-surface API.
    fn make_bfs_flavoured_module() -> Module {
        let mut module = Module::new("fn bfs_step_flat_stream3(&[u64]) { }");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "bfs_step", ft, entry);
        let mut block = Block::new(entry);
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn test_prefetch_pass_annotates_compiled_module_name() {
        // Integration (b) from epic #4251 Stream 3: `compile_module` must
        // run the prefetch pass, which annotates the module name with
        // `[prefetch ...]` when a BFS-frontier-drain pattern is detected.
        // Real `@llvm.prefetch` emission is stubbed pending LLVM2#390 — see
        // `crates/tla-llvm2/src/prefetch.rs` module docs. This test asserts
        // the pass fires and the lowering pipeline observes its effect.
        let module = make_bfs_flavoured_module();
        let compiled = compile_module(&module).expect("should compile");
        assert!(
            compiled.name.contains("[prefetch "),
            "prefetch pass should have annotated module name with sites tag; got: {}",
            compiled.name
        );
        // Shape check: the annotation must encode distance + access hints
        // so future readers can inspect what the pass actually did without
        // re-running it. Defaults (distance=2, access=Read) are locked in
        // by `PrefetchConfig::default()`.
        assert!(
            compiled.name.contains("distance=2"),
            "annotation should record the default prefetch distance; got: {}",
            compiled.name
        );
        assert!(
            compiled.name.contains("access=Read"),
            "annotation should record the read access hint; got: {}",
            compiled.name
        );
    }

    #[test]
    fn test_prefetch_pass_no_op_when_module_unrelated_to_bfs() {
        // Negative companion to `test_prefetch_pass_annotates_compiled_module_name`:
        // a module with no BFS hint must not gain a prefetch annotation.
        // This confirms the pass is firing selectively rather than always.
        let module = make_return_42_module();
        let compiled = compile_module(&module).expect("should compile");
        assert!(
            !compiled.name.contains("[prefetch "),
            "prefetch pass should be a no-op on non-BFS modules; got: {}",
            compiled.name
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_artifact_cache_hit_skips_recompilation() {
        // Integration (a) from epic #4251 Stream 3: `compile_module_native`
        // must service the second call to an identical
        // `(module, opt_level, target_triple)` from the process-local JIT
        // cache. The on-disk sidecar is best-effort observability; the
        // functional guarantee is the in-process Arc hit.
        use std::sync::Arc as StdArc;

        // Redirect the on-disk observability sidecar to a tempdir so this
        // test does not touch the user's real `~/.cache/tla2/compiled`
        // state. Cache behaviour under test is layer 1 (in-process),
        // which is independent of the on-disk path.
        let tmp = tempfile::tempdir().expect("should create tempdir");
        // SAFETY: test-only, single-threaded w.r.t. its own env var.
        // Setting an env var races with other tests that read it, but no
        // test in this file reads TLA2_CACHE_DIR besides this one.
        unsafe {
            std::env::set_var("TLA2_CACHE_DIR", tmp.path());
        }

        // Start from a clean slate so we control the hit/miss transition.
        clear_jit_cache();

        let module = make_return_42_module();

        // First call: cache miss — must invoke the real compilation pipeline.
        let lib1 = compile_module_native(&module, OptLevel::O1)
            .expect("first native compile should succeed");

        // Second call with the same inputs: must be served from the
        // process-local cache. We verify this structurally by reaching
        // into the cache ourselves and confirming the stored Arc points
        // at the same ExecutableBuffer as the returned handle. Pointer
        // identity on the Arc is the strictest possible observation that
        // no recompilation occurred.
        let lib2 = compile_module_native(&module, OptLevel::O1)
            .expect("second native compile should be a cache hit");

        // Poke the internal cache to retrieve the stored Arc.
        let key = crate::artifact_cache::CacheKey::for_module(
            &module,
            OptLevel::O1.as_str(),
            target_triple_static(),
        );
        let cached =
            jit_cache_lookup(&key).expect("cache must contain an entry after the first compile");

        // Both handles must point at the same buffer as the cache entry.
        assert!(
            StdArc::ptr_eq(&cached, &lib1.buffer),
            "first handle's buffer must be the cached Arc"
        );
        assert!(
            StdArc::ptr_eq(&cached, &lib2.buffer),
            "second handle's buffer must be the same cached Arc — cache miss would \
             have produced a fresh Arc",
        );

        // Clear and re-run: the key must be gone and a recompile must
        // produce a *different* Arc. This guards against silent global
        // state leaks where a stale entry survives `clear_jit_cache`.
        clear_jit_cache();
        assert!(
            jit_cache_lookup(&key).is_none(),
            "clear_jit_cache must purge every entry"
        );
        let lib3 = compile_module_native(&module, OptLevel::O1)
            .expect("third native compile should succeed after cache clear");
        assert!(
            !StdArc::ptr_eq(&lib3.buffer, &cached),
            "after clearing the cache, a fresh compile must produce a distinct Arc"
        );

        // Cleanup: drop the env var so it doesn't leak to other tests.
        unsafe {
            std::env::remove_var("TLA2_CACHE_DIR");
        }
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_artifact_cache_disabled_env_forces_recompile() {
        // Complement to `test_artifact_cache_hit_skips_recompilation`:
        // `TLA2_DISABLE_ARTIFACT_CACHE=1` must suppress both cache layers
        // so two consecutive compiles always produce distinct Arc buffers.
        use std::sync::Arc as StdArc;

        let tmp = tempfile::tempdir().expect("should create tempdir");
        // SAFETY: see test_artifact_cache_hit_skips_recompilation.
        unsafe {
            std::env::set_var("TLA2_CACHE_DIR", tmp.path());
            std::env::set_var("TLA2_DISABLE_ARTIFACT_CACHE", "1");
        }

        clear_jit_cache();
        let module = make_return_42_module();

        let lib1 = compile_module_native(&module, OptLevel::O1)
            .expect("first compile should succeed with cache disabled");
        let lib2 = compile_module_native(&module, OptLevel::O1)
            .expect("second compile should succeed with cache disabled");

        assert!(
            !StdArc::ptr_eq(&lib1.buffer, &lib2.buffer),
            "TLA2_DISABLE_ARTIFACT_CACHE must force fresh Arcs each call"
        );

        // The in-process cache must remain empty too.
        let key = crate::artifact_cache::CacheKey::for_module(
            &module,
            OptLevel::O1.as_str(),
            target_triple_static(),
        );
        assert!(
            jit_cache_lookup(&key).is_none(),
            "disabled cache must not populate the in-process map"
        );

        unsafe {
            std::env::remove_var("TLA2_DISABLE_ARTIFACT_CACHE");
            std::env::remove_var("TLA2_CACHE_DIR");
        }
    }

    #[test]
    fn test_native_extern_symbol_overlay_validation() {
        let null_overlay = NativeExternSymbolOverlay::from_symbols([("missing", std::ptr::null())]);
        assert!(
            null_overlay.is_err(),
            "null overlay addresses must be rejected"
        );

        let duplicate_overlay = NativeExternSymbolOverlay::from_symbols([
            ("dup", overlay_add_one as *const u8),
            ("dup", overlay_add_two as *const u8),
        ]);
        assert!(
            duplicate_overlay.is_err(),
            "duplicate overlay symbols must be rejected"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_bodyless_external_declaration_is_not_registered_as_local_symbol() {
        let mut module = Module::new("bodyless_extern_shadow");
        let extern_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let main_ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

        let extern_id = FuncId::new(10_000);
        let mut extern_decl = Function::new(extern_id, "__func_10000", extern_ty, BlockId::new(0));
        extern_decl.linkage = tmir::Linkage::External;
        module.add_function(extern_decl);

        let mut main = Function::new(FuncId::new(0), "main", main_ty, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(41),
            })
            .with_result(ValueId::new(0)),
        );
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: extern_id,
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        main.blocks.push(entry);
        module.add_function(main);

        assert_eq!(
            bodyless_external_declaration_names(&module),
            HashSet::from(["__func_10000".to_string()])
        );

        let overlay = NativeExternSymbolOverlay::from_symbols([(
            "__func_10000",
            overlay_add_one as *const u8,
        )])
        .expect("extern overlay");
        let library = compile_module_native_with_extern_symbols(&module, OptLevel::O1, &overlay)
            .expect("bodyless extern declaration should compile through overlay");
        unsafe { library.get_symbol("main") }.expect("main symbol");
        assert!(
            unsafe { library.get_symbol("__func_10000") }.is_err(),
            "bodyless external declaration must not be registered as a local JIT symbol"
        );
    }

    #[cfg(feature = "native")]
    #[test]
    fn test_native_extern_symbol_overlay_merges_and_partitions_cache() {
        use std::sync::Arc as StdArc;

        let tmp = tempfile::tempdir().expect("should create tempdir");
        unsafe {
            std::env::set_var("TLA2_CACHE_DIR", tmp.path());
            std::env::remove_var("TLA2_DISABLE_ARTIFACT_CACHE");
        }
        clear_jit_cache();

        let module = make_return_42_module();
        let overlay_one = NativeExternSymbolOverlay::from_symbols([(
            "overlay_hook",
            overlay_add_one as *const u8,
        )])
        .expect("overlay one");
        let overlay_two = NativeExternSymbolOverlay::from_symbols([(
            "overlay_hook",
            overlay_add_two as *const u8,
        )])
        .expect("overlay two");

        let mut extern_symbols = build_extern_symbol_map();
        overlay_one.overlay_into(&mut extern_symbols);
        assert_eq!(
            extern_symbols.get("overlay_hook").copied(),
            Some(overlay_add_one as *const u8),
            "overlay symbol must be merged into the native JIT extern map"
        );

        let default_key =
            CacheKey::for_module(&module, OptLevel::O1.as_str(), target_triple_static());
        let overlay_one_key = native_cache_key(&module, OptLevel::O1, &overlay_one);
        let overlay_two_key = native_cache_key(&module, OptLevel::O1, &overlay_two);
        assert_ne!(default_key.digest_hex, overlay_one_key.digest_hex);
        assert_ne!(overlay_one_key.digest_hex, overlay_two_key.digest_hex);

        let lib1 = compile_module_native_with_extern_symbols(&module, OptLevel::O1, &overlay_one)
            .expect("compile with first extern overlay");
        type MainFn = unsafe extern "C" fn() -> i64;
        let main1: MainFn =
            unsafe { std::mem::transmute(lib1.get_symbol("main").expect("main symbol")) };
        assert_eq!(unsafe { main1() }, 42);

        let lib2 = compile_module_native_with_extern_symbols(&module, OptLevel::O1, &overlay_two)
            .expect("compile with second extern overlay");
        let main2: MainFn =
            unsafe { std::mem::transmute(lib2.get_symbol("main").expect("main symbol")) };
        assert_eq!(unsafe { main2() }, 42);
        assert!(
            !StdArc::ptr_eq(&lib1.buffer, &lib2.buffer),
            "different overlay pointer identities must not share a cached buffer"
        );

        let lib3 = compile_module_native_with_extern_symbols(&module, OptLevel::O1, &overlay_one)
            .expect("compile with first overlay again");
        assert!(
            StdArc::ptr_eq(&lib1.buffer, &lib3.buffer),
            "same overlay identity should hit the process-local JIT cache"
        );

        unsafe {
            std::env::remove_var("TLA2_CACHE_DIR");
        }
    }

    // ========================================================================
    // Extern symbol map (Fixes #4314)
    // ========================================================================

    /// Every runtime helper declared in `RUNTIME_HELPERS` must resolve to a
    /// non-null in-process function pointer via `build_extern_symbol_map`.
    ///
    /// On Mach-O (macOS / iOS) the map also contains the underscored siblings
    /// (`_jit_*`) that the native ABI emits for globally visible symbols.
    #[cfg(feature = "native")]
    #[test]
    fn test_build_extern_symbol_map_all_helpers_resolved() {
        let symbols = build_extern_symbol_map();

        // Lower bound: the initial #4314 `jit_*` surface shipped 14
        // helpers. The `tla_*` Option B surface (#4318) brought the total
        // well above that. We assert the lower bound instead of an exact
        // count so adding new helpers does not require touching this test,
        // but a regression that drops below the baseline still trips.
        assert!(
            crate::runtime::RUNTIME_HELPERS.len() >= 14,
            "RUNTIME_HELPERS dropped below the #4314 baseline ({} < 14)",
            crate::runtime::RUNTIME_HELPERS.len(),
        );

        for helper in crate::runtime::RUNTIME_HELPERS {
            let addr = symbols.get(helper.symbol).unwrap_or_else(|| {
                panic!(
                    "runtime helper '{}' not in extern symbol map",
                    helper.symbol,
                )
            });
            assert!(
                !addr.is_null(),
                "runtime helper '{}' resolved to a null pointer",
                helper.symbol,
            );

            // Mach-O sibling: the linker may emit either `jit_pow_i64` or
            // `_jit_pow_i64` depending on relocation style; both must resolve.
            #[cfg(any(target_os = "macos", target_os = "ios"))]
            {
                let macho_name = format!("_{}", helper.symbol);
                let macho_addr = symbols.get(&macho_name).unwrap_or_else(|| {
                    panic!("runtime helper Mach-O alias '{macho_name}' not in extern symbol map",)
                });
                assert_eq!(
                    *macho_addr, *addr,
                    "Mach-O alias '{macho_name}' must point to the same helper",
                );
            }
        }

        for helper in ["tla2_compiled_fp_u64", "resizable_fp_set_probe"] {
            let addr = symbols
                .get(helper)
                .unwrap_or_else(|| panic!("native BFS helper '{helper}' not in extern symbol map"));
            assert!(
                !addr.is_null(),
                "native BFS helper '{helper}' resolved to a null pointer",
            );

            #[cfg(any(target_os = "macos", target_os = "ios"))]
            {
                let macho_name = format!("_{helper}");
                let macho_addr = symbols.get(&macho_name).unwrap_or_else(|| {
                    panic!("native BFS helper Mach-O alias '{macho_name}' not in extern symbol map")
                });
                assert_eq!(
                    *macho_addr, *addr,
                    "Mach-O alias '{macho_name}' must point to the same helper",
                );
            }
        }

        let expected_helper_count = crate::runtime::RUNTIME_HELPERS.len() + 2;
        // Expected entry count: N helpers on Linux, 2N on Mach-O.
        #[cfg(any(target_os = "macos", target_os = "ios"))]
        assert_eq!(
            symbols.len(),
            expected_helper_count * 2,
            "Mach-O map should contain each helper twice (bare + `_`-prefixed)",
        );
        #[cfg(not(any(target_os = "macos", target_os = "ios")))]
        assert_eq!(
            symbols.len(),
            expected_helper_count,
            "non-Mach-O map should contain each helper exactly once",
        );
    }

    /// Smoke test: actually invoke one of the resolved helpers through the
    /// `build_extern_symbol_map` pointer and verify it produces the expected
    /// result. A correct pointer must be not just non-null but executable
    /// with the declared `extern "C"` signature.
    #[cfg(feature = "native")]
    #[test]
    fn test_extern_symbol_map_smoke_call() {
        let symbols = build_extern_symbol_map();
        let raw = *symbols
            .get("jit_pow_i64")
            .expect("jit_pow_i64 must be in the extern symbol map");

        // Cast back to the helper's `extern "C"` signature and invoke.
        // `jit_pow_i64(base=2, exp=10)` must return `1024` (per the
        // runtime_abi implementation — see TLA+ semantics there).
        let pow_fn: extern "C" fn(i64, i64) -> i64 =
            unsafe { std::mem::transmute::<*const u8, _>(raw) };
        assert_eq!(pow_fn(2, 10), 1024);
        assert_eq!(pow_fn(3, 4), 81);
        assert_eq!(pow_fn(0, 0), 1, "TLA+ convention: 0^0 = 1");
        assert_eq!(pow_fn(5, -1), 0, "TLA+ convention: negative exp = 0");
    }
}
