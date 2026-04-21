// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LLVM AOT compiler: orchestrates IR emission, optimization, and native
//! code compilation.

use crate::error::LlvmError;
use crate::ir::LlvmModule;
use crate::lower;
use std::path::{Path, PathBuf};
use std::process::Command;
use tla_jit::abi::{JitInvariantFn, JitNextStateFn};
use tla_tir::bytecode::BytecodeFunction;

/// Optimization level for LLVM compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptLevel {
    /// No optimization (useful for debugging IR).
    O0,
    /// Basic optimizations.
    O1,
    /// Full optimizations (default for AOT model checking).
    O2,
    /// Aggressive optimizations including vectorization.
    O3,
}

impl OptLevel {
    fn as_flag(&self) -> &'static str {
        match self {
            Self::O0 => "-O0",
            Self::O1 => "-O1",
            Self::O2 => "-O2",
            Self::O3 => "-O3",
        }
    }
}

/// LLVM AOT compiler.
///
/// Translates `BytecodeFunction`s to LLVM IR text and optionally compiles
/// them to native shared libraries via external LLVM tools.
pub struct LlvmCompiler {
    /// Target triple (e.g., "aarch64-apple-darwin").
    target_triple: String,
    /// Optimization level for native compilation.
    opt_level: OptLevel,
    /// Counter for generating unique function names.
    func_counter: u32,
    /// Accumulated LLVM module with all compiled functions.
    module: LlvmModule,
}

impl LlvmCompiler {
    /// Create a new LLVM compiler targeting the host platform.
    #[must_use]
    pub fn new() -> Self {
        let target_triple = detect_target_triple();
        let module = LlvmModule::new(&target_triple);
        Self {
            target_triple,
            opt_level: OptLevel::O2,
            func_counter: 0,
            module,
        }
    }

    /// Create a compiler with a specific optimization level.
    #[must_use]
    pub fn with_opt_level(mut self, level: OptLevel) -> Self {
        self.opt_level = level;
        self
    }

    /// Emit LLVM IR for a bytecode invariant function.
    ///
    /// Returns the function name in the module. Does not compile to native
    /// code -- call [`Self::compile_to_file`] or [`Self::to_ir`] to get output.
    pub fn add_invariant(
        &mut self,
        func: &BytecodeFunction,
    ) -> Result<String, LlvmError> {
        let func_name = format!("llvm_inv_{}", self.func_counter);
        self.func_counter += 1;

        lower::lower_invariant_into(func, &func_name, &mut self.module)?;
        Ok(func_name)
    }

    /// Emit LLVM IR for a bytecode next-state function.
    ///
    /// Returns the function name in the module.
    pub fn add_next_state(
        &mut self,
        func: &BytecodeFunction,
    ) -> Result<String, LlvmError> {
        let func_name = format!("llvm_nxt_{}", self.func_counter);
        self.func_counter += 1;

        lower::lower_next_state_into(func, &func_name, &mut self.module)?;
        Ok(func_name)
    }

    /// Get the accumulated LLVM IR text for all added functions.
    #[must_use]
    pub fn to_ir(&self) -> String {
        self.module.to_ir()
    }

    /// Write LLVM IR to a `.ll` file.
    pub fn write_ir(&self, path: &Path) -> Result<(), LlvmError> {
        let ir = self.to_ir();
        std::fs::write(path, ir)?;
        Ok(())
    }

    /// Compile the accumulated LLVM IR to a native object file.
    ///
    /// Requires `clang` to be available on `PATH`.
    /// Returns the path to the compiled object file.
    pub fn compile_to_object(&self, output_dir: &Path) -> Result<PathBuf, LlvmError> {
        let ll_path = output_dir.join("tla_aot.ll");
        let obj_path = output_dir.join("tla_aot.o");

        self.write_ir(&ll_path)?;

        // Use clang to compile .ll -> .o with optimizations
        let output = Command::new("clang")
            .arg(self.opt_level.as_flag())
            .arg("-c")
            .arg("-fPIC")
            .arg(&ll_path)
            .arg("-o")
            .arg(&obj_path)
            .output()
            .map_err(|e| LlvmError::CompileError(format!("failed to run clang: {e}")))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LlvmError::CompileError(format!(
                "clang exited with status {}: {stderr}",
                output.status
            )));
        }

        Ok(obj_path)
    }

    /// Compile and link to a shared library (.dylib / .so).
    ///
    /// Requires `clang` to be available on `PATH`.
    /// Returns the path to the compiled shared library.
    pub fn compile_to_dylib(&self, output_dir: &Path) -> Result<PathBuf, LlvmError> {
        let ll_path = output_dir.join("tla_aot.ll");
        let dylib_ext = if cfg!(target_os = "macos") {
            "dylib"
        } else {
            "so"
        };
        let dylib_path = output_dir.join(format!("tla_aot.{dylib_ext}"));

        self.write_ir(&ll_path)?;

        let output = Command::new("clang")
            .arg(self.opt_level.as_flag())
            .arg("-shared")
            .arg("-fPIC")
            .arg(&ll_path)
            .arg("-o")
            .arg(&dylib_path)
            .output()
            .map_err(|e| LlvmError::CompileError(format!("failed to run clang: {e}")))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LlvmError::CompileError(format!(
                "clang exited with status {}: {stderr}",
                output.status
            )));
        }

        Ok(dylib_path)
    }

    /// Compile to a shared library and load an invariant function pointer.
    ///
    /// # Safety
    ///
    /// The returned function pointers are valid only as long as the library
    /// handle is kept alive. The caller must ensure the library is not
    /// unloaded while function pointers are in use.
    pub unsafe fn compile_and_load_invariant(
        &self,
        _func: &BytecodeFunction,
        func_name: &str,
        output_dir: &Path,
    ) -> Result<(JitInvariantFn, *mut std::ffi::c_void), LlvmError> {
        let dylib_path = self.compile_to_dylib(output_dir)?;
        load_invariant_from_dylib(&dylib_path, func_name)
    }

    /// Compile to a shared library and load a next-state function pointer.
    ///
    /// # Safety
    ///
    /// The returned function pointers are valid only as long as the library
    /// handle is kept alive. The caller must ensure the library is not
    /// unloaded while function pointers are in use.
    pub unsafe fn compile_and_load_next_state(
        &self,
        _func: &BytecodeFunction,
        func_name: &str,
        output_dir: &Path,
    ) -> Result<(JitNextStateFn, *mut std::ffi::c_void), LlvmError> {
        let dylib_path = self.compile_to_dylib(output_dir)?;
        load_next_state_from_dylib(&dylib_path, func_name)
    }

    /// Check if LLVM tools (clang) are available for native compilation.
    #[must_use]
    pub fn has_llvm_tools() -> bool {
        Command::new("clang")
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    }

    /// Get the target triple being used.
    #[must_use]
    pub fn target_triple(&self) -> &str {
        &self.target_triple
    }
}

impl Default for LlvmCompiler {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Library loading via dlopen
// =========================================================================

/// Load an invariant function from a compiled shared library.
///
/// # Safety
///
/// The returned function pointer is only valid while the library handle is
/// alive. The caller must keep the handle and not dlclose it.
pub(crate) unsafe fn load_invariant_from_dylib(
    dylib_path: &Path,
    func_name: &str,
) -> Result<(JitInvariantFn, *mut std::ffi::c_void), LlvmError> {
    let (sym, handle) = load_symbol_from_dylib(dylib_path, func_name)?;
    // SAFETY: The transmute is sound because:
    // 1. The LLVM IR was generated with the JitInvariantFn signature
    // 2. clang compiled with the C ABI (default)
    // 3. JitInvariantFn is extern "C" fn(*mut JitCallOut, *const i64, u32)
    let fn_ptr: JitInvariantFn = std::mem::transmute(sym);
    Ok((fn_ptr, handle))
}

/// Load a next-state function from a compiled shared library.
///
/// # Safety
///
/// The returned function pointer is only valid while the library handle is
/// alive. The caller must keep the handle and not dlclose it.
pub(crate) unsafe fn load_next_state_from_dylib(
    dylib_path: &Path,
    func_name: &str,
) -> Result<(JitNextStateFn, *mut std::ffi::c_void), LlvmError> {
    let (sym, handle) = load_symbol_from_dylib(dylib_path, func_name)?;
    // SAFETY: The transmute is sound because:
    // 1. The LLVM IR was generated with the JitNextStateFn signature
    // 2. clang compiled with the C ABI (default)
    // 3. JitNextStateFn is extern "C" fn(*mut JitCallOut, *const i64, *mut i64, u32)
    let fn_ptr: JitNextStateFn = std::mem::transmute(sym);
    Ok((fn_ptr, handle))
}

/// Load a raw symbol address from a shared library via dlopen/dlsym.
///
/// # Safety
///
/// The returned symbol pointer and library handle must be kept consistent.
/// The symbol pointer is invalid after dlclose.
unsafe fn load_symbol_from_dylib(
    dylib_path: &Path,
    func_name: &str,
) -> Result<(*mut std::ffi::c_void, *mut std::ffi::c_void), LlvmError> {
    use std::ffi::CString;

    let path_str = dylib_path
        .to_str()
        .ok_or_else(|| LlvmError::LoadError("non-UTF8 path".to_string()))?;
    let c_path = CString::new(path_str)
        .map_err(|e| LlvmError::LoadError(format!("path contains null byte: {e}")))?;

    // SAFETY: dlopen with RTLD_NOW loads the library and resolves all symbols.
    let handle = libc::dlopen(c_path.as_ptr(), libc::RTLD_NOW);
    if handle.is_null() {
        let err = std::ffi::CStr::from_ptr(libc::dlerror());
        return Err(LlvmError::LoadError(format!(
            "dlopen failed: {}",
            err.to_string_lossy()
        )));
    }

    let c_name = CString::new(func_name)
        .map_err(|e| LlvmError::LoadError(format!("func name contains null byte: {e}")))?;
    let sym = libc::dlsym(handle, c_name.as_ptr());
    if sym.is_null() {
        let err = std::ffi::CStr::from_ptr(libc::dlerror());
        return Err(LlvmError::LoadError(format!(
            "dlsym failed for {func_name}: {}",
            err.to_string_lossy()
        )));
    }

    Ok((sym, handle))
}

/// RAII wrapper for a loaded AOT shared library.
///
/// Holds the dlopen handle and ensures the library stays loaded as long
/// as function pointers derived from it are in use. Drop calls dlclose.
pub struct AotLibrary {
    handle: *mut std::ffi::c_void,
}

impl AotLibrary {
    /// Load a shared library from a path.
    ///
    /// # Safety
    ///
    /// The library must be a valid shared object compiled from LLVM IR
    /// generated by this crate.
    pub unsafe fn load(path: &Path) -> Result<Self, LlvmError> {
        use std::ffi::CString;

        let path_str = path
            .to_str()
            .ok_or_else(|| LlvmError::LoadError("non-UTF8 path".to_string()))?;
        let c_path = CString::new(path_str)
            .map_err(|e| LlvmError::LoadError(format!("path contains null byte: {e}")))?;

        // SAFETY: dlopen with RTLD_NOW loads the library and resolves all symbols.
        let handle = libc::dlopen(c_path.as_ptr(), libc::RTLD_NOW);
        if handle.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror());
            return Err(LlvmError::LoadError(format!(
                "dlopen failed: {}",
                err.to_string_lossy()
            )));
        }

        Ok(Self { handle })
    }

    /// Look up an invariant function by name.
    ///
    /// # Safety
    ///
    /// The returned function pointer is valid only while this `AotLibrary` is alive.
    pub unsafe fn get_invariant_fn(&self, name: &str) -> Result<JitInvariantFn, LlvmError> {
        let sym = self.get_symbol(name)?;
        // SAFETY: The symbol was compiled from LLVM IR with the JitInvariantFn signature.
        Ok(std::mem::transmute(sym))
    }

    /// Look up a next-state function by name.
    ///
    /// # Safety
    ///
    /// The returned function pointer is valid only while this `AotLibrary` is alive.
    pub unsafe fn get_next_state_fn(&self, name: &str) -> Result<JitNextStateFn, LlvmError> {
        let sym = self.get_symbol(name)?;
        // SAFETY: The symbol was compiled from LLVM IR with the JitNextStateFn signature.
        Ok(std::mem::transmute(sym))
    }

    unsafe fn get_symbol(&self, name: &str) -> Result<*mut std::ffi::c_void, LlvmError> {
        use std::ffi::CString;

        let c_name = CString::new(name)
            .map_err(|e| LlvmError::LoadError(format!("func name contains null byte: {e}")))?;
        // SAFETY: handle is valid (checked in load), name is a valid C string.
        let sym = libc::dlsym(self.handle, c_name.as_ptr());
        if sym.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror());
            return Err(LlvmError::LoadError(format!(
                "dlsym failed for {name}: {}",
                err.to_string_lossy()
            )));
        }
        Ok(sym)
    }
}

impl Drop for AotLibrary {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            // SAFETY: handle was obtained from dlopen and is still valid.
            unsafe {
                libc::dlclose(self.handle);
            }
        }
    }
}

// SAFETY: The library handle is process-wide and function pointers can be
// called from any thread.
unsafe impl Send for AotLibrary {}
unsafe impl Sync for AotLibrary {}

/// Detect the host target triple.
fn detect_target_triple() -> String {
    // Use Rust's built-in target triple
    if cfg!(target_os = "macos") {
        if cfg!(target_arch = "aarch64") {
            "aarch64-apple-darwin".to_string()
        } else {
            "x86_64-apple-darwin".to_string()
        }
    } else if cfg!(target_os = "linux") {
        if cfg!(target_arch = "aarch64") {
            "aarch64-unknown-linux-gnu".to_string()
        } else {
            "x86_64-unknown-linux-gnu".to_string()
        }
    } else {
        // Fallback
        "x86_64-unknown-linux-gnu".to_string()
    }
}
