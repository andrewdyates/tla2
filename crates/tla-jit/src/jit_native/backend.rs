// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Vendored from cranelift-jit 0.112.3, src/backend.rs
// Original: Copyright (c) Bytecode Alliance. Apache-2.0 WITH LLVM-exception.
// Modified: Removed hotswap, PLT/GOT, data objects, Windows, perf map, SELinux.
// Kept: function declaration/definition/finalization, symbol resolution, memory management.

use crate::jit_native::memory::Memory;
use crate::jit_native::reloc::CompiledBlob;
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::entity::SecondaryMap;
use cranelift_codegen::isa::{OwnedTargetIsa, TargetIsa};
use cranelift_codegen::{ir, FinalizedMachReloc};

use super::{
    DataDescription, DataId, FuncId, FuncOrDataId, Linkage, Module, ModuleDeclarations,
    ModuleError, ModuleReloc, ModuleRelocTarget, ModuleResult,
};

use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::CString;
use std::ptr;

/// A builder for `JITModule`.
pub struct JITBuilder {
    isa: OwnedTargetIsa,
    symbols: HashMap<String, SendWrapper<*const u8>>,
    lookup_symbols: Vec<Box<dyn Fn(&str) -> Option<*const u8> + Send>>,
    libcall_names: Box<dyn Fn(ir::LibCall) -> String + Send + Sync>,
}

impl JITBuilder {
    /// Create a new `JITBuilder` with an ISA and libcall name resolver.
    pub fn with_isa(
        isa: OwnedTargetIsa,
        libcall_names: Box<dyn Fn(ir::LibCall) -> String + Send + Sync>,
    ) -> Self {
        let symbols = HashMap::new();
        let lookup_symbols = vec![Box::new(lookup_with_dlsym) as Box<_>];
        Self {
            isa,
            symbols,
            lookup_symbols,
            libcall_names,
        }
    }

    /// Define a symbol in the internal symbol table.
    ///
    /// These are resolved when JIT-compiled code references external functions.
    /// If a symbol is defined more than once, the most recent definition wins.
    pub fn symbol<K>(&mut self, name: K, ptr: *const u8) -> &mut Self
    where
        K: Into<String>,
    {
        self.symbols.insert(name.into(), SendWrapper(ptr));
        self
    }

    /// Add a custom symbol lookup function.
    ///
    /// Lookup functions are tried in reverse order (last added = first tried).
    pub fn symbol_lookup_fn(
        &mut self,
        symbol_lookup_fn: Box<dyn Fn(&str) -> Option<*const u8> + Send>,
    ) -> &mut Self {
        self.lookup_symbols.push(symbol_lookup_fn);
        self
    }
}

/// Wrapper that impls Send for raw pointers.
///
/// SAFETY: Only used for function pointers which are safe to share across threads.
#[derive(Copy, Clone)]
struct SendWrapper<T>(T);
unsafe impl<T> Send for SendWrapper<T> {}

/// JIT module: compiles functions to executable memory.
///
/// This is a stripped version of `cranelift_jit::JITModule` optimized for
/// the tla-jit use case: no hotswap, no PLT/GOT, no data objects, Unix-only.
pub struct JITModule {
    isa: OwnedTargetIsa,
    symbols: RefCell<HashMap<String, SendWrapper<*const u8>>>,
    lookup_symbols: Vec<Box<dyn Fn(&str) -> Option<*const u8> + Send>>,
    libcall_names: Box<dyn Fn(ir::LibCall) -> String + Send + Sync>,
    memory: MemoryHandle,
    declarations: ModuleDeclarations,
    compiled_functions: SecondaryMap<FuncId, Option<CompiledBlob>>,
    functions_to_finalize: Vec<FuncId>,
}

impl std::fmt::Debug for JITModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("JITModule")
            .field("num_symbols", &self.symbols.borrow().len())
            .field("num_compiled", &self.compiled_functions.iter().filter(|(_, v)| v.is_some()).count())
            .field("pending_finalize", &self.functions_to_finalize.len())
            .finish()
    }
}

struct MemoryHandle {
    code: Memory,
    readonly: Memory,
}

impl JITModule {
    /// Free memory allocated for compiled functions.
    ///
    /// # Safety
    ///
    /// Invalidates all function pointers. Only call when no JIT-compiled
    /// functions are executing or will be called again.
    pub unsafe fn free_memory(mut self) {
        self.memory.code.free_memory();
        self.memory.readonly.free_memory();
    }

    fn lookup_symbol(&self, name: &str) -> Option<*const u8> {
        match self.symbols.borrow_mut().entry(name.to_owned()) {
            std::collections::hash_map::Entry::Occupied(occ) => Some(occ.get().0),
            std::collections::hash_map::Entry::Vacant(vac) => {
                let ptr = self
                    .lookup_symbols
                    .iter()
                    .rev()
                    .find_map(|lookup| lookup(name));
                if let Some(ptr) = ptr {
                    vac.insert(SendWrapper(ptr));
                }
                ptr
            }
        }
    }

    fn get_address(&self, name: &ModuleRelocTarget) -> *const u8 {
        match *name {
            ModuleRelocTarget::User { .. } => {
                let func_id = FuncId::from_name(name);
                match &self.compiled_functions[func_id] {
                    Some(compiled) => compiled.ptr,
                    None => {
                        let decl = self.declarations.get_function_decl(func_id);
                        let name = decl
                            .name
                            .as_ref()
                            .expect("anonymous symbol must be defined locally");
                        if let Some(ptr) = self.lookup_symbol(name) {
                            ptr
                        } else if decl.linkage == Linkage::Preemptible {
                            ptr::null()
                        } else {
                            panic!("can't resolve symbol {name}");
                        }
                    }
                }
            }
            ModuleRelocTarget::LibCall(ref libcall) => {
                let sym = (self.libcall_names)(*libcall);
                self.lookup_symbol(&sym)
                    .unwrap_or_else(|| panic!("can't resolve libcall {sym}"))
            }
            _ => panic!("invalid relocation target"),
        }
    }

    /// Returns the address of a finalized function.
    ///
    /// The pointer remains valid until `free_memory()` is called.
    pub fn get_finalized_function(&self, func_id: FuncId) -> *const u8 {
        let info = &self.compiled_functions[func_id];
        assert!(
            !self.functions_to_finalize.iter().any(|x| *x == func_id),
            "function not yet finalized"
        );
        info.as_ref()
            .expect("function must be compiled before it can be finalized")
            .ptr
    }

    /// Finalize all pending function definitions.
    ///
    /// Applies relocations and marks code memory as executable.
    pub fn finalize_definitions(&mut self) -> ModuleResult<()> {
        for func in std::mem::take(&mut self.functions_to_finalize) {
            let decl = self.declarations.get_function_decl(func);
            assert!(decl.linkage.is_definable());
            let func = self.compiled_functions[func]
                .as_ref()
                .expect("function must be compiled before finalization");
            func.perform_relocations(
                |name| self.get_address(name),
                |name| self.get_address(name), // No separate GOT in non-PIC mode
                |name| self.get_address(name), // No separate PLT in non-PIC mode
            );
        }

        self.memory.readonly.set_readonly()?;
        self.memory.code.set_readable_and_executable()?;

        Ok(())
    }

    /// Create a new `JITModule`.
    pub fn new(builder: JITBuilder) -> Self {
        Self {
            isa: builder.isa,
            symbols: RefCell::new(builder.symbols),
            lookup_symbols: builder.lookup_symbols,
            libcall_names: builder.libcall_names,
            memory: MemoryHandle {
                code: Memory::new(),
                readonly: Memory::new(),
            },
            declarations: ModuleDeclarations::default(),
            compiled_functions: SecondaryMap::new(),
            functions_to_finalize: Vec::new(),
        }
    }
}

impl Module for JITModule {
    fn isa(&self) -> &dyn TargetIsa {
        &*self.isa
    }

    fn declarations(&self) -> &ModuleDeclarations {
        &self.declarations
    }

    fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &ir::Signature,
    ) -> ModuleResult<FuncId> {
        let (id, _linkage) = self
            .declarations
            .declare_function(name, linkage, signature)?;
        Ok(id)
    }

    fn declare_anonymous_function(&mut self, signature: &ir::Signature) -> ModuleResult<FuncId> {
        self.declarations.declare_anonymous_function(signature)
    }

    fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> ModuleResult<DataId> {
        let (id, _) = self
            .declarations
            .declare_data(name, linkage, writable, tls)?;
        Ok(id)
    }

    fn declare_anonymous_data(&mut self, writable: bool, tls: bool) -> ModuleResult<DataId> {
        self.declarations.declare_anonymous_data(writable, tls)
    }

    fn define_function_with_control_plane(
        &mut self,
        id: FuncId,
        ctx: &mut cranelift_codegen::Context,
        ctrl_plane: &mut ControlPlane,
    ) -> ModuleResult<()> {
        let decl = self.declarations.get_function_decl(id);
        if !decl.linkage.is_definable() {
            return Err(ModuleError::InvalidImportDefinition(
                decl.linkage_name(id).into_owned(),
            ));
        }

        if self.compiled_functions[id].is_some() {
            return Err(ModuleError::DuplicateDefinition(
                decl.linkage_name(id).into_owned(),
            ));
        }

        let res = ctx.compile(self.isa(), ctrl_plane)?;
        let alignment = res.buffer.alignment as u64;
        let compiled_code = ctx.compiled_code().unwrap();

        let size = compiled_code.code_info().total_size as usize;
        let align = alignment
            .max(self.isa.function_alignment().minimum as u64)
            .max(self.isa.symbol_alignment());
        let ptr = self
            .memory
            .code
            .allocate(size, align)
            .map_err(|e| ModuleError::Allocation {
                message: "unable to alloc function",
                err: e,
            })?;

        {
            let mem = unsafe { std::slice::from_raw_parts_mut(ptr, size) };
            mem.copy_from_slice(compiled_code.code_buffer());
        }

        let relocs = compiled_code
            .buffer
            .relocs()
            .iter()
            .map(|reloc| ModuleReloc::from_mach_reloc(reloc, &ctx.func, id))
            .collect();

        self.compiled_functions[id] = Some(CompiledBlob { ptr, size, relocs });
        self.functions_to_finalize.push(id);

        Ok(())
    }

    fn define_function_bytes(
        &mut self,
        id: FuncId,
        func: &ir::Function,
        alignment: u64,
        bytes: &[u8],
        relocs: &[FinalizedMachReloc],
    ) -> ModuleResult<()> {
        let decl = self.declarations.get_function_decl(id);
        if !decl.linkage.is_definable() {
            return Err(ModuleError::InvalidImportDefinition(
                decl.linkage_name(id).into_owned(),
            ));
        }

        if self.compiled_functions[id].is_some() {
            return Err(ModuleError::DuplicateDefinition(
                decl.linkage_name(id).into_owned(),
            ));
        }

        let size = bytes.len();
        let align = alignment
            .max(self.isa.function_alignment().minimum as u64)
            .max(self.isa.symbol_alignment());
        let ptr = self
            .memory
            .code
            .allocate(size, align)
            .map_err(|e| ModuleError::Allocation {
                message: "unable to alloc function bytes",
                err: e,
            })?;

        unsafe {
            ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, size);
        }

        self.compiled_functions[id] = Some(CompiledBlob {
            ptr,
            size,
            relocs: relocs
                .iter()
                .map(|reloc| ModuleReloc::from_mach_reloc(reloc, func, id))
                .collect(),
        });
        self.functions_to_finalize.push(id);

        Ok(())
    }

    fn define_data(&mut self, _data_id: DataId, _data: &DataDescription) -> ModuleResult<()> {
        // Data objects are not used by tla-jit.
        unimplemented!("define_data not supported in stripped JIT backend")
    }

    fn get_name(&self, name: &str) -> Option<FuncOrDataId> {
        self.declarations.get_name(name)
    }

    fn target_config(&self) -> cranelift_codegen::isa::TargetFrontendConfig {
        self.isa().frontend_config()
    }

    fn make_context(&self) -> cranelift_codegen::Context {
        let mut ctx = cranelift_codegen::Context::new();
        ctx.func.signature.call_conv = self.isa().default_call_conv();
        ctx
    }

    fn clear_context(&self, ctx: &mut cranelift_codegen::Context) {
        ctx.clear();
        ctx.func.signature.call_conv = self.isa().default_call_conv();
    }

    fn make_signature(&self) -> ir::Signature {
        ir::Signature::new(self.isa().default_call_conv())
    }

    fn clear_signature(&self, sig: &mut ir::Signature) {
        sig.clear(self.isa().default_call_conv());
    }
}

/// Resolve a symbol via dlsym on Unix.
fn lookup_with_dlsym(name: &str) -> Option<*const u8> {
    let c_str = CString::new(name).unwrap();
    let sym = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_str.as_ptr()) };
    if sym.is_null() {
        None
    } else {
        Some(sym as *const u8)
    }
}
