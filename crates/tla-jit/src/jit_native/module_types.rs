// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Vendored from cranelift-module 0.112.3, src/module.rs
// Original: Copyright (c) Bytecode Alliance. Apache-2.0 WITH LLVM-exception.
// Modified: Removed serde support, removed `no_std` conditional compilation,
// removed `hashbrown` conditional, simplified error types.

use std::borrow::Cow;
use std::collections::{hash_map, HashMap};
use std::fmt::Display;

use cranelift_codegen::binemit::CodeOffset;
use cranelift_codegen::binemit::Reloc;
use cranelift_codegen::entity::{entity_impl, PrimaryMap};
use cranelift_codegen::ir::function::VersionMarker;
use cranelift_codegen::ir::ExternalName;
use cranelift_codegen::settings::SetError;
use cranelift_codegen::{
    ir, isa, CodegenError, CompileError, Context, FinalizedMachReloc, FinalizedRelocTarget,
};

use super::DataDescription;

/// A module relocation.
#[derive(Clone)]
pub struct ModuleReloc {
    /// Offset relative to the containing section.
    pub offset: CodeOffset,
    /// Relocation kind.
    pub kind: Reloc,
    /// The external symbol this relocation refers to.
    pub name: ModuleRelocTarget,
    /// Addend.
    pub addend: i64,
}

impl ModuleReloc {
    /// Convert a `FinalizedMachReloc` into a `ModuleReloc`.
    pub fn from_mach_reloc(
        mach_reloc: &FinalizedMachReloc,
        func: &ir::Function,
        func_id: FuncId,
    ) -> Self {
        let name = match mach_reloc.target {
            FinalizedRelocTarget::ExternalName(ExternalName::User(reff)) => {
                let name = &func.params.user_named_funcs()[reff];
                ModuleRelocTarget::user(name.namespace, name.index)
            }
            FinalizedRelocTarget::ExternalName(ExternalName::TestCase(_)) => unimplemented!(),
            FinalizedRelocTarget::ExternalName(ExternalName::LibCall(libcall)) => {
                ModuleRelocTarget::LibCall(libcall)
            }
            FinalizedRelocTarget::ExternalName(ExternalName::KnownSymbol(ks)) => {
                ModuleRelocTarget::KnownSymbol(ks)
            }
            FinalizedRelocTarget::Func(offset) => {
                ModuleRelocTarget::FunctionOffset(func_id, offset)
            }
        };
        Self {
            offset: mach_reloc.offset,
            kind: mach_reloc.kind,
            name,
            addend: mach_reloc.addend,
        }
    }
}

/// A function identifier.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FuncId(u32);
entity_impl!(FuncId, "funcid");

impl From<FuncId> for ModuleRelocTarget {
    fn from(id: FuncId) -> Self {
        Self::User {
            namespace: 0,
            index: id.0,
        }
    }
}

impl FuncId {
    /// Get the `FuncId` for a given `ModuleRelocTarget`.
    pub fn from_name(name: &ModuleRelocTarget) -> FuncId {
        if let ModuleRelocTarget::User { namespace, index } = name {
            debug_assert_eq!(*namespace, 0);
            FuncId::from_u32(*index)
        } else {
            panic!("unexpected name in FuncId::from_name")
        }
    }
}

/// A data object identifier.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DataId(u32);
entity_impl!(DataId, "dataid");

impl From<DataId> for ModuleRelocTarget {
    fn from(id: DataId) -> Self {
        Self::User {
            namespace: 1,
            index: id.0,
        }
    }
}

impl DataId {
    /// Get the `DataId` for a given `ModuleRelocTarget`.
    pub fn from_name(name: &ModuleRelocTarget) -> DataId {
        if let ModuleRelocTarget::User { namespace, index } = name {
            debug_assert_eq!(*namespace, 1);
            DataId::from_u32(*index)
        } else {
            panic!("unexpected name in DataId::from_name")
        }
    }
}

/// Linkage type for declarations.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Linkage {
    /// Defined outside the module.
    Import,
    /// Defined inside the module, not visible outside.
    Local,
    /// Defined inside, visible outside, may be preempted.
    Preemptible,
    /// Defined inside, visible within the static linkage unit.
    Hidden,
    /// Defined inside, visible outside.
    Export,
}

impl Linkage {
    fn merge(a: Self, b: Self) -> Self {
        match a {
            Self::Export => Self::Export,
            Self::Hidden => match b {
                Self::Export => Self::Export,
                Self::Preemptible => Self::Preemptible,
                _ => Self::Hidden,
            },
            Self::Preemptible => match b {
                Self::Export => Self::Export,
                _ => Self::Preemptible,
            },
            Self::Local => match b {
                Self::Export => Self::Export,
                Self::Hidden => Self::Hidden,
                Self::Preemptible => Self::Preemptible,
                Self::Local | Self::Import => Self::Local,
            },
            Self::Import => b,
        }
    }

    /// Whether this linkage can have a definition.
    pub fn is_definable(self) -> bool {
        !matches!(self, Self::Import)
    }

    /// Whether the definition cannot be preempted.
    pub fn is_final(self) -> bool {
        matches!(self, Self::Local | Self::Hidden | Self::Export)
    }
}

/// Refers to either a function or data declaration.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum FuncOrDataId {
    /// A function.
    Func(FuncId),
    /// A data object.
    Data(DataId),
}

impl From<FuncOrDataId> for ModuleRelocTarget {
    fn from(id: FuncOrDataId) -> Self {
        match id {
            FuncOrDataId::Func(funcid) => Self::from(funcid),
            FuncOrDataId::Data(dataid) => Self::from(dataid),
        }
    }
}

/// Information about a declared function.
#[derive(Debug)]
pub struct FunctionDeclaration {
    /// The function name, or `None` for anonymous functions.
    pub name: Option<String>,
    /// Linkage type.
    pub linkage: Linkage,
    /// Function signature.
    pub signature: ir::Signature,
}

impl FunctionDeclaration {
    /// The linkage name. Synthesized for anonymous functions.
    pub fn linkage_name(&self, id: FuncId) -> Cow<'_, str> {
        match &self.name {
            Some(name) => Cow::Borrowed(name),
            None => Cow::Owned(format!(".Lfn{:x}", id.as_u32())),
        }
    }

    fn merge(
        &mut self,
        id: FuncId,
        linkage: Linkage,
        sig: &ir::Signature,
    ) -> Result<(), ModuleError> {
        self.linkage = Linkage::merge(self.linkage, linkage);
        if &self.signature != sig {
            return Err(ModuleError::IncompatibleSignature(
                self.linkage_name(id).into_owned(),
                self.signature.clone(),
                sig.clone(),
            ));
        }
        Ok(())
    }
}

/// Information about a declared data object.
#[derive(Debug)]
pub struct DataDeclaration {
    /// The data name.
    pub name: Option<String>,
    /// Linkage type.
    pub linkage: Linkage,
    /// Whether the data is writable.
    pub writable: bool,
    /// Whether the data is TLS.
    pub tls: bool,
}

impl DataDeclaration {
    /// The linkage name.
    pub fn linkage_name(&self, id: DataId) -> Cow<'_, str> {
        match &self.name {
            Some(name) => Cow::Borrowed(name),
            None => Cow::Owned(format!(".Ldata{:x}", id.as_u32())),
        }
    }

    fn merge(&mut self, linkage: Linkage, writable: bool, tls: bool) {
        self.linkage = Linkage::merge(self.linkage, linkage);
        self.writable = self.writable || writable;
        assert_eq!(self.tls, tls, "Can't change TLS property of data object");
    }
}

/// A translated external name.
#[derive(Clone, Debug)]
pub enum ModuleRelocTarget {
    /// User-defined function.
    User {
        /// Namespace.
        namespace: u32,
        /// Index.
        index: u32,
    },
    /// Library call.
    LibCall(ir::LibCall),
    /// Known linker symbol.
    KnownSymbol(ir::KnownSymbol),
    /// Offset inside a function.
    FunctionOffset(FuncId, CodeOffset),
}

impl ModuleRelocTarget {
    /// Creates a user-defined external name.
    pub fn user(namespace: u32, index: u32) -> Self {
        Self::User { namespace, index }
    }
}

impl Display for ModuleRelocTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::User { namespace, index } => write!(f, "u{namespace}:{index}"),
            Self::LibCall(lc) => write!(f, "%{lc}"),
            Self::KnownSymbol(ks) => write!(f, "{ks}"),
            Self::FunctionOffset(fname, offset) => write!(f, "{fname}+{offset}"),
        }
    }
}

/// Error type for Module operations.
#[derive(Debug)]
pub enum ModuleError {
    /// Identifier used before declaration.
    Undeclared(String),
    /// Incompatible re-declaration.
    IncompatibleDeclaration(String),
    /// Signature mismatch.
    IncompatibleSignature(String, ir::Signature, ir::Signature),
    /// Duplicate definition.
    DuplicateDefinition(String),
    /// Tried to define an import.
    InvalidImportDefinition(String),
    /// Cranelift codegen error.
    Compilation(CodegenError),
    /// Memory allocation failure.
    Allocation {
        /// Context message.
        message: &'static str,
        /// IO error.
        err: std::io::Error,
    },
    /// Backend error.
    Backend(Box<dyn std::error::Error + Send + Sync>),
    /// Flag error.
    Flag(SetError),
}

impl<'a> From<CompileError<'a>> for ModuleError {
    fn from(err: CompileError<'a>) -> Self {
        Self::Compilation(err.inner)
    }
}

impl From<CodegenError> for ModuleError {
    fn from(source: CodegenError) -> Self {
        Self::Compilation(source)
    }
}

impl From<SetError> for ModuleError {
    fn from(source: SetError) -> Self {
        Self::Flag(source)
    }
}

impl std::error::Error for ModuleError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Compilation(source) => Some(source),
            Self::Allocation { err: source, .. } => Some(source),
            Self::Backend(source) => Some(&**source),
            Self::Flag(source) => Some(source),
            _ => None,
        }
    }
}

impl std::fmt::Display for ModuleError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Undeclared(name) => write!(f, "Undeclared identifier: {name}"),
            Self::IncompatibleDeclaration(name) => {
                write!(f, "Incompatible declaration: {name}")
            }
            Self::IncompatibleSignature(name, prev, new) => {
                write!(
                    f,
                    "Function {name} signature {new:?} incompatible with {prev:?}"
                )
            }
            Self::DuplicateDefinition(name) => write!(f, "Duplicate definition: {name}"),
            Self::InvalidImportDefinition(name) => {
                write!(f, "Invalid import definition: {name}")
            }
            Self::Compilation(err) => write!(f, "Compilation error: {err}"),
            Self::Allocation { message, err } => write!(f, "Allocation error: {message}: {err}"),
            Self::Backend(err) => write!(f, "Backend error: {err}"),
            Self::Flag(err) => write!(f, "Flag error: {err}"),
        }
    }
}

/// Convenience alias.
pub type ModuleResult<T> = Result<T, ModuleError>;

/// Tracks all declarations in a module.
#[derive(Debug, Default)]
pub struct ModuleDeclarations {
    _version_marker: VersionMarker,
    names: HashMap<String, FuncOrDataId>,
    pub(crate) functions: PrimaryMap<FuncId, FunctionDeclaration>,
    data_objects: PrimaryMap<DataId, DataDeclaration>,
}

impl ModuleDeclarations {
    /// Look up a name.
    pub fn get_name(&self, name: &str) -> Option<FuncOrDataId> {
        self.names.get(name).copied()
    }

    /// Whether `name` refers to a function.
    pub fn is_function(name: &ModuleRelocTarget) -> bool {
        match name {
            ModuleRelocTarget::User { namespace, .. } => *namespace == 0,
            _ => panic!("unexpected module ext name"),
        }
    }

    /// Get a function declaration.
    pub fn get_function_decl(&self, func_id: FuncId) -> &FunctionDeclaration {
        &self.functions[func_id]
    }

    /// Get a data declaration.
    pub fn get_data_decl(&self, data_id: DataId) -> &DataDeclaration {
        &self.data_objects[data_id]
    }

    /// Declare a function.
    pub fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &ir::Signature,
    ) -> ModuleResult<(FuncId, Linkage)> {
        match self.names.entry(name.to_owned()) {
            hash_map::Entry::Occupied(entry) => match *entry.get() {
                FuncOrDataId::Func(id) => {
                    let existing = &mut self.functions[id];
                    existing.merge(id, linkage, signature)?;
                    Ok((id, existing.linkage))
                }
                FuncOrDataId::Data(..) => {
                    Err(ModuleError::IncompatibleDeclaration(name.to_owned()))
                }
            },
            hash_map::Entry::Vacant(entry) => {
                let id = self.functions.push(FunctionDeclaration {
                    name: Some(name.to_owned()),
                    linkage,
                    signature: signature.clone(),
                });
                entry.insert(FuncOrDataId::Func(id));
                Ok((id, self.functions[id].linkage))
            }
        }
    }

    /// Declare an anonymous function.
    pub fn declare_anonymous_function(
        &mut self,
        signature: &ir::Signature,
    ) -> ModuleResult<FuncId> {
        let id = self.functions.push(FunctionDeclaration {
            name: None,
            linkage: Linkage::Local,
            signature: signature.clone(),
        });
        Ok(id)
    }

    /// Declare a data object.
    pub fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> ModuleResult<(DataId, Linkage)> {
        match self.names.entry(name.to_owned()) {
            hash_map::Entry::Occupied(entry) => match *entry.get() {
                FuncOrDataId::Data(id) => {
                    let existing = &mut self.data_objects[id];
                    existing.merge(linkage, writable, tls);
                    Ok((id, existing.linkage))
                }
                FuncOrDataId::Func(..) => {
                    Err(ModuleError::IncompatibleDeclaration(name.to_owned()))
                }
            },
            hash_map::Entry::Vacant(entry) => {
                let id = self.data_objects.push(DataDeclaration {
                    name: Some(name.to_owned()),
                    linkage,
                    writable,
                    tls,
                });
                entry.insert(FuncOrDataId::Data(id));
                Ok((id, self.data_objects[id].linkage))
            }
        }
    }

    /// Declare an anonymous data object.
    pub fn declare_anonymous_data(&mut self, writable: bool, tls: bool) -> ModuleResult<DataId> {
        let id = self.data_objects.push(DataDeclaration {
            name: None,
            linkage: Linkage::Local,
            writable,
            tls,
        });
        Ok(id)
    }
}

/// A module for collecting and linking functions and data.
pub trait Module {
    /// Return the `TargetIsa`.
    fn isa(&self) -> &dyn isa::TargetIsa;

    /// Get all declarations.
    fn declarations(&self) -> &ModuleDeclarations;

    /// Look up a name.
    fn get_name(&self, name: &str) -> Option<FuncOrDataId> {
        self.declarations().get_name(name)
    }

    /// Return the target frontend config.
    fn target_config(&self) -> isa::TargetFrontendConfig {
        self.isa().frontend_config()
    }

    /// Create a new `Context` with the host calling convention.
    fn make_context(&self) -> Context {
        let mut ctx = Context::new();
        ctx.func.signature.call_conv = self.isa().default_call_conv();
        ctx
    }

    /// Clear and reset a `Context`.
    fn clear_context(&self, ctx: &mut Context) {
        ctx.clear();
        ctx.func.signature.call_conv = self.isa().default_call_conv();
    }

    /// Create a new `Signature` with the host calling convention.
    fn make_signature(&self) -> ir::Signature {
        ir::Signature::new(self.isa().default_call_conv())
    }

    /// Clear and reset a `Signature`.
    fn clear_signature(&self, sig: &mut ir::Signature) {
        sig.clear(self.isa().default_call_conv());
    }

    /// Declare a function.
    fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &ir::Signature,
    ) -> ModuleResult<FuncId>;

    /// Declare an anonymous function.
    fn declare_anonymous_function(&mut self, signature: &ir::Signature) -> ModuleResult<FuncId>;

    /// Declare a data object.
    fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> ModuleResult<DataId>;

    /// Declare an anonymous data object.
    fn declare_anonymous_data(&mut self, writable: bool, tls: bool) -> ModuleResult<DataId>;

    /// Declare a function reference within another function being built.
    fn declare_func_in_func(&mut self, func_id: FuncId, func: &mut ir::Function) -> ir::FuncRef {
        let decl = &self.declarations().functions[func_id];
        let signature = func.import_signature(decl.signature.clone());
        let user_name_ref = func.declare_imported_user_function(ir::UserExternalName {
            namespace: 0,
            index: func_id.as_u32(),
        });
        let colocated = decl.linkage.is_final();
        func.import_function(ir::ExtFuncData {
            name: ir::ExternalName::user(user_name_ref),
            signature,
            colocated,
        })
    }

    /// Declare a data reference within a function being built.
    fn declare_data_in_func(&self, data: DataId, func: &mut ir::Function) -> ir::GlobalValue {
        let decl = &self.declarations().data_objects[data];
        let colocated = decl.linkage.is_final();
        let user_name_ref = func.declare_imported_user_function(ir::UserExternalName {
            namespace: 1,
            index: data.as_u32(),
        });
        func.create_global_value(ir::GlobalValueData::Symbol {
            name: ir::ExternalName::user(user_name_ref),
            offset: ir::immediates::Imm64::new(0),
            colocated,
            tls: decl.tls,
        })
    }

    /// Declare a function reference within a data description.
    fn declare_func_in_data(&self, func_id: FuncId, data: &mut DataDescription) -> ir::FuncRef {
        data.import_function(ModuleRelocTarget::user(0, func_id.as_u32()))
    }

    /// Declare a data reference within a data description.
    fn declare_data_in_data(&self, data_id: DataId, data: &mut DataDescription) -> ir::GlobalValue {
        data.import_global_value(ModuleRelocTarget::user(1, data_id.as_u32()))
    }

    /// Define a function from a `Context`.
    fn define_function(&mut self, func: FuncId, ctx: &mut Context) -> ModuleResult<()> {
        self.define_function_with_control_plane(
            func,
            ctx,
            &mut cranelift_codegen::control::ControlPlane::default(),
        )
    }

    /// Define a function with an explicit control plane.
    fn define_function_with_control_plane(
        &mut self,
        func: FuncId,
        ctx: &mut Context,
        ctrl_plane: &mut cranelift_codegen::control::ControlPlane,
    ) -> ModuleResult<()>;

    /// Define a function from raw bytes.
    fn define_function_bytes(
        &mut self,
        func_id: FuncId,
        func: &ir::Function,
        alignment: u64,
        bytes: &[u8],
        relocs: &[FinalizedMachReloc],
    ) -> ModuleResult<()>;

    /// Define a data object.
    fn define_data(&mut self, data_id: DataId, data: &DataDescription) -> ModuleResult<()>;
}
