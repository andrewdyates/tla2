// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Vendored from cranelift-module 0.112.3, src/data_context.rs
// Original: Copyright (c) Bytecode Alliance. Apache-2.0 WITH LLVM-exception.
// Retained because the Module trait signature references DataDescription.

use cranelift_codegen::binemit::{Addend, CodeOffset, Reloc};
use cranelift_codegen::entity::PrimaryMap;
use cranelift_codegen::ir;

use super::{ModuleReloc, ModuleRelocTarget};

/// How data is initialized.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Init {
    /// Not yet initialized.
    Uninitialized,
    /// Zero-initialized.
    Zeros {
        /// The size of the data.
        size: usize,
    },
    /// Initialized with specific bytes.
    Bytes {
        /// The contents (also implies size).
        contents: Box<[u8]>,
    },
}

impl Init {
    /// Return the size of the data.
    pub fn size(&self) -> usize {
        match *self {
            Self::Uninitialized => panic!("data size not initialized yet"),
            Self::Zeros { size } => size,
            Self::Bytes { ref contents } => contents.len(),
        }
    }
}

/// Description of a data object.
#[derive(Clone, Debug)]
pub struct DataDescription {
    /// How the data should be initialized.
    pub init: Init,
    /// External function declarations.
    pub function_decls: PrimaryMap<ir::FuncRef, ModuleRelocTarget>,
    /// External data object declarations.
    pub data_decls: PrimaryMap<ir::GlobalValue, ModuleRelocTarget>,
    /// Function addresses to write at specified offsets.
    pub function_relocs: Vec<(CodeOffset, ir::FuncRef)>,
    /// Data addresses to write at specified offsets.
    pub data_relocs: Vec<(CodeOffset, ir::GlobalValue, Addend)>,
    /// Object file section.
    pub custom_segment_section: Option<(String, String)>,
    /// Alignment in bytes.
    pub align: Option<u64>,
}

impl DataDescription {
    /// Allocate a new `DataDescription`.
    pub fn new() -> Self {
        Self {
            init: Init::Uninitialized,
            function_decls: PrimaryMap::new(),
            data_decls: PrimaryMap::new(),
            function_relocs: vec![],
            data_relocs: vec![],
            custom_segment_section: None,
            align: None,
        }
    }

    /// Import a function reference into this data description.
    pub fn import_function(&mut self, name: ModuleRelocTarget) -> ir::FuncRef {
        self.function_decls.push(name)
    }

    /// Import a global value reference into this data description.
    pub fn import_global_value(&mut self, name: ModuleRelocTarget) -> ir::GlobalValue {
        self.data_decls.push(name)
    }

    /// An iterator over all relocations of the data object.
    pub fn all_relocs<'a>(
        &'a self,
        pointer_reloc: Reloc,
    ) -> impl Iterator<Item = ModuleReloc> + 'a {
        let func_relocs = self
            .function_relocs
            .iter()
            .map(move |&(offset, id)| ModuleReloc {
                kind: pointer_reloc,
                offset,
                name: self.function_decls[id].clone(),
                addend: 0,
            });
        let data_relocs = self
            .data_relocs
            .iter()
            .map(move |&(offset, id, addend)| ModuleReloc {
                kind: pointer_reloc,
                offset,
                name: self.data_decls[id].clone(),
                addend,
            });
        func_relocs.chain(data_relocs)
    }
}
