// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure-Rust LLVM IR text builder types.

use std::fmt::{self, Display, Write};

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum LlvmType {
    I1,
    I8,
    I32,
    I64,
    Ptr,
    Void,
    Array(Box<LlvmType>, usize),
    Struct(Vec<LlvmType>),
}

impl Display for LlvmType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I1 => f.write_str("i1"),
            Self::I8 => f.write_str("i8"),
            Self::I32 => f.write_str("i32"),
            Self::I64 => f.write_str("i64"),
            Self::Ptr => f.write_str("ptr"),
            Self::Void => f.write_str("void"),
            Self::Array(element_type, len) => write!(f, "[{len} x {element_type}]"),
            Self::Struct(field_types) => {
                f.write_str("{")?;
                if !field_types.is_empty() {
                    f.write_str(" ")?;
                    for (index, field_type) in field_types.iter().enumerate() {
                        if index > 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{field_type}")?;
                    }
                    f.write_str(" ")?;
                }
                f.write_str("}")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct LlvmValue(pub(crate) String);

impl Display for LlvmValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LlvmBlock {
    pub(crate) name: String,
    pub(crate) instructions: Vec<String>,
    pub(crate) terminated: bool,
}

impl LlvmBlock {
    pub(crate) fn emit_instruction(&mut self, inst: String) {
        self.instructions.push(inst);
    }

    pub(crate) fn is_terminated(&self) -> bool {
        self.terminated
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LlvmFunction {
    pub(crate) name: String,
    pub(crate) params: Vec<(LlvmValue, LlvmType)>,
    pub(crate) return_type: LlvmType,
    pub(crate) blocks: Vec<LlvmBlock>,
    pub(crate) next_reg: u32,
}

impl LlvmFunction {
    pub(crate) fn new_block(&mut self, name: &str) -> usize {
        let block_index = self.blocks.len();
        self.blocks.push(LlvmBlock {
            name: name.to_owned(),
            instructions: Vec::new(),
            terminated: false,
        });
        block_index
    }

    pub(crate) fn fresh_reg(&mut self) -> LlvmValue {
        let reg = LlvmValue(format!("%{}", self.next_reg));
        self.next_reg += 1;
        reg
    }

    pub(crate) fn emit(&mut self, block: usize, inst: String) {
        if let Some(block) = self.blocks.get_mut(block) {
            block.emit_instruction(inst);
        }
    }

    pub(crate) fn emit_with_result(&mut self, block: usize, inst_template: &str) -> LlvmValue {
        let result = self.fresh_reg();
        self.emit(block, format!("{result} = {inst_template}"));
        result
    }

    pub(crate) fn terminate(&mut self, block: usize, inst: String) {
        if let Some(block) = self.blocks.get_mut(block) {
            block.emit_instruction(inst);
            block.terminated = true;
        }
    }

    pub(crate) fn to_ir(&self) -> String {
        let mut ir = String::new();
        let _ = write!(ir, "define {} @{}(", self.return_type, self.name);
        for (index, (value, value_type)) in self.params.iter().enumerate() {
            if index > 0 {
                ir.push_str(", ");
            }
            let _ = write!(ir, "{} {}", value_type, value);
        }
        ir.push_str(") {\n");

        for block in &self.blocks {
            let _ = writeln!(ir, "{}:", block.name);
            for instruction in &block.instructions {
                let _ = writeln!(ir, "  {instruction}");
            }
        }

        ir.push_str("}\n");
        ir
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LlvmModule {
    pub(crate) target_triple: String,
    pub(crate) functions: Vec<LlvmFunction>,
    pub(crate) type_declarations: Vec<String>,
    /// External function declarations (e.g., LLVM intrinsics).
    pub(crate) declarations: Vec<String>,
}

impl LlvmModule {
    pub(crate) fn new(target_triple: &str) -> Self {
        Self {
            target_triple: target_triple.to_owned(),
            functions: Vec::new(),
            type_declarations: Vec::new(),
            declarations: Vec::new(),
        }
    }

    pub(crate) fn add_function(&mut self, func: LlvmFunction) {
        self.functions.push(func);
    }

    #[allow(dead_code)]
    pub(crate) fn add_type_declaration(&mut self, decl: String) {
        self.type_declarations.push(decl);
    }

    /// Add an external function declaration (e.g., `declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)`).
    pub(crate) fn add_declaration(&mut self, decl: String) {
        if !self.declarations.contains(&decl) {
            self.declarations.push(decl);
        }
    }

    pub(crate) fn to_ir(&self) -> String {
        let mut ir = String::new();
        let _ = writeln!(ir, "target triple = \"{}\"", self.target_triple);

        if !self.type_declarations.is_empty()
            || !self.declarations.is_empty()
            || !self.functions.is_empty()
        {
            ir.push('\n');
        }

        for declaration in &self.type_declarations {
            let _ = writeln!(ir, "{}", declaration.trim_end());
        }

        if !self.type_declarations.is_empty()
            && (!self.declarations.is_empty() || !self.functions.is_empty())
        {
            ir.push('\n');
        }

        for declaration in &self.declarations {
            let _ = writeln!(ir, "{}", declaration.trim_end());
        }

        if !self.declarations.is_empty() && !self.functions.is_empty() {
            ir.push('\n');
        }

        for (index, function) in self.functions.iter().enumerate() {
            if index > 0 {
                ir.push('\n');
            }
            ir.push_str(function.to_ir().trim_end());
            ir.push('\n');
        }

        ir
    }
}
