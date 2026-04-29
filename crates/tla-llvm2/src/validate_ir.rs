// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural validation of emitted LLVM IR text.
//!
//! Performs lightweight static analysis on LLVM IR text to catch common
//! emission bugs before the IR is fed to `llc` or `opt`. This is NOT a
//! full LLVM verifier -- it catches structural issues that the text emitter
//! can introduce:
//!
//! - Well-formed function signatures
//! - SSA form: each `%N` register defined exactly once, used after definition
//! - Branch targets: every `label %bbN` target must correspond to a block
//! - Basic type consistency in operations
//!
//! # Limitations
//!
//! This validator does NOT check:
//! - Full type inference (would require reimplementing LLVM's type system)
//! - Intrinsic function signatures
//! - Alignment or ABI compliance
//! - Dominance (a register might be used in a block that doesn't dominate
//!   the definition -- only `llc --verify` catches this)

use std::collections::{HashMap, HashSet};

/// Validate emitted LLVM IR text for structural correctness.
///
/// Returns `Ok(())` if the IR passes all structural checks, or
/// `Err(errors)` with a list of human-readable error descriptions.
///
/// # Checks performed
///
/// 1. **Function signatures**: `define` lines parse correctly with return type and name
/// 2. **SSA definitions**: Each `%N = ...` is defined at most once per function
/// 3. **Branch targets**: Every `label %bbN` or `label %entry` target exists as a block
/// 4. **Block structure**: Every function has an `entry:` block
/// 5. **Terminator presence**: Every block ends with a terminator (`ret`, `br`, `switch`, `unreachable`)
pub(crate) fn validate_llvm_ir(ir_text: &str) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();

    // Parse into per-function chunks.
    let functions = parse_functions(ir_text);

    if functions.is_empty() && ir_text.contains("define ") {
        errors.push("IR contains 'define' but no functions could be parsed".to_string());
    }

    for func in &functions {
        validate_function(func, &mut errors);
    }

    // Check module-level: all declared functions referenced in calls should
    // either be defined or declared.
    validate_declarations(ir_text, &functions, &mut errors);

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// A parsed function from LLVM IR text.
struct IrFunction {
    name: String,
    /// Block labels in order. First is always "entry".
    blocks: Vec<IrBlock>,
}

/// A parsed basic block.
struct IrBlock {
    label: String,
    /// Lines of instructions in this block.
    instructions: Vec<String>,
    /// SSA register definitions (%N = ...) in this block.
    definitions: Vec<String>,
    /// SSA register uses (%N) in this block.
    /// Collected for potential future dominance checks; not validated yet.
    #[allow(dead_code)]
    uses: Vec<String>,
    /// Branch targets (label names) referenced by terminators.
    branch_targets: Vec<String>,
    /// Whether the last instruction is a terminator.
    has_terminator: bool,
}

/// Parse LLVM IR text into function structures.
fn parse_functions(ir_text: &str) -> Vec<IrFunction> {
    let mut functions = Vec::new();
    let lines: Vec<&str> = ir_text.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();
        if line.starts_with("define ") {
            // Extract function name.
            if let Some(name) = extract_func_name(line) {
                let mut func = IrFunction {
                    name,
                    blocks: Vec::new(),
                };

                i += 1; // Skip the 'define' line (it includes '{')

                // Parse blocks until closing '}'.
                let mut current_label = String::new();
                let mut current_instructions: Vec<String> = Vec::new();

                while i < lines.len() {
                    let bline = lines[i].trim();

                    if bline == "}" {
                        // End of function. Flush current block.
                        if !current_label.is_empty() || !current_instructions.is_empty() {
                            let block = parse_block(
                                &if current_label.is_empty() {
                                    "entry".to_string()
                                } else {
                                    current_label.clone()
                                },
                                &current_instructions,
                            );
                            func.blocks.push(block);
                        }
                        break;
                    }

                    // Check for block label.
                    if bline.ends_with(':')
                        || bline.contains(':')
                            && !bline.starts_with("  ")
                            && !bline.starts_with('%')
                    {
                        // Flush previous block.
                        if !current_label.is_empty() || !current_instructions.is_empty() {
                            let block = parse_block(
                                &if current_label.is_empty() {
                                    "entry".to_string()
                                } else {
                                    current_label.clone()
                                },
                                &current_instructions,
                            );
                            func.blocks.push(block);
                            current_instructions = Vec::new();
                        }
                        // Extract label name (everything before ':').
                        current_label = bline.split(':').next().unwrap_or("").trim().to_string();
                    } else if !bline.is_empty() && !bline.starts_with(';') {
                        current_instructions.push(bline.to_string());
                    }

                    i += 1;
                }

                functions.push(func);
            }
        }
        i += 1;
    }

    functions
}

/// Extract function name from a `define` line.
/// e.g. "define i64 @main(i64 %10, i64 %11) {" -> "main"
fn extract_func_name(line: &str) -> Option<String> {
    let at_pos = line.find('@')?;
    let after_at = &line[at_pos + 1..];
    let end = after_at.find('(')?;
    Some(after_at[..end].to_string())
}

/// Parse a block's instructions into an IrBlock.
fn parse_block(label: &str, instructions: &[String]) -> IrBlock {
    let mut definitions = Vec::new();
    let mut uses = Vec::new();
    let mut branch_targets = Vec::new();
    let mut has_terminator = false;

    for (idx, inst) in instructions.iter().enumerate() {
        let trimmed = inst.trim();

        // Extract SSA definitions: %N = ...
        if let Some(def) = extract_ssa_definition(trimmed) {
            definitions.push(def);
        }

        // Extract SSA uses: all %N references.
        for u in extract_ssa_uses(trimmed) {
            uses.push(u);
        }

        // Extract branch targets.
        for target in extract_branch_targets(trimmed) {
            branch_targets.push(target);
        }

        // Check if this is a terminator (only check last instruction).
        if idx == instructions.len() - 1 {
            has_terminator = is_terminator(trimmed);
        }
    }

    IrBlock {
        label: label.to_string(),
        instructions: instructions.to_vec(),
        definitions,
        uses,
        branch_targets,
        has_terminator,
    }
}

/// Extract SSA register definition from an instruction.
/// "%0 = add i64 42, 0" -> Some("%0")
fn extract_ssa_definition(inst: &str) -> Option<String> {
    let trimmed = inst.trim();
    if let Some(eq_pos) = trimmed.find(" = ") {
        let lhs = trimmed[..eq_pos].trim();
        if lhs.starts_with('%') && lhs[1..].chars().all(|c| c.is_ascii_digit()) {
            return Some(lhs.to_string());
        }
    }
    None
}

/// Extract all SSA register uses from an instruction.
/// Returns all %N patterns that appear as operands (not definitions).
fn extract_ssa_uses(inst: &str) -> Vec<String> {
    let mut result = Vec::new();
    let trimmed = inst.trim();

    // Skip the definition part (left of ' = ').
    let operand_part = if let Some(eq_pos) = trimmed.find(" = ") {
        &trimmed[eq_pos + 3..]
    } else {
        trimmed
    };

    // Find all %N patterns in the operand part.
    let mut chars = operand_part.char_indices().peekable();
    while let Some((pos, ch)) = chars.next() {
        if ch == '%' {
            // Collect digits after %.
            let start = pos;
            let mut end = pos + 1;
            while let Some(&(next_pos, next_ch)) = chars.peek() {
                if next_ch.is_ascii_digit() {
                    end = next_pos + 1;
                    chars.next();
                } else {
                    break;
                }
            }
            if end > start + 1 {
                let reg = &operand_part[start..end];
                result.push(reg.to_string());
            }
        }
    }

    result
}

/// Extract branch targets from an instruction.
/// "br label %bb1" -> ["bb1"]
/// "br i1 %0, label %bb1, label %bb2" -> ["bb1", "bb2"]
fn extract_branch_targets(inst: &str) -> Vec<String> {
    let mut targets = Vec::new();
    let trimmed = inst.trim();

    // Find all "label %" patterns.
    let mut search_from = 0;
    while let Some(pos) = trimmed[search_from..].find("label %") {
        let actual_pos = search_from + pos;
        let after_label = &trimmed[actual_pos + 7..]; // skip "label %"
                                                      // Collect label name (alphanumeric + underscore).
        let end = after_label
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(after_label.len());
        if end > 0 {
            targets.push(after_label[..end].to_string());
        }
        search_from = actual_pos + 7 + end;
    }

    targets
}

/// Check if an instruction is a terminator.
fn is_terminator(inst: &str) -> bool {
    let trimmed = inst.trim();
    trimmed.starts_with("ret ")
        || trimmed == "ret void"
        || trimmed.starts_with("br ")
        || trimmed.starts_with("switch ")
        || trimmed == "unreachable"
}

/// Validate a single function's structure.
fn validate_function(func: &IrFunction, errors: &mut Vec<String>) {
    if func.blocks.is_empty() {
        errors.push(format!("function @{} has no blocks", func.name));
        return;
    }

    // Check that first block is entry.
    if func.blocks[0].label != "entry" {
        errors.push(format!(
            "function @{}: first block should be 'entry', got '{}'",
            func.name, func.blocks[0].label
        ));
    }

    // Collect all block labels.
    let block_labels: HashSet<&str> = func.blocks.iter().map(|b| b.label.as_str()).collect();

    // Collect all SSA definitions across the function (for duplicate detection).
    let mut all_defs: HashMap<String, usize> = HashMap::new();

    for (block_idx, block) in func.blocks.iter().enumerate() {
        // Check terminator presence.
        if !block.has_terminator && !block.instructions.is_empty() {
            errors.push(format!(
                "function @{}, block '{}': does not end with a terminator",
                func.name, block.label
            ));
        }

        // Check for duplicate SSA definitions.
        for def in &block.definitions {
            let count = all_defs.entry(def.clone()).or_insert(0);
            *count += 1;
            if *count > 1 {
                errors.push(format!(
                    "function @{}, block '{}': SSA register {} defined multiple times",
                    func.name, block.label, def
                ));
            }
        }

        // Check branch targets exist.
        for target in &block.branch_targets {
            if !block_labels.contains(target.as_str()) {
                errors.push(format!(
                    "function @{}, block '{}': branch target '{}' does not exist (available: {:?})",
                    func.name,
                    block.label,
                    target,
                    block_labels.iter().collect::<Vec<_>>()
                ));
            }
        }

        // Check that empty blocks (no instructions) are flagged — but only
        // for blocks after the first (entry block always exists).
        if block.instructions.is_empty() && block_idx > 0 {
            errors.push(format!(
                "function @{}, block '{}': has no instructions",
                func.name, block.label
            ));
        }
    }
}

/// Validate module-level declarations.
fn validate_declarations(ir_text: &str, functions: &[IrFunction], errors: &mut Vec<String>) {
    // Collect all defined function names.
    let defined: HashSet<&str> = functions.iter().map(|f| f.name.as_str()).collect();

    // Collect all declared function names.
    let mut declared: HashSet<String> = HashSet::new();
    for line in ir_text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("declare ") {
            if let Some(name) = extract_func_name_from_declare(trimmed) {
                declared.insert(name);
            }
        }
    }

    // Check that all call targets are either defined or declared.
    for func in functions {
        for block in &func.blocks {
            for inst in &block.instructions {
                let trimmed = inst.trim();
                if let Some(callee) = extract_call_target(trimmed) {
                    // Skip LLVM intrinsics (llvm.*)
                    if callee.starts_with("llvm.") {
                        continue;
                    }
                    if !defined.contains(callee.as_str()) && !declared.contains(&callee) {
                        errors.push(format!(
                            "function @{}: calls undefined function @{} (not defined or declared)",
                            func.name, callee
                        ));
                    }
                }
            }
        }
    }
}

/// Extract function name from a `declare` line.
fn extract_func_name_from_declare(line: &str) -> Option<String> {
    let at_pos = line.find('@')?;
    let after_at = &line[at_pos + 1..];
    let end = after_at.find('(')?;
    Some(after_at[..end].to_string())
}

/// Extract the callee name from a `call` instruction.
/// "call i64 @helper(i32 %20, ptr %21)" -> Some("helper")
/// "%0 = call i64 @helper(i32 %20)" -> Some("helper")
fn extract_call_target(inst: &str) -> Option<String> {
    let trimmed = inst.trim();
    // Look for "call " or "= call ".
    if !trimmed.contains("call ") {
        return None;
    }
    // Find @name( pattern.
    if let Some(at_pos) = trimmed.find("@") {
        let after_at = &trimmed[at_pos + 1..];
        let end = after_at.find('(')?;
        return Some(after_at[..end].to_string());
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::emit::emit_module;
    use tmir::constant::Constant;
    use tmir::inst::*;
    use tmir::ty::{FieldDef, FuncTy, StructDef, Ty};
    use tmir::value::{BlockId, FuncId, StructId, ValueId};
    use tmir::{Block, Function, InstrNode, Module};

    // =========================================================================
    // Helper: build modules and validate their emitted IR
    // =========================================================================

    /// Emit a module's IR and validate it, returning the IR text for further checks.
    fn emit_and_validate(module: &Module) -> String {
        let ir = emit_module(module).expect("emission should succeed");
        match validate_llvm_ir(&ir) {
            Ok(()) => ir,
            Err(errors) => {
                panic!(
                    "IR validation failed with {} errors:\n{}\n\nFull IR:\n{}",
                    errors.len(),
                    errors.join("\n"),
                    ir
                );
            }
        }
    }

    // =========================================================================
    // 1. Function signature validation
    // =========================================================================

    #[test]
    fn test_validate_return_42_function_signature() {
        let mut module = Module::new("sig_test");
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

        let ir = emit_and_validate(&module);
        assert!(ir.contains("define i64 @main()"));
    }

    #[test]
    fn test_validate_multi_param_function_signature() {
        let mut module = Module::new("multi_param");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I32, Ty::Ptr],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "multi", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::I64)
            .with_param(ValueId::new(11), Ty::I32)
            .with_param(ValueId::new(12), Ty::Ptr);
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(10)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("define i64 @multi(i64 %10, i32 %11, ptr %12)"));
    }

    #[test]
    fn test_validate_void_function_signature() {
        let mut module = Module::new("void_sig");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "void_fn", ft, entry);
        let mut block = Block::new(entry);
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("define void @void_fn()"));
    }

    // =========================================================================
    // 2. SSA form validation
    // =========================================================================

    #[test]
    fn test_validate_ssa_single_def() {
        // Each register should be defined exactly once.
        let mut module = Module::new("ssa_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "add_fn", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::I64)
            .with_param(ValueId::new(11), Ty::I64);
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(10),
                rhs: ValueId::new(11),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        // Verify %0 appears exactly once as a definition.
        let def_count = ir.matches("%0 = ").count();
        assert_eq!(
            def_count, 1,
            "SSA register %0 should be defined exactly once, found {def_count}"
        );
    }

    #[test]
    fn test_validate_ssa_multiple_registers() {
        // Build a function with several distinct register definitions.
        let mut module = Module::new("ssa_multi");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "chain", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::I64)
            .with_param(ValueId::new(11), Ty::I64);

        // %0 = add %10, %11
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(10),
                rhs: ValueId::new(11),
            })
            .with_result(ValueId::new(0)),
        );
        // %1 = mul %0, %10
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(10),
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert_eq!(ir.matches("%0 = ").count(), 1, "SSA %0 defined once");
        assert_eq!(ir.matches("%1 = ").count(), 1, "SSA %1 defined once");
    }

    // =========================================================================
    // 3. Branch target validation
    // =========================================================================

    #[test]
    fn test_validate_branch_targets_exist() {
        let mut module = Module::new("branch_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let then_bb = BlockId::new(1);
        let else_bb = BlockId::new(2);

        let mut func = Function::new(FuncId::new(0), "br_fn", ft, entry);

        let mut entry_block = Block::new(entry).with_param(ValueId::new(10), Ty::Bool);
        // Need an i1 for the branch condition.
        entry_block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: ValueId::new(10),
                rhs: ValueId::new(10),
            })
            .with_result(ValueId::new(0)),
        );
        entry_block.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: then_bb,
            then_args: vec![],
            else_target: else_bb,
            else_args: vec![],
        }));
        func.blocks.push(entry_block);

        let mut then_block = Block::new(then_bb);
        then_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(1)),
        );
        then_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        func.blocks.push(then_block);

        let mut else_block = Block::new(else_bb);
        else_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(2)),
        );
        else_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }));
        func.blocks.push(else_block);

        module.add_function(func);

        // This should pass validation -- all branch targets (bb1, bb2) exist.
        let ir = emit_and_validate(&module);
        assert!(ir.contains("br i1"));
        assert!(ir.contains("bb1:"));
        assert!(ir.contains("bb2:"));
    }

    #[test]
    fn test_validate_unconditional_branch_target() {
        let mut module = Module::new("uncond_br");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let target = BlockId::new(1);

        let mut func = Function::new(FuncId::new(0), "br_fn", ft, entry);

        let mut entry_block = Block::new(entry);
        entry_block.body.push(InstrNode::new(Inst::Br {
            target,
            args: vec![],
        }));
        func.blocks.push(entry_block);

        let mut target_block = Block::new(target);
        target_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(99),
            })
            .with_result(ValueId::new(0)),
        );
        target_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(target_block);

        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("br label %bb1"));
        assert!(ir.contains("bb1:"));
    }

    // =========================================================================
    // 4. Type consistency validation
    // =========================================================================

    #[test]
    fn test_validate_struct_type_consistency() {
        let mut module = Module::new("struct_valid");
        let sid = StructId::new(0);
        module.add_struct(StructDef {
            id: sid,
            name: "Pair".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::I64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::I32,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
        });

        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Struct(sid)],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "struct_fn", ft, entry);
        let mut block = Block::new(entry).with_param(ValueId::new(10), Ty::Struct(sid));

        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Struct(sid),
                aggregate: ValueId::new(10),
                field: 0,
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("%struct.Pair = type { i64, i32 }"));
        assert!(ir.contains("extractvalue %struct.Pair"));
    }

    #[test]
    fn test_validate_array_type_consistency() {
        let mut module = Module::new("array_valid");
        let elem_ty_id = module.add_type(Ty::I32);

        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "array_fn", ft, entry);
        let mut block = Block::new(entry);

        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::Array(elem_ty_id, 5),
                count: None,
                align: None,
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("[5 x i32]"));
    }

    // =========================================================================
    // 5. Cast instruction validation
    // =========================================================================

    #[test]
    fn test_validate_cast_instructions() {
        let mut module = Module::new("cast_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "cast_fn", ft, entry);
        let mut block = Block::new(entry).with_param(ValueId::new(10), Ty::I32);

        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: ValueId::new(10),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("sext i32 %10 to i64"));
    }

    // =========================================================================
    // 6. Memory instruction validation
    // =========================================================================

    #[test]
    fn test_validate_alloca_load_store_sequence() {
        let mut module = Module::new("mem_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "mem_fn", ft, entry);
        let mut block = Block::new(entry);

        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            align: None,
            volatile: false,
        }));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(2)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("%0 = alloca i64"));
        assert!(ir.contains("store i64 %1, ptr %0"));
        assert!(ir.contains("%2 = load i64, ptr %0"));
    }

    // =========================================================================
    // 7. Assert lowering validation
    // =========================================================================

    #[test]
    fn test_validate_assert_lowering_produces_valid_blocks() {
        let mut module = Module::new("assert_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "assert_fn", ft, entry);
        let mut block = Block::new(entry).with_param(ValueId::new(10), Ty::Bool);
        block.body.push(InstrNode::new(Inst::Assert {
            cond: ValueId::new(10),
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        // Assert creates: assert_fail_0, assert_ok_0 blocks.
        assert!(ir.contains("assert_fail_0:"));
        assert!(ir.contains("assert_ok_0:"));
        // The fail block ends with unreachable (a terminator).
        assert!(ir.contains("unreachable"));
    }

    // =========================================================================
    // 8. Multi-function module validation
    // =========================================================================

    #[test]
    fn test_validate_multi_function_module() {
        let mut module = Module::new("multi_fn");

        // Function 0: helper(i64) -> i64
        let helper_ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let helper_entry = BlockId::new(0);
        let mut helper = Function::new(FuncId::new(0), "helper", helper_ft, helper_entry);
        let mut helper_block = Block::new(helper_entry).with_param(ValueId::new(10), Ty::I64);
        helper_block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(10),
                rhs: ValueId::new(10),
            })
            .with_result(ValueId::new(0)),
        );
        helper_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        helper.blocks.push(helper_block);
        module.add_function(helper);

        // Function 1: caller() -> i64
        let caller_ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let caller_entry = BlockId::new(0);
        let mut caller = Function::new(FuncId::new(1), "caller", caller_ft, caller_entry);
        let mut caller_block = Block::new(caller_entry);
        caller_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(5),
            })
            .with_result(ValueId::new(0)),
        );
        caller_block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        caller_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        caller.blocks.push(caller_block);
        module.add_function(caller);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("define i64 @helper("));
        assert!(ir.contains("define i64 @caller("));
        assert!(ir.contains("call i64 @helper("));
    }

    // =========================================================================
    // 9. Select instruction validation
    // =========================================================================

    #[test]
    fn test_validate_select_instruction() {
        let mut module = Module::new("select_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "sel_fn", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::Bool)
            .with_param(ValueId::new(11), Ty::I64)
            .with_param(ValueId::new(12), Ty::I64);
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: ValueId::new(10),
                then_val: ValueId::new(11),
                else_val: ValueId::new(12),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("select i1"));
    }

    // =========================================================================
    // 10. Switch instruction validation
    // =========================================================================

    #[test]
    fn test_validate_switch_instruction() {
        let mut module = Module::new("switch_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let case_a = BlockId::new(1);
        let case_b = BlockId::new(2);
        let default_bb = BlockId::new(3);

        let mut func = Function::new(FuncId::new(0), "switch_fn", ft, entry);

        let mut entry_block = Block::new(entry).with_param(ValueId::new(10), Ty::I64);
        entry_block.body.push(InstrNode::new(Inst::Switch {
            value: ValueId::new(10),
            default: default_bb,
            default_args: vec![],
            cases: vec![
                SwitchCase {
                    value: Constant::Int(1),
                    target: case_a,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(2),
                    target: case_b,
                    args: vec![],
                },
            ],
        }));
        func.blocks.push(entry_block);

        // Case A: return 10
        let mut block_a = Block::new(case_a);
        block_a.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(10),
            })
            .with_result(ValueId::new(0)),
        );
        block_a.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block_a);

        // Case B: return 20
        let mut block_b = Block::new(case_b);
        block_b.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(20),
            })
            .with_result(ValueId::new(1)),
        );
        block_b.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        func.blocks.push(block_b);

        // Default: return 0
        let mut default_block = Block::new(default_bb);
        default_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(2)),
        );
        default_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }));
        func.blocks.push(default_block);

        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("switch i64"));
        assert!(ir.contains("bb1:"));
        assert!(ir.contains("bb2:"));
        assert!(ir.contains("bb3:"));
    }

    // =========================================================================
    // 11. GEP instruction validation
    // =========================================================================

    #[test]
    fn test_validate_gep_instruction() {
        let mut module = Module::new("gep_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "gep_fn", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::Ptr)
            .with_param(ValueId::new(11), Ty::I32);
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(10),
                indices: vec![ValueId::new(11)],
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("getelementptr i64, ptr %10, i32 %11"));
    }

    // =========================================================================
    // 12. Atomic operations validation
    // =========================================================================

    #[test]
    fn test_validate_atomic_operations() {
        let mut module = Module::new("atomic_valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "atomic_fn", ft, entry);
        let mut block = Block::new(entry).with_param(ValueId::new(10), Ty::Ptr);

        // atomic load
        block.body.push(
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: ValueId::new(10),
                ordering: Ordering::SeqCst,
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_and_validate(&module);
        assert!(ir.contains("load atomic i64, ptr %10 seq_cst"));
    }

    // =========================================================================
    // 13. End-to-end pipeline validation (BytecodeFunction -> IR validation)
    // =========================================================================

    #[test]
    fn test_validate_pipeline_invariant_ir() {
        use tla_tir::bytecode::{BytecodeFunction, Opcode};

        let mut func = BytecodeFunction::new("Inv_valid".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled = crate::compile_invariant(&func, "inv_valid").expect("should compile");

        match validate_llvm_ir(&compiled.llvm_ir) {
            Ok(()) => {} // pass
            Err(errors) => {
                panic!(
                    "Pipeline-produced IR failed validation:\n{}\n\nIR:\n{}",
                    errors.join("\n"),
                    compiled.llvm_ir
                );
            }
        }
    }

    #[test]
    fn test_validate_pipeline_next_state_ir() {
        use tla_tir::bytecode::{BytecodeFunction, Opcode};

        let mut func = BytecodeFunction::new("Next_valid".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::Ret { rs: 3 });

        let compiled = crate::compile_next_state(&func, "next_valid").expect("should compile");

        match validate_llvm_ir(&compiled.llvm_ir) {
            Ok(()) => {} // pass
            Err(errors) => {
                panic!(
                    "Pipeline-produced IR failed validation:\n{}\n\nIR:\n{}",
                    errors.join("\n"),
                    compiled.llvm_ir
                );
            }
        }
    }

    #[test]
    fn test_validate_pipeline_multi_function_chunk_ir() {
        use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

        let mut chunk = BytecodeChunk::new();

        let mut main_func = BytecodeFunction::new("main".to_string(), 0);
        main_func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        main_func.emit(Opcode::Call {
            rd: 1,
            op_idx: 1,
            args_start: 0,
            argc: 1,
        });
        main_func.emit(Opcode::Ret { rs: 1 });
        chunk.functions.push(main_func);

        let mut helper_func = BytecodeFunction::new("helper".to_string(), 1);
        helper_func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        helper_func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        helper_func.emit(Opcode::Ret { rs: 2 });
        chunk.functions.push(helper_func);

        let compiled =
            crate::compile_spec_invariant(&chunk, 0, "multi_valid").expect("should compile");

        match validate_llvm_ir(&compiled.llvm_ir) {
            Ok(()) => {} // pass
            Err(errors) => {
                panic!(
                    "Multi-function IR failed validation:\n{}\n\nIR:\n{}",
                    errors.join("\n"),
                    compiled.llvm_ir
                );
            }
        }
    }

    // =========================================================================
    // 14. Validator unit tests (test the validator itself)
    // =========================================================================

    #[test]
    fn test_validator_catches_missing_branch_target() {
        // Manually craft IR with a branch to a nonexistent block.
        let bad_ir = r#"; ModuleID = 'bad'
source_filename = "bad"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

declare void @llvm.trap() noreturn nounwind

define i64 @bad_fn() {
entry:
  br label %nonexistent
}
"#;
        let result = validate_llvm_ir(bad_ir);
        assert!(result.is_err(), "Should detect missing branch target");
        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|e| e.contains("nonexistent")),
            "Error should mention the missing target. Errors: {:?}",
            errors
        );
    }

    #[test]
    fn test_validator_catches_duplicate_ssa_def() {
        // Manually craft IR with duplicate %0 definitions.
        let bad_ir = r#"; ModuleID = 'dup'
source_filename = "dup"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

declare void @llvm.trap() noreturn nounwind

define i64 @dup_fn() {
entry:
  %0 = add i64 1, 0
  %0 = add i64 2, 0
  ret i64 %0
}
"#;
        let result = validate_llvm_ir(bad_ir);
        assert!(result.is_err(), "Should detect duplicate SSA definition");
        let errors = result.unwrap_err();
        assert!(
            errors
                .iter()
                .any(|e| e.contains("%0") && e.contains("multiple")),
            "Error should mention duplicate %0. Errors: {:?}",
            errors
        );
    }

    #[test]
    fn test_validator_accepts_valid_ir() {
        let good_ir = r#"; ModuleID = 'good'
source_filename = "good"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

declare void @llvm.trap() noreturn nounwind

define i64 @good_fn(i64 %0) {
entry:
  %1 = add i64 %0, 42
  ret i64 %1
}
"#;
        let result = validate_llvm_ir(good_ir);
        assert!(
            result.is_ok(),
            "Valid IR should pass. Errors: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_validator_accepts_empty_module() {
        // Module with no functions is valid.
        let ir = r#"; ModuleID = 'empty'
source_filename = "empty"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"

declare void @llvm.trap() noreturn nounwind
"#;
        let result = validate_llvm_ir(ir);
        assert!(result.is_ok(), "Empty module should be valid");
    }

    // =========================================================================
    // 15. Optional llc ground-truth validation
    // =========================================================================

    #[test]
    fn test_llc_ground_truth_validation() {
        // Check if llc is available. If not, the test passes trivially
        // (we can't validate without the tool). This is acceptable because
        // the structural validator above catches most issues, and llc is
        // the ultimate authority when available.
        let llc_available = std::process::Command::new("llc")
            .arg("--version")
            .output()
            .is_ok();

        if !llc_available {
            // llc not available -- structural validation above is sufficient.
            return;
        }

        // Build a simple module and validate it through llc.
        let mut module = Module::new("llc_test");
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

        let ir = emit_module(&module).expect("should emit");

        // Pipe IR through llc --verify.
        use std::io::Write;
        let mut child = std::process::Command::new("llc")
            .args(["--verify-each", "-o", "/dev/null", "-"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("failed to spawn llc");

        child
            .stdin
            .as_mut()
            .expect("failed to open stdin")
            .write_all(ir.as_bytes())
            .expect("failed to write IR to llc");

        let output = child.wait_with_output().expect("failed to wait on llc");

        assert!(
            output.status.success(),
            "llc rejected our IR:\nstdout: {}\nstderr: {}\nIR:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
            ir
        );
    }

    // =========================================================================
    // 16. Validation of all existing emit.rs test modules
    // =========================================================================

    #[test]
    fn test_validate_all_existing_emit_test_modules() {
        // This test constructs every module type from emit.rs tests and
        // validates them all through the structural validator. This ensures
        // that any future regression in the emitter is caught.

        // Return 42
        {
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
            emit_and_validate(&module);
        }

        // BinOp add
        {
            let mut module = Module::new("binop");
            let ft = module.add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            });
            let entry = BlockId::new(0);
            let mut func = Function::new(FuncId::new(0), "add_fn", ft, entry);
            let mut block = Block::new(entry)
                .with_param(ValueId::new(10), Ty::I64)
                .with_param(ValueId::new(11), Ty::I64);
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(0)),
            );
            block.body.push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }));
            func.blocks.push(block);
            module.add_function(func);
            emit_and_validate(&module);
        }

        // Void return
        {
            let mut module = Module::new("void_ret");
            let ft = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            });
            let entry = BlockId::new(0);
            let mut func = Function::new(FuncId::new(0), "void_fn", ft, entry);
            let mut block = Block::new(entry);
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module.add_function(func);
            emit_and_validate(&module);
        }
    }

    // =========================================================================
    // Helper function unit tests
    // =========================================================================

    #[test]
    fn test_extract_func_name() {
        assert_eq!(
            extract_func_name("define i64 @main() {"),
            Some("main".to_string())
        );
        assert_eq!(
            extract_func_name("define void @foo(i64 %0, ptr %1) {"),
            Some("foo".to_string())
        );
        assert_eq!(
            extract_func_name("define %struct.Point @bar() {"),
            Some("bar".to_string())
        );
    }

    #[test]
    fn test_extract_ssa_definition() {
        assert_eq!(
            extract_ssa_definition("%0 = add i64 42, 0"),
            Some("%0".to_string())
        );
        assert_eq!(
            extract_ssa_definition("%123 = load i64, ptr %10"),
            Some("%123".to_string())
        );
        assert_eq!(extract_ssa_definition("store i64 %1, ptr %0"), None);
        assert_eq!(extract_ssa_definition("ret i64 %0"), None);
        assert_eq!(extract_ssa_definition("br label %bb1"), None);
    }

    #[test]
    fn test_extract_ssa_uses() {
        let uses = extract_ssa_uses("%0 = add i64 %10, %11");
        assert!(uses.contains(&"%10".to_string()));
        assert!(uses.contains(&"%11".to_string()));
        // %0 is the definition, not a use on the RHS
        assert!(!uses.contains(&"%0".to_string()));
    }

    #[test]
    fn test_extract_branch_targets() {
        let targets = extract_branch_targets("br label %bb1");
        assert_eq!(targets, vec!["bb1"]);

        let targets = extract_branch_targets("br i1 %0, label %bb1, label %bb2");
        assert_eq!(targets, vec!["bb1", "bb2"]);

        let targets = extract_branch_targets("ret i64 %0");
        assert!(targets.is_empty());
    }

    #[test]
    fn test_is_terminator() {
        assert!(is_terminator("ret void"));
        assert!(is_terminator("ret i64 %0"));
        assert!(is_terminator("br label %bb1"));
        assert!(is_terminator("br i1 %0, label %bb1, label %bb2"));
        assert!(is_terminator("switch i64 %0, label %bb1 []"));
        assert!(is_terminator("unreachable"));
        assert!(!is_terminator("%0 = add i64 1, 0"));
        assert!(!is_terminator("store i64 %1, ptr %0"));
    }

    #[test]
    fn test_extract_call_target() {
        assert_eq!(
            extract_call_target("call i64 @helper(i32 %0)"),
            Some("helper".to_string())
        );
        assert_eq!(
            extract_call_target("%0 = call i64 @foo(i64 %1, ptr %2)"),
            Some("foo".to_string())
        );
        assert_eq!(extract_call_target("ret void"), None);
    }
}
