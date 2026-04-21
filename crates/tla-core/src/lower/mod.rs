// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CST to AST lowering
//!
//! This module converts the lossless Concrete Syntax Tree (CST) produced by the
//! parser into a typed Abstract Syntax Tree (AST) suitable for semantic analysis.
//!
//! The CST preserves all whitespace and comments, while the AST only contains
//! the semantically meaningful parts of the source code.

mod analysis;
mod assume_prove;
mod ctx;
mod expr_core;
mod expr_except;
mod expr_labels;
mod expr_modules_subscripts;
mod expr_operator_map;
mod expr_quantifiers;
mod expr_records_tuples;
mod expr_sets_funcs;
mod module_items;
mod operators;
mod proof;
mod recursive;

#[cfg(test)]
#[path = "tests/mod.rs"]
mod tests;

// Re-exports
pub use analysis::{
    compute_contains_prime, compute_guards_depend_on_prime, compute_has_primed_param,
    operator_has_primed_param,
};
pub(crate) use ctx::LowerCtx;
pub use ctx::LowerError;
pub use recursive::compute_is_recursive;

use crate::ast::{Expr, Module};
use crate::span::{FileId, Spanned};
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

use self::expr_core::lower_expr;
use self::module_items::{
    lower_main_module as lower_main_module_impl, lower_module, lower_module_node,
};

/// Result of lowering
pub struct LowerResult {
    pub module: Option<Module>,
    pub errors: Vec<LowerError>,
}

/// Result of lowering all modules in a syntax tree (including inline submodules)
pub(crate) struct LowerAllResult {
    pub(crate) modules: Vec<Module>,
    pub(crate) errors: Vec<LowerError>,
}

/// Lower a parsed syntax tree to an AST
pub fn lower(file_id: FileId, root: &SyntaxNode) -> LowerResult {
    let mut ctx = LowerCtx::new(file_id);
    let module = lower_module(&mut ctx, root);
    let errors = ctx.take_errors();
    LowerResult { module, errors }
}

/// Lower the "main" module from a syntax tree that may contain multiple modules.
///
/// For multi-module files, the last top-level module is the main entry point,
/// unless `hint_name` matches an earlier module (e.g., when the filename specifies
/// which module is the target). Single-module files behave identically to [`lower`].
///
/// This should be used instead of [`lower`] when parsing the main spec file, because
/// `lower` always returns the first module — which is a dependency, not the main module,
/// in multi-module files.
pub fn lower_main_module(
    file_id: FileId,
    root: &SyntaxNode,
    hint_name: Option<&str>,
) -> LowerResult {
    let mut ctx = LowerCtx::new(file_id);
    let module = lower_main_module_impl(&mut ctx, root, hint_name);
    let errors = ctx.take_errors();
    LowerResult { module, errors }
}

/// Lower all `MODULE` nodes in the syntax tree to AST modules.
///
/// TLA+ allows defining inline submodules (a `MODULE` nested within another `MODULE`).
/// For semantic analysis, tools often need to resolve `INSTANCE Inner` against such
/// inline module definitions.
pub(crate) fn lower_all_modules(file_id: FileId, root: &SyntaxNode) -> LowerAllResult {
    let mut ctx = LowerCtx::new(file_id);
    let mut modules = Vec::new();

    for node in root
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::Module)
    {
        if let Some(module) = lower_module_node(&mut ctx, &node) {
            modules.push(module);
        }
    }

    let errors = ctx.take_errors();
    LowerAllResult { modules, errors }
}

/// Lower a single expression syntax node to an AST expression
///
/// This is useful for lowering inline expressions extracted from the syntax tree,
/// such as fairness constraint actions that are not simple operator names.
///
/// Returns `None` if the node cannot be lowered to an expression.
pub fn lower_single_expr(file_id: FileId, node: &SyntaxNode) -> Option<Expr> {
    let mut ctx = LowerCtx::new(file_id);
    lower_expr(&mut ctx, node)
}

pub(super) fn collect_idents(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<Spanned<String>> {
    let mut idents = Vec::new();

    // Check direct tokens
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::Ident {
                let span = ctx.token_span(&token);
                idents.push(Spanned::new(token.text().to_string(), span));
            }
        }
    }

    // Also check NameList children
    for child in node.children() {
        if child.kind() == SyntaxKind::NameList {
            for tok in child.children_with_tokens() {
                if let rowan::NodeOrToken::Token(token) = tok {
                    if token.kind() == SyntaxKind::Ident {
                        let span = ctx.token_span(&token);
                        idents.push(Spanned::new(token.text().to_string(), span));
                    }
                }
            }
        }
    }

    idents
}
