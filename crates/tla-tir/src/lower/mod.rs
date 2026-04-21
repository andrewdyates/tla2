// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod expr_kind;
mod lowerer;
mod lowerer_helpers;
mod resolve;
mod scope;

use crate::error::TirLowerError;
use crate::nodes::TirExpr;
use lowerer::Lowerer;
use scope::LoweringScope;
use std::collections::HashMap;
use tla_core::ast::{Expr, Module, OperatorDef, Substitution, Unit};
use tla_core::{intern_name, NameId, Spanned};

/// Module set available to TIR lowering for resolving INSTANCE/module
/// references into concrete operator bodies.
#[derive(Debug, Clone, Default)]
pub struct TirLoweringEnv<'a> {
    modules: HashMap<String, &'a Module>,
}

impl<'a> TirLoweringEnv<'a> {
    #[must_use]
    pub fn new(root: &'a Module) -> Self {
        let mut env = Self::default();
        env.add_module(root);
        env
    }

    pub fn add_module(&mut self, module: &'a Module) {
        self.modules.insert(module.name.node.clone(), module);
    }

    #[must_use]
    pub fn with_module(mut self, module: &'a Module) -> Self {
        self.add_module(module);
        self
    }

    fn module(&self, name: &str) -> Option<&'a Module> {
        self.modules.get(name).copied()
    }

    /// Public accessor for looking up a module by name.
    ///
    /// Used by `tla-codegen` to resolve INSTANCE module references when
    /// importing operators for TIR-based code generation.
    #[must_use]
    pub fn module_ref(&self, name: &str) -> Option<&'a Module> {
        self.module(name)
    }
}

/// A lowered TIR view of an AST module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TirModule {
    pub name: String,
    pub operators: Vec<TirOperator>,
}

/// A lowered operator body in TIR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TirOperator {
    pub name: String,
    pub name_id: NameId,
    /// Parameter names (empty for zero-arity operators).
    /// Carried through from AST `OperatorDef.params` for bytecode compilation.
    pub params: Vec<String>,
    pub is_recursive: bool,
    pub body: Spanned<TirExpr>,
}

/// Lower a single AST expression into the current supported TIR slice with a
/// caller-provided module environment for INSTANCE resolution.
pub fn lower_expr_with_env<'a>(
    env: &'a TirLoweringEnv<'a>,
    module: &'a Module,
    expr: &Spanned<Expr>,
) -> Result<Spanned<TirExpr>, TirLowerError> {
    Lowerer::new(env).lower_expr(&LoweringScope::root(module), expr)
}

/// Lower a single AST expression into the current supported TIR slice.
pub fn lower_expr(
    module: &Module,
    expr: &Spanned<Expr>,
) -> Result<Spanned<TirExpr>, TirLowerError> {
    let env = TirLoweringEnv::new(module);
    lower_expr_with_env(&env, module, expr)
}

/// Lower a single operator body into the current supported TIR slice with a
/// caller-provided module environment.
pub fn lower_operator_with_env<'a>(
    env: &'a TirLoweringEnv<'a>,
    module: &'a Module,
    def: &OperatorDef,
) -> Result<TirOperator, TirLowerError> {
    Ok(TirOperator {
        name: def.name.node.clone(),
        name_id: intern_name(&def.name.node),
        params: def.params.iter().map(|p| p.name.node.clone()).collect(),
        is_recursive: def.is_recursive,
        body: lower_expr_with_env(env, module, &def.body)?,
    })
}

/// Lower a single operator body into the current supported TIR slice.
pub fn lower_operator(module: &Module, def: &OperatorDef) -> Result<TirOperator, TirLowerError> {
    let env = TirLoweringEnv::new(module);
    lower_operator_with_env(&env, module, def)
}

/// Lower an operator body from an instanced module using substitution bindings
/// from the root module's INSTANCE declaration.
///
/// Creates a `LoweringScope` with:
/// - `instance_module` as the current module (sibling operator resolution)
/// - Substitution bindings from `substitutions` (name remapping)
/// - `root_module` as the origin scope (substitution RHS evaluation context)
///
/// Part of #3352: enables TIR evaluation for INSTANCE wrapper specs where
/// operators are defined in a dep module and imported via unnamed INSTANCE.
pub fn lower_operator_in_instance_scope<'a>(
    env: &'a TirLoweringEnv<'a>,
    root_module: &'a Module,
    instance_module: &'a Module,
    def: &OperatorDef,
    substitutions: &[Substitution],
) -> Result<TirOperator, TirLowerError> {
    let root_scope = LoweringScope::root(root_module);
    let instance_scope = root_scope.with_bindings_from(
        instance_module,
        &root_scope,
        substitutions
            .iter()
            .map(|sub| (sub.from.node.clone(), sub.to.clone())),
    );
    Ok(TirOperator {
        name: def.name.node.clone(),
        name_id: intern_name(&def.name.node),
        params: def.params.iter().map(|p| p.name.node.clone()).collect(),
        is_recursive: def.is_recursive,
        body: Lowerer::new(env).lower_expr(&instance_scope, &def.body)?,
    })
}

/// Strictly lower every executable operator body in a module into the current
/// supported TIR slice with a caller-provided module environment.
///
/// Top-level INSTANCE-definition operators (whose bodies are `InstanceExpr` or
/// `SubstIn`-wrapped `InstanceExpr`) are namespace carriers, not executable
/// expression bodies, and are silently skipped.
///
/// All other operators are lowered strictly: if any non-INSTANCE operator
/// contains an expression outside the supported TIR slice, the entire module
/// lowering fails with `TirLowerError`.
pub fn lower_module_with_env<'a>(
    env: &'a TirLoweringEnv<'a>,
    module: &'a Module,
) -> Result<TirModule, TirLowerError> {
    let operators = module
        .units
        .iter()
        .filter_map(|unit| match &unit.node {
            Unit::Operator(def) if !is_instance_expr(&def.body) => {
                Some(lower_operator_with_env(env, module, def))
            }
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(TirModule {
        name: module.name.node.clone(),
        operators,
    })
}

/// Strictly lower every executable operator body in a module into the current
/// supported TIR slice. See [`lower_module_with_env`] for the strict contract.
pub fn lower_module(module: &Module) -> Result<TirModule, TirLowerError> {
    let env = TirLoweringEnv::new(module);
    lower_module_with_env(&env, module)
}

/// Lower a single operator body in permissive mode with a caller-provided
/// module environment.
///
/// Like [`lower_operator_with_env`], but allows parameterized stdlib builtins
/// (`Append`, `Len`, `Cardinality`, etc.) through as generic `TirExpr::Apply`
/// nodes. Used by the bytecode compilation path where these builtins are
/// handled by `CallBuiltin` opcodes, so rejecting them at TIR lowering is
/// unnecessary. Part of #3967.
pub fn lower_operator_with_env_permissive<'a>(
    env: &'a TirLoweringEnv<'a>,
    module: &'a Module,
    def: &OperatorDef,
) -> Result<TirOperator, TirLowerError> {
    Ok(TirOperator {
        name: def.name.node.clone(),
        name_id: intern_name(&def.name.node),
        params: def.params.iter().map(|p| p.name.node.clone()).collect(),
        is_recursive: def.is_recursive,
        body: lower_expr_with_env_permissive(env, module, &def.body)?,
    })
}

/// Lower a single AST expression in permissive mode.
///
/// Part of #3967: allows parameterized builtins through for bytecode compilation.
fn lower_expr_with_env_permissive<'a>(
    env: &'a TirLoweringEnv<'a>,
    module: &'a Module,
    expr: &Spanned<Expr>,
) -> Result<Spanned<TirExpr>, TirLowerError> {
    Lowerer::new_permissive(env).lower_expr(&LoweringScope::root(module), expr)
}

/// Permissive module lowering for code generation.
///
/// Like [`lower_module_with_env`], but allows parameterized stdlib builtins
/// (`Append`, `Len`, `Cardinality`, etc.) through as generic `TirExpr::Apply`
/// nodes. The codegen backend translates these directly to Rust stdlib method
/// calls, so they do not need TIR evaluator dispatch. Part of #3729.
pub fn lower_module_for_codegen<'a>(
    env: &'a TirLoweringEnv<'a>,
    module: &'a Module,
) -> Result<TirModule, TirLowerError> {
    let lowerer = Lowerer::new_permissive(env);
    let operators = module
        .units
        .iter()
        .filter_map(|unit| match &unit.node {
            Unit::Operator(def) if !is_instance_expr(&def.body) => {
                let scope = LoweringScope::root(module);
                Some(
                    lowerer
                        .lower_expr(&scope, &def.body)
                        .map(|body| TirOperator {
                            name: def.name.node.clone(),
                            name_id: intern_name(&def.name.node),
                            params: def.params.iter().map(|p| p.name.node.clone()).collect(),
                            is_recursive: def.is_recursive,
                            body,
                        }),
                )
            }
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(TirModule {
        name: module.name.node.clone(),
        operators,
    })
}

fn find_operator<'a>(module: &'a Module, name: &str) -> Option<&'a OperatorDef> {
    module.units.iter().find_map(|unit| match &unit.node {
        Unit::Operator(def) if def.name.node == name => Some(def),
        _ => None,
    })
}

fn is_instance_expr(expr: &Spanned<Expr>) -> bool {
    match &expr.node {
        Expr::InstanceExpr(_, _) => true,
        Expr::SubstIn(_, body) => is_instance_expr(body),
        _ => false,
    }
}
