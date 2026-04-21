// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type inference for TLA+ expressions
//!
//! TLA+ is untyped, but for code generation we need to infer Rust types.
//! This module provides a simple type inference system that:
//! - Infers types from expression structure (literals, operators)
//! - Propagates type constraints through the expression tree
//! - Reports errors when types cannot be determined or are inconsistent

mod infer_expr;
mod stdlib_types;
pub mod struct_registry;

use std::collections::HashMap;
use tla_core::ast::{Module, OperatorDef, Unit};

/// Inferred TLA+ types that map to Rust types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TlaType {
    /// Boolean type -> bool
    Bool,
    /// Integer type -> i64 (or BigInt for unbounded)
    Int,
    /// String type -> String
    String,
    /// Set type -> `TlaSet<T>`
    Set(Box<TlaType>),
    /// Sequence type -> `Vec<T>`
    Seq(Box<TlaType>),
    /// Tuple type -> (T1, T2, ...)
    Tuple(Vec<TlaType>),
    /// Record type -> struct
    Record(Vec<(String, TlaType)>),
    /// Function type -> TlaFunc<K, V>
    Func(Box<TlaType>, Box<TlaType>),
    /// Type variable (unresolved)
    Var(usize),
    /// Unknown type (inference failed)
    Unknown,
}

impl TlaType {
    /// Convert TLA+ type to Rust type string
    pub fn to_rust_type(&self) -> String {
        match self {
            TlaType::Bool => "bool".to_string(),
            TlaType::Int => "i64".to_string(),
            TlaType::String => "String".to_string(),
            TlaType::Set(elem) => format!("TlaSet<{}>", elem.to_rust_type()),
            TlaType::Seq(elem) => format!("Vec<{}>", elem.to_rust_type()),
            TlaType::Tuple(elems) => {
                let types: Vec<_> = elems.iter().map(|t| t.to_rust_type()).collect();
                format!("({})", types.join(", "))
            }
            TlaType::Record(_fields) => {
                // Always use TlaRecord<Value> for uniform compatibility between
                // state vars, helpers, and invariants.
                "TlaRecord<Value>".to_string()
            }
            TlaType::Func(key, val) => {
                format!("TlaFunc<{}, {}>", key.to_rust_type(), val.to_rust_type())
            }
            TlaType::Var(id) => format!("T{}", id),
            TlaType::Unknown => "Value".to_string(),
        }
    }

    /// Convert TLA+ type to Rust type string, using struct names from a
    /// [`StructRegistry`] for records with known fields.
    ///
    /// Falls back to `to_rust_type()` for records not in the registry.
    pub fn to_rust_type_with_structs(&self, registry: &struct_registry::StructRegistry) -> String {
        match self {
            TlaType::Record(fields) if !fields.is_empty() => {
                if let Some(gs) = registry.lookup_record(fields) {
                    gs.name.clone()
                } else {
                    self.to_rust_type()
                }
            }
            TlaType::Set(inner) => {
                format!("TlaSet<{}>", inner.to_rust_type_with_structs(registry))
            }
            TlaType::Seq(inner) => {
                format!("Vec<{}>", inner.to_rust_type_with_structs(registry))
            }
            TlaType::Func(k, v) => {
                format!(
                    "TlaFunc<{}, {}>",
                    k.to_rust_type_with_structs(registry),
                    v.to_rust_type_with_structs(registry)
                )
            }
            TlaType::Tuple(elems) => {
                let types: Vec<_> = elems
                    .iter()
                    .map(|t| t.to_rust_type_with_structs(registry))
                    .collect();
                format!("({})", types.join(", "))
            }
            _ => self.to_rust_type(),
        }
    }

    /// Check if this is a record type with statically-known, fully-resolved fields.
    pub fn is_known_record(&self) -> bool {
        matches!(self, TlaType::Record(fields) if !fields.is_empty() && fields.iter().all(|(_, t)| t.is_resolved()))
    }

    /// If this is a `Record` variant, return the fields. Otherwise `None`.
    pub fn as_record_fields(&self) -> Option<&[(String, TlaType)]> {
        match self {
            TlaType::Record(fields) => Some(fields),
            _ => None,
        }
    }

    /// Check if type is fully resolved (no type variables)
    pub fn is_resolved(&self) -> bool {
        match self {
            TlaType::Var(_) | TlaType::Unknown => false,
            TlaType::Set(t) | TlaType::Seq(t) => t.is_resolved(),
            TlaType::Tuple(ts) => ts.iter().all(|t| t.is_resolved()),
            TlaType::Record(fs) => fs.iter().all(|(_, t)| t.is_resolved()),
            TlaType::Func(k, v) => k.is_resolved() && v.is_resolved(),
            _ => true,
        }
    }
}

/// Type inference errors
#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeInferError {
    /// Type mismatch between expected and actual
    #[error("type mismatch in {context}: expected {expected:?}, got {actual:?}")]
    TypeMismatch {
        expected: TlaType,
        actual: TlaType,
        context: String,
    },
    /// Unknown identifier
    #[error("unknown identifier: {0}")]
    UnknownIdent(String),
    /// Cannot infer type for expression
    #[error("cannot infer type: {0}")]
    CannotInfer(String),
    /// Unsupported construct for code generation
    #[error("unsupported for codegen: {0}")]
    Unsupported(String),
}

/// Type inference context
pub struct TypeContext {
    /// Variable name to type mapping
    vars: HashMap<String, TlaType>,
    /// Operator definitions
    ops: HashMap<String, TlaType>,
    /// Inferred parameter types for each operator definition
    op_param_types: HashMap<String, Vec<TlaType>>,
    /// Next type variable id
    next_var: usize,
    /// Collected errors
    errors: Vec<TypeInferError>,
}

impl TypeContext {
    /// Create a new type context
    pub fn new() -> Self {
        TypeContext {
            vars: HashMap::new(),
            ops: HashMap::new(),
            op_param_types: HashMap::new(),
            next_var: 0,
            errors: Vec::new(),
        }
    }

    /// Create a fresh type variable
    pub fn fresh_var(&mut self) -> TlaType {
        let id = self.next_var;
        self.next_var += 1;
        TlaType::Var(id)
    }

    /// Add a variable binding
    pub fn bind_var(&mut self, name: &str, ty: TlaType) {
        self.vars.insert(name.to_string(), ty);
    }

    /// Look up a variable type
    pub fn lookup_var(&self, name: &str) -> Option<&TlaType> {
        self.vars.get(name)
    }

    /// Look up inferred operator result types.
    pub fn op_types(&self) -> &HashMap<String, TlaType> {
        &self.ops
    }

    /// Look up inferred operator parameter types.
    pub fn op_param_types(&self) -> &HashMap<String, Vec<TlaType>> {
        &self.op_param_types
    }

    /// Record an error
    pub fn error(&mut self, err: TypeInferError) {
        self.errors.push(err);
    }

    /// Take collected errors
    pub fn take_errors(&mut self) -> Vec<TypeInferError> {
        std::mem::take(&mut self.errors)
    }

    /// Infer types for a module
    pub fn infer_module(&mut self, module: &Module) -> HashMap<String, TlaType> {
        // First pass: collect variable declarations
        for unit in &module.units {
            if let Unit::Variable(vars) = &unit.node {
                for var in vars {
                    // Initially unknown, will be inferred from Init
                    let fresh = self.fresh_var();
                    self.bind_var(&var.node, fresh);
                }
            }
        }

        // Second pass: pre-register stdlib operators based on EXTENDS
        self.register_stdlib_operators(&module.extends);

        // Third pass: pre-register operator names (supports forward references)
        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if !self.ops.contains_key(&op.name.node) {
                    let fresh = self.fresh_var();
                    self.ops.insert(op.name.node.clone(), fresh);
                }
            }
        }

        // Fourth pass: infer from operator definitions
        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                self.infer_operator(op);
            }
        }

        // Return variable types
        self.vars.clone()
    }

    /// Infer type for an operator definition
    fn infer_operator(&mut self, op: &OperatorDef) {
        if matches!(&op.body.node, tla_core::ast::Expr::InstanceExpr(..)) {
            if !self.ops.contains_key(&op.name.node) {
                let fresh = self.fresh_var();
                self.ops.insert(op.name.node.clone(), fresh);
            }
            return;
        }

        // Add parameters to scope
        let mut saved_bindings = Vec::with_capacity(op.params.len());
        for param in &op.params {
            let fresh = self.fresh_var();
            saved_bindings.push(self.vars.insert(param.name.node.clone(), fresh));
        }

        // Infer body type
        let body_type = self.infer_expr(&op.body);

        let param_types = op
            .params
            .iter()
            .map(|param| {
                self.vars
                    .get(&param.name.node)
                    .cloned()
                    .unwrap_or(TlaType::Unknown)
            })
            .collect();
        self.op_param_types
            .insert(op.name.node.clone(), param_types);

        for (param, saved) in op.params.iter().zip(saved_bindings) {
            match saved {
                Some(prev) => {
                    self.vars.insert(param.name.node.clone(), prev);
                }
                None => {
                    self.vars.remove(&param.name.node);
                }
            }
        }

        // Store operator type
        self.ops.insert(op.name.node.clone(), body_type);
    }
}

impl Default for TypeContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::Expr;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_type_to_rust() {
        assert_eq!(TlaType::Bool.to_rust_type(), "bool");
        assert_eq!(TlaType::Int.to_rust_type(), "i64");
        assert_eq!(
            TlaType::Set(Box::new(TlaType::Int)).to_rust_type(),
            "TlaSet<i64>"
        );
        assert_eq!(
            TlaType::Func(Box::new(TlaType::Int), Box::new(TlaType::Bool)).to_rust_type(),
            "TlaFunc<i64, bool>"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_literals() {
        let mut ctx = TypeContext::new();

        use tla_core::span::{FileId, Span, Spanned};
        let span = Span::new(FileId(0), 0, 0);

        let bool_expr = Spanned::new(Expr::Bool(true), span);
        assert_eq!(ctx.infer_expr(&bool_expr), TlaType::Bool);

        let int_expr = Spanned::new(Expr::Int(42.into()), span);
        assert_eq!(ctx.infer_expr(&int_expr), TlaType::Int);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_set() {
        let mut ctx = TypeContext::new();

        use tla_core::span::{FileId, Span, Spanned};
        let span = Span::new(FileId(0), 0, 0);

        // {1, 2, 3}
        let set_expr = Spanned::new(
            Expr::SetEnum(vec![
                Spanned::new(Expr::Int(1.into()), span),
                Spanned::new(Expr::Int(2.into()), span),
            ]),
            span,
        );
        assert_eq!(
            ctx.infer_expr(&set_expr),
            TlaType::Set(Box::new(TlaType::Int))
        );
    }
}
