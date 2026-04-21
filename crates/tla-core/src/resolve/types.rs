// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for name resolution: options, symbol kinds, scopes.

use crate::span::Span;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Copy)]
pub struct ResolveOptions {
    /// Resolve proof bodies (THEOREM proofs).
    ///
    /// TLC does not semantically validate TLAPS proof scripts during model checking, and many
    /// tlaplus-examples specs include TLAPS proof language constructs that we don't yet fully
    /// lower/resolve. For model checking, callers should typically disable proof resolution.
    pub resolve_proofs: bool,
}

impl ResolveOptions {
    pub fn model_checking() -> Self {
        Self {
            resolve_proofs: false,
        }
    }
}

impl Default for ResolveOptions {
    fn default() -> Self {
        Self {
            resolve_proofs: true,
        }
    }
}

/// The kind of symbol in TLA+
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    /// State variable (VARIABLE declaration)
    Variable,
    /// Constant (CONSTANT declaration)
    Constant,
    /// Operator definition
    Operator,
    /// Bound variable (from quantifier, function def, set comprehension)
    BoundVar,
    /// Higher-order operator parameter
    OpParam,
    /// Module name (from EXTENDS or INSTANCE)
    Module,
}

/// A resolved symbol with metadata
#[derive(Debug, Clone)]
pub struct Symbol {
    /// Name of the symbol
    pub name: String,
    /// Kind of symbol
    pub kind: SymbolKind,
    /// Span of the definition site
    pub def_span: Span,
    /// Arity for operators/constants (0 for non-operators)
    pub arity: usize,
    /// Whether the definition is LOCAL
    pub local: bool,
}

/// A scope level containing symbol bindings
#[derive(Debug, Clone)]
pub(crate) struct Scope {
    /// Symbols defined in this scope
    pub(crate) symbols: HashMap<String, Symbol>,
    /// Names declared via forward declarations (e.g. `RECURSIVE`).
    ///
    /// These may later be defined without triggering a duplicate-definition error.
    pub(crate) forward_decls: HashSet<String>,
    /// Kind of scope (for error messages and diagnostics)
    pub(crate) _kind: ScopeKind,
}

/// The kind of scope
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScopeKind {
    /// Top-level module scope
    Module,
    /// LET...IN expression
    Let,
    /// Quantifier (\A, \E, CHOOSE)
    Quantifier,
    /// Function definition [x \in S |-> ...]
    Function,
    /// Set builder {e : x \in S}
    SetBuilder,
    /// Set filter {x \in S : P}
    SetFilter,
    /// Lambda expression
    Lambda,
    /// EXCEPT update value scope (for `@`)
    Except,
    /// Proof step (TAKE, PICK, etc.)
    Proof,
}
