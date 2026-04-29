// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Resolution context: scope stack, symbol table, and error collection.

use super::error::{ResolveError, ResolveErrorKind};
use super::types::{Scope, ScopeKind, Symbol, SymbolKind};
use crate::span::Span;
use std::collections::{HashMap, HashSet};

/// Context for name resolution (crate-internal; external callers use `ResolveResult`)
#[derive(Debug)]
pub(crate) struct ResolveCtx {
    /// Stack of scopes (innermost last)
    scopes: Vec<Scope>,
    /// Collected errors
    pub(crate) errors: Vec<ResolveError>,
    /// All resolved symbols (for symbol table)
    pub(crate) all_symbols: Vec<Symbol>,
    /// Reference sites: (use_span, def_span)
    pub(crate) references: Vec<(Span, Span)>,
}

impl Default for ResolveCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl ResolveCtx {
    /// Create a new resolution context
    pub(crate) fn new() -> Self {
        Self {
            scopes: Vec::new(),
            errors: Vec::new(),
            all_symbols: Vec::new(),
            references: Vec::new(),
        }
    }

    /// Push a new scope
    pub(crate) fn push_scope(&mut self, kind: ScopeKind) {
        self.scopes.push(Scope {
            symbols: HashMap::new(),
            forward_decls: HashSet::new(),
            _kind: kind,
        });
    }

    /// Pop the current scope
    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// Define a symbol in the current scope
    pub(crate) fn define(
        &mut self,
        name: &str,
        kind: SymbolKind,
        span: Span,
        arity: usize,
        local: bool,
    ) {
        let symbol = Symbol {
            name: name.to_string(),
            kind,
            def_span: span,
            arity,
            local,
        };

        if let Some(scope) = self.scopes.last_mut() {
            // Check for duplicate in current scope
            if let Some(existing) = scope.symbols.get(name) {
                // Allow an actual definition to replace a forward declaration.
                let can_replace_forward_decl = scope.forward_decls.contains(name)
                    && existing.kind == SymbolKind::Operator
                    && kind == SymbolKind::Operator;

                if can_replace_forward_decl {
                    scope.symbols.insert(name.to_string(), symbol.clone());
                    scope.forward_decls.remove(name);
                } else {
                    self.errors.push(ResolveError {
                        kind: ResolveErrorKind::Duplicate {
                            name: name.to_string(),
                            first_def: existing.def_span,
                        },
                        span,
                    });
                }
            } else {
                scope.symbols.insert(name.to_string(), symbol.clone());
            }
        }

        self.all_symbols.push(symbol);
    }

    /// Define an imported operator in the current (module) scope.
    ///
    /// When bringing names into the unqualified scope via `EXTENDS` or standalone `INSTANCE`,
    /// TLC reports conflicts between operator definitions as warnings and continues.
    ///
    /// For model checking, we match this by keeping the first operator definition already in
    /// scope and ignoring later imported operator definitions with the same name.
    ///
    /// Conflicts with non-operator symbols remain errors.
    pub(crate) fn define_imported_operator(&mut self, name: &str, span: Span, arity: usize) {
        let symbol = Symbol {
            name: name.to_string(),
            kind: SymbolKind::Operator,
            def_span: span,
            arity,
            local: false,
        };

        if let Some(scope) = self.scopes.last_mut() {
            match scope.symbols.get(name) {
                None => {
                    scope.symbols.insert(name.to_string(), symbol.clone());
                }
                Some(existing) => {
                    if existing.kind != SymbolKind::Operator {
                        self.errors.push(ResolveError {
                            kind: ResolveErrorKind::Duplicate {
                                name: name.to_string(),
                                first_def: existing.def_span,
                            },
                            span,
                        });
                    } else if existing.arity != arity {
                        self.errors.push(ResolveError {
                            kind: ResolveErrorKind::ImportedOperatorArityConflict {
                                name: name.to_string(),
                                first_def: existing.def_span,
                                first_arity: existing.arity,
                                second_arity: arity,
                            },
                            span,
                        });
                    } else {
                        // Existing operator wins; ignore conflicting imported operator.
                        return;
                    }
                }
            }
        }

        self.all_symbols.push(symbol);
    }

    /// Look up a symbol by name, searching from innermost scope outward
    /// Returns the symbol's def_span if found
    fn lookup_def_span(&self, name: &str) -> Option<Span> {
        for scope in self.scopes.iter().rev() {
            if let Some(sym) = scope.symbols.get(name) {
                return Some(sym.def_span);
            }
        }
        None
    }

    /// Record a reference to a symbol
    pub(crate) fn reference(&mut self, name: &str, use_span: Span) -> bool {
        if let Some(def_span) = self.lookup_def_span(name) {
            self.references.push((use_span, def_span));
            true
        } else {
            self.errors.push(ResolveError {
                kind: ResolveErrorKind::Undefined {
                    name: name.to_string(),
                },
                span: use_span,
            });
            false
        }
    }
}
