// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::command::{self, Term as ParsedTerm};
use z4_core::Sort;

use super::{is_reserved_symbol, Context, ElaborateError, Result, SymbolInfo};

impl Context {
    /// Declare a constant
    pub(crate) fn declare_const(&mut self, name: &str, sort: &command::Sort) -> Result<()> {
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        let sort = self.elaborate_sort(sort)?;
        let term = self.terms.mk_fresh_named_var(name, sort.clone());
        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term: Some(term),
                sort,
                arg_sorts: vec![],
            },
        );
        if let Some(frame) = self.scopes.last_mut() {
            frame.symbols.push(name.to_string());
        }
        Ok(())
    }

    /// Declare a function
    pub(crate) fn declare_fun(
        &mut self,
        name: &str,
        arg_sorts: &[command::Sort],
        ret_sort: &command::Sort,
    ) -> Result<()> {
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        let arg_sorts: Vec<Sort> = arg_sorts
            .iter()
            .map(|s| self.elaborate_sort(s))
            .collect::<Result<Vec<_>>>()?;
        let ret_sort = self.elaborate_sort(ret_sort)?;

        // If no arguments, it's a constant
        let term = if arg_sorts.is_empty() {
            Some(self.terms.mk_fresh_named_var(name, ret_sort.clone()))
        } else {
            None
        };

        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term,
                sort: ret_sort,
                arg_sorts,
            },
        );
        if let Some(frame) = self.scopes.last_mut() {
            frame.symbols.push(name.to_string());
        }
        Ok(())
    }

    /// Define a function
    pub(crate) fn define_fun(
        &mut self,
        name: &str,
        params: &[(String, command::Sort)],
        ret_sort: &command::Sort,
        body: &ParsedTerm,
    ) -> Result<()> {
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        let params: Vec<(String, Sort)> = params
            .iter()
            .map(|(n, s)| Ok((n.clone(), self.elaborate_sort(s)?)))
            .collect::<Result<Vec<_>>>()?;
        let ret_sort = self.elaborate_sort(ret_sort)?;

        // Store the definition for expansion
        self.fun_defs
            .insert(name.to_string(), (params.clone(), body.clone()));

        // Also add to symbol table
        let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term: None,
                sort: ret_sort,
                arg_sorts,
            },
        );
        Ok(())
    }

    /// Define a recursive function
    ///
    /// For recursive functions, the function can reference itself in its body.
    /// We add to the symbol table first to enable self-reference during expansion.
    pub(crate) fn define_fun_rec(
        &mut self,
        name: &str,
        params: &[(String, command::Sort)],
        ret_sort: &command::Sort,
        body: &ParsedTerm,
    ) -> Result<()> {
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        let params: Vec<(String, Sort)> = params
            .iter()
            .map(|(n, s)| Ok((n.clone(), self.elaborate_sort(s)?)))
            .collect::<Result<Vec<_>>>()?;
        let ret_sort = self.elaborate_sort(ret_sort)?;

        // For recursive functions, add to symbol table first so body can reference the function
        let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term: None,
                sort: ret_sort,
                arg_sorts,
            },
        );

        // Store the definition for expansion
        self.fun_defs
            .insert(name.to_string(), (params, body.clone()));

        Ok(())
    }

    /// Define mutually recursive functions
    ///
    /// For mutually recursive functions, all function signatures are registered
    /// first so the bodies can reference each other.
    pub(crate) fn define_funs_rec(
        &mut self,
        declarations: &[command::FuncDeclaration],
        bodies: &[ParsedTerm],
    ) -> Result<()> {
        // Validate all function names first
        for (name, _params, _ret_sort) in declarations {
            if is_reserved_symbol(name) {
                return Err(ElaborateError::ReservedSymbol(name.clone()));
            }
        }

        // Elaborated declarations with internal Sort type
        type ElaboratedDecl = (String, Vec<(String, Sort)>, Sort);

        // First pass: register all function signatures in the symbol table
        let mut elaborated_decls: Vec<ElaboratedDecl> = Vec::new();

        for (name, params, ret_sort) in declarations {
            let params: Vec<(String, Sort)> = params
                .iter()
                .map(|(n, s)| Ok((n.clone(), self.elaborate_sort(s)?)))
                .collect::<Result<Vec<_>>>()?;
            let ret_sort = self.elaborate_sort(ret_sort)?;

            let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
            self.symbols.insert(
                name.clone(),
                SymbolInfo {
                    term: None,
                    sort: ret_sort.clone(),
                    arg_sorts,
                },
            );

            elaborated_decls.push((name.clone(), params, ret_sort));
        }

        // Second pass: store all function definitions
        for ((name, params, _ret_sort), body) in elaborated_decls.into_iter().zip(bodies.iter()) {
            self.fun_defs.insert(name, (params, body.clone()));
        }

        Ok(())
    }
}
