// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use hashbrown::HashMap;

use crate::command::{Command, Term as ParsedTerm};
use z4_core::{Sort, TermId};

use super::{
    CommandResult, Context, ElaborateError, Objective, ObjectiveDirection, OptionValue, Result,
    ScopeFrame, SymbolInfo,
};

impl Context {
    /// Add an assertion
    pub(crate) fn assert(&mut self, term: &ParsedTerm) -> Result<()> {
        let id = self.elaborate_term(term, &HashMap::new())?;
        self.assertions.push(id);
        self.assertions_parsed.push(term.clone());
        Ok(())
    }

    /// Push a scope
    pub(crate) fn push(&mut self) {
        self.scopes.push(ScopeFrame {
            symbols: Vec::new(),
            assertion_count: self.assertions.len(),
            objective_count: self.objectives.len(),
            named_terms: Vec::new(),
            datatypes: Vec::new(),
            constructors: Vec::new(),
            sort_defs: Vec::new(),
        });
    }

    /// Pop a scope. Returns `true` on success, `false` on underflow (no scopes).
    pub(crate) fn pop(&mut self) -> bool {
        if let Some(frame) = self.scopes.pop() {
            // Remove symbols defined in this scope
            for name in frame.symbols {
                self.symbols.remove(&name);
                self.overloaded_symbols.remove(&name);
            }
            // Remove assertions from this scope
            self.assertions.truncate(frame.assertion_count);
            self.assertions_parsed.truncate(frame.assertion_count);
            // Remove objectives from this scope
            self.objectives.truncate(frame.objective_count);
            // Remove named terms defined in this scope
            for name in frame.named_terms {
                self.named_terms.remove(&name);
            }
            // Remove datatypes defined in this scope
            for name in frame.datatypes {
                self.datatypes.remove(&name);
            }
            // Remove constructors defined in this scope
            for name in frame.constructors {
                self.constructors.remove(&name);
                self.ctor_selectors.remove(&name);
                self.ctor_selector_info.remove(&name);
            }
            // Remove sort definitions defined in this scope
            for name in frame.sort_defs {
                self.sort_defs.remove(&name);
            }
            true
        } else {
            false
        }
    }

    /// Iterate over all declared symbols
    pub fn symbol_iter(&self) -> impl Iterator<Item = (&String, &SymbolInfo)> {
        self.symbols.iter()
    }

    /// Register a symbol directly (for native API use)
    ///
    /// This is used by the native Rust API to register constants created
    /// via `mk_var` so they appear in models.
    pub fn register_symbol(&mut self, name: String, term: TermId, sort: Sort) {
        self.symbols.insert(
            name.clone(),
            SymbolInfo {
                term: Some(term),
                sort,
                arg_sorts: vec![],
            },
        );
        if let Some(frame) = self.scopes.last_mut() {
            frame.symbols.push(name);
        }
    }

    pub(super) fn register_overloadable_symbol(&mut self, name: String, info: SymbolInfo) {
        if let Some(existing) = self.symbols.get(&name).cloned() {
            self.overloaded_symbols
                .entry(name.clone())
                .or_insert_with(|| vec![existing])
                .push(info.clone());
        } else if let Some(overloads) = self.overloaded_symbols.get_mut(&name) {
            overloads.push(info.clone());
        }

        self.symbols.insert(name.clone(), info);
        if let Some(frame) = self.scopes.last_mut() {
            frame.symbols.push(name);
        }
    }

    pub(super) fn resolve_overloaded_symbol(
        &self,
        name: &str,
        args: &[TermId],
    ) -> Result<Option<SymbolInfo>> {
        let Some(candidates) = self.overloaded_symbols.get(name) else {
            return Ok(None);
        };

        let mut matches = candidates.iter().filter(|info| {
            info.arg_sorts.len() == args.len()
                && info
                    .arg_sorts
                    .iter()
                    .zip(args.iter())
                    .all(|(expected, arg)| expected == self.terms.sort(*arg))
        });

        let Some(first) = matches.next().cloned() else {
            return Ok(None);
        };

        if matches.next().is_some() {
            return Err(ElaborateError::Unsupported(format!(
                "ambiguous overloaded symbol '{name}'"
            )));
        }

        Ok(Some(first))
    }

    /// Process a command
    pub fn process_command(&mut self, cmd: &Command) -> Result<Option<CommandResult>> {
        match cmd {
            Command::SetLogic(logic) => {
                self.logic = Some(logic.clone());
                Ok(None)
            }
            Command::DeclareConst(name, sort) => {
                self.declare_const(name, sort)?;
                Ok(None)
            }
            Command::DeclareFun(name, arg_sorts, ret_sort) => {
                self.declare_fun(name, arg_sorts, ret_sort)?;
                Ok(None)
            }
            Command::DefineFun(name, params, ret_sort, body) => {
                self.define_fun(name, params, ret_sort, body)?;
                Ok(None)
            }
            Command::DefineFunRec(name, params, ret_sort, body) => {
                // For recursive functions, register the symbol first so the body can reference it
                self.define_fun_rec(name, params, ret_sort, body)?;
                Ok(None)
            }
            Command::DefineFunsRec(declarations, bodies) => {
                // For mutually recursive functions, register all symbols first
                self.define_funs_rec(declarations, bodies)?;
                Ok(None)
            }
            Command::Assert(term) => {
                self.assert(term)?;
                Ok(None)
            }
            Command::Maximize(term) => {
                let id = self.elaborate_term(term, &HashMap::new())?;
                self.objectives.push(Objective {
                    direction: ObjectiveDirection::Maximize,
                    term: id,
                });
                Ok(None)
            }
            Command::Minimize(term) => {
                let id = self.elaborate_term(term, &HashMap::new())?;
                self.objectives.push(Objective {
                    direction: ObjectiveDirection::Minimize,
                    term: id,
                });
                Ok(None)
            }
            Command::Push(n) => {
                for _ in 0..*n {
                    self.push();
                }
                Ok(None)
            }
            Command::Pop(n) => {
                for _ in 0..*n {
                    if !self.pop() {
                        return Err(ElaborateError::ScopeUnderflow);
                    }
                }
                Ok(None)
            }
            Command::CheckSat => Ok(Some(CommandResult::CheckSat)),
            Command::CheckSatAssuming(terms) => {
                // Elaborate each assumption term to get its TermId
                let term_ids: Vec<TermId> = terms
                    .iter()
                    .map(|t| self.elaborate_term(t, &HashMap::new()))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Some(CommandResult::CheckSatAssuming(term_ids)))
            }
            Command::GetModel => Ok(Some(CommandResult::GetModel)),
            Command::GetObjectives => Ok(Some(CommandResult::GetObjectives)),
            Command::GetValue(terms) => {
                // Elaborate each term to get its TermId
                let term_ids: Vec<TermId> = terms
                    .iter()
                    .map(|t| self.elaborate_term(t, &HashMap::new()))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Some(CommandResult::GetValue(term_ids)))
            }
            Command::GetInfo(keyword) => Ok(Some(CommandResult::GetInfo(keyword.clone()))),
            Command::GetOption(keyword) => Ok(Some(CommandResult::GetOption(keyword.clone()))),
            Command::GetAssertions => Ok(Some(CommandResult::GetAssertions)),
            Command::SetOption(keyword, value) => {
                self.set_option(keyword, value);
                Ok(None)
            }
            Command::Exit => Ok(Some(CommandResult::Exit)),
            Command::Reset => {
                *self = Self::new();
                Ok(None)
            }
            Command::ResetAssertions => {
                self.assertions.clear();
                self.assertions_parsed.clear();
                self.objectives.clear();
                self.scopes.clear();
                Ok(None)
            }
            // Declare/define sort are stored but don't produce output
            Command::DeclareSort(name, _arity) => {
                // Store as uninterpreted sort
                self.sort_defs
                    .insert(name.clone(), Sort::Uninterpreted(name.clone()));
                Ok(None)
            }
            Command::DefineSort(name, _params, sort) => {
                let elaborated = self.elaborate_sort(sort)?;
                self.sort_defs.insert(name.clone(), elaborated);
                Ok(None)
            }
            Command::DeclareDatatype(name, datatype_dec) => {
                self.declare_datatype(name, datatype_dec)?;
                Ok(None)
            }
            Command::DeclareDatatypes(sort_decs, datatype_decs) => {
                self.declare_datatypes(sort_decs, datatype_decs)?;
                Ok(None)
            }
            // SetInfo is acknowledged but not required to produce output
            Command::SetInfo(_, _) => Ok(None),
            // Echo returns the message to be printed (handled by executor)
            Command::Echo(msg) => Ok(Some(CommandResult::Echo(msg.clone()))),
            Command::GetAssignment => Ok(Some(CommandResult::GetAssignment)),
            Command::GetUnsatCore => Ok(Some(CommandResult::GetUnsatCore)),
            Command::GetUnsatAssumptions => Ok(Some(CommandResult::GetUnsatAssumptions)),
            Command::GetProof => Ok(Some(CommandResult::GetProof)),
            Command::Simplify(term) => {
                let term_id = self.elaborate_term(term, &HashMap::new())?;
                Ok(Some(CommandResult::Simplify(term_id)))
            }
        }
    }

    /// Set a solver option
    fn set_option(&mut self, keyword: &str, value: &crate::sexp::SExpr) {
        use crate::sexp::SExpr;
        let key = keyword.trim_start_matches(':').to_string();
        let opt_value = match value {
            SExpr::True => OptionValue::Bool(true),
            SExpr::False => OptionValue::Bool(false),
            SExpr::Numeral(n) => OptionValue::Numeral(n.clone()),
            SExpr::String(s) | SExpr::Symbol(s) => OptionValue::String(s.clone()),
            _ => return, // Ignore unsupported value types
        };
        self.options.insert(key, opt_value);
    }

    /// Get an option value
    pub fn get_option(&self, keyword: &str) -> Option<&OptionValue> {
        let key = keyword.trim_start_matches(':');
        self.options.get(key)
    }

    /// Iterate over named terms (for get-assignment)
    pub fn named_terms_iter(&self) -> impl Iterator<Item = (&str, TermId)> {
        self.named_terms.iter().map(|(k, v)| (k.as_str(), *v))
    }

    /// Register a named term for get-assignment and get-unsat-core.
    ///
    /// Tracks in the current scope so the name is removed on pop().
    pub fn register_named_term(&mut self, name: String, term_id: TermId) {
        self.named_terms.insert(name.clone(), term_id);
        if let Some(scope) = self.scopes.last_mut() {
            scope.named_terms.push(name);
        }
    }

    /// Iterate over declared datatypes: (dt_name, constructor_names)
    ///
    /// Returns an iterator over all datatype definitions with their constructor names.
    /// Used by theory solvers (e.g., DtSolver) to register datatype information.
    pub fn datatype_iter(&self) -> impl Iterator<Item = (&str, &[String])> {
        self.datatypes
            .iter()
            .map(|(name, ctors)| (name.as_str(), ctors.as_slice()))
    }

    /// Check if a symbol name is a datatype constructor
    ///
    /// Returns Some((dt_name, ctor_name)) if the symbol is a constructor,
    /// None otherwise. Used by theory solvers to identify constructor applications.
    pub fn is_constructor(&self, name: &str) -> Option<(String, String)> {
        self.constructors.get(name).cloned()
    }

    /// Get the selector names for a constructor symbol.
    ///
    /// Returns selector names in the order they appear in the datatype declaration.
    /// Used by DT theory solver to generate selector axioms.
    pub fn constructor_selectors(&self, ctor_name: &str) -> Option<&[String]> {
        self.ctor_selectors.get(ctor_name).map(Vec::as_slice)
    }

    /// Get selector metadata for a constructor in declaration order.
    pub fn constructor_selector_info(&self, ctor_name: &str) -> Option<&[(String, Sort)]> {
        self.ctor_selector_info.get(ctor_name).map(Vec::as_slice)
    }

    /// Iterate over all constructor -> selector mappings.
    ///
    /// Returns (constructor_name, selector_names) pairs. Used by the DT theory
    /// solver to identify selector applications when propagating axioms through
    /// variable indirection (#1740).
    pub fn ctor_selectors_iter(&self) -> impl Iterator<Item = (&String, &Vec<String>)> {
        self.ctor_selectors.iter()
    }

    /// Get the return sort of a declared symbol.
    ///
    /// Returns the return sort for function/constructor/selector symbols.
    /// Used by DT theory solver to build selector application terms.
    pub fn symbol_sort(&self, name: &str) -> Option<&Sort> {
        self.symbols.get(name).map(|info| &info.sort)
    }

    /// Get full symbol information for a declared symbol.
    ///
    /// Returns the [`SymbolInfo`] for a symbol, including its return sort
    /// and argument sorts. Used by the API layer to validate datatype
    /// constructor/selector/tester usage.
    pub fn symbol_info(&self, name: &str) -> Option<&SymbolInfo> {
        self.symbols.get(name)
    }
}
