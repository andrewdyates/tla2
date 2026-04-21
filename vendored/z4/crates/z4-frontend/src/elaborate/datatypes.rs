// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::command;
use z4_core::Sort;

use super::{is_reserved_symbol, Context, ElaborateError, Result, SymbolInfo};

impl Context {
    /// Declare a single datatype
    ///
    /// A datatype declaration creates:
    /// - A new uninterpreted sort
    /// - A constructor function for each constructor
    /// - A selector function for each selector
    /// - A tester function (is-Constructor) for each constructor
    pub(crate) fn declare_datatype(
        &mut self,
        name: &str,
        datatype_dec: &command::DatatypeDec,
    ) -> Result<()> {
        // Validate datatype name and all constructor/selector names
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        for ctor in &datatype_dec.constructors {
            if is_reserved_symbol(&ctor.name) {
                return Err(ElaborateError::ReservedSymbol(ctor.name.clone()));
            }
            for sel in &ctor.selectors {
                if is_reserved_symbol(&sel.name) {
                    return Err(ElaborateError::ReservedSymbol(sel.name.clone()));
                }
            }
        }

        // Register the sort as uninterpreted
        let sort = Sort::Uninterpreted(name.to_string());
        self.sort_defs.insert(name.to_string(), sort.clone());

        // Collect constructor names for datatype lookup
        let ctor_names: Vec<String> = datatype_dec
            .constructors
            .iter()
            .map(|c| c.name.clone())
            .collect();
        self.datatypes.insert(name.to_string(), ctor_names);

        // Track datatype and its sort in current scope for push/pop
        if let Some(frame) = self.scopes.last_mut() {
            frame.datatypes.push(name.to_string());
            frame.sort_defs.push(name.to_string());
        }

        // Register constructors, selectors, and testers
        for ctor in &datatype_dec.constructors {
            // Track constructor -> selectors mapping (positional)
            self.ctor_selectors.insert(
                ctor.name.clone(),
                ctor.selectors.iter().map(|s| s.name.clone()).collect(),
            );
            // Track constructor -> datatype mapping
            self.constructors
                .insert(ctor.name.clone(), (name.to_string(), ctor.name.clone()));
            // Track constructor in current scope for push/pop
            if let Some(frame) = self.scopes.last_mut() {
                frame.constructors.push(ctor.name.clone());
            }
            // Elaborate selector sorts
            let selector_sorts: Vec<Sort> = ctor
                .selectors
                .iter()
                .map(|s| self.elaborate_sort(&s.sort))
                .collect::<Result<Vec<_>>>()?;
            self.ctor_selector_info.insert(
                ctor.name.clone(),
                ctor.selectors
                    .iter()
                    .zip(selector_sorts.iter())
                    .map(|(sel, sel_sort)| (sel.name.clone(), sel_sort.clone()))
                    .collect(),
            );

            // Constructor: (sel_sort1, ..., sel_sortN) -> DataType
            let ctor_term = if selector_sorts.is_empty() {
                Some(self.terms.mk_fresh_named_var(&ctor.name, sort.clone()))
            } else {
                None
            };
            self.register_overloadable_symbol(
                ctor.name.clone(),
                SymbolInfo {
                    term: ctor_term,
                    sort: sort.clone(),
                    arg_sorts: selector_sorts.clone(),
                },
            );

            // Selectors: DataType -> field_sort
            for (sel, sel_sort) in ctor.selectors.iter().zip(selector_sorts.iter()) {
                self.register_overloadable_symbol(
                    sel.name.clone(),
                    SymbolInfo {
                        term: None,
                        sort: sel_sort.clone(),
                        arg_sorts: vec![sort.clone()],
                    },
                );
            }

            // Tester: DataType -> Bool
            let tester_name = format!("is-{}", ctor.name);
            self.register_overloadable_symbol(
                tester_name.clone(),
                SymbolInfo {
                    term: None,
                    sort: Sort::Bool,
                    arg_sorts: vec![sort.clone()],
                },
            );
        }

        Ok(())
    }

    /// Declare multiple (possibly mutually recursive) datatypes
    ///
    /// For mutually recursive datatypes, all sort names are registered first
    /// so that constructor/selector sorts can reference each other.
    pub(crate) fn declare_datatypes(
        &mut self,
        sort_decs: &[command::SortDec],
        datatype_decs: &[command::DatatypeDec],
    ) -> Result<()> {
        // Validate all names before making any changes
        for sort_dec in sort_decs {
            if is_reserved_symbol(&sort_dec.name) {
                return Err(ElaborateError::ReservedSymbol(sort_dec.name.clone()));
            }
        }
        for datatype_dec in datatype_decs {
            for ctor in &datatype_dec.constructors {
                if is_reserved_symbol(&ctor.name) {
                    return Err(ElaborateError::ReservedSymbol(ctor.name.clone()));
                }
                for sel in &ctor.selectors {
                    if is_reserved_symbol(&sel.name) {
                        return Err(ElaborateError::ReservedSymbol(sel.name.clone()));
                    }
                }
            }
        }

        // First pass: register all sort names
        for sort_dec in sort_decs {
            if sort_dec.arity != 0 {
                return Err(ElaborateError::Unsupported(
                    "parametric datatypes are not yet supported".to_string(),
                ));
            }
            let sort = Sort::Uninterpreted(sort_dec.name.clone());
            self.sort_defs.insert(sort_dec.name.clone(), sort);
            // Track sort in current scope for push/pop
            if let Some(frame) = self.scopes.last_mut() {
                frame.sort_defs.push(sort_dec.name.clone());
            }
        }

        // Second pass: register constructors, selectors, and testers for each datatype
        for (sort_dec, datatype_dec) in sort_decs.iter().zip(datatype_decs.iter()) {
            let sort = Sort::Uninterpreted(sort_dec.name.clone());

            // Collect constructor names for datatype lookup
            let ctor_names: Vec<String> = datatype_dec
                .constructors
                .iter()
                .map(|c| c.name.clone())
                .collect();
            self.datatypes.insert(sort_dec.name.clone(), ctor_names);

            // Track datatype in current scope for push/pop
            if let Some(frame) = self.scopes.last_mut() {
                frame.datatypes.push(sort_dec.name.clone());
            }

            for ctor in &datatype_dec.constructors {
                // Track constructor -> selectors mapping (positional)
                self.ctor_selectors.insert(
                    ctor.name.clone(),
                    ctor.selectors.iter().map(|s| s.name.clone()).collect(),
                );
                // Track constructor -> datatype mapping
                self.constructors.insert(
                    ctor.name.clone(),
                    (sort_dec.name.clone(), ctor.name.clone()),
                );
                // Track constructor in current scope for push/pop
                if let Some(frame) = self.scopes.last_mut() {
                    frame.constructors.push(ctor.name.clone());
                }
                // Elaborate selector sorts
                let selector_sorts: Vec<Sort> = ctor
                    .selectors
                    .iter()
                    .map(|s| self.elaborate_sort(&s.sort))
                    .collect::<Result<Vec<_>>>()?;
                self.ctor_selector_info.insert(
                    ctor.name.clone(),
                    ctor.selectors
                        .iter()
                        .zip(selector_sorts.iter())
                        .map(|(sel, sel_sort)| (sel.name.clone(), sel_sort.clone()))
                        .collect(),
                );

                // Constructor: (sel_sort1, ..., sel_sortN) -> DataType
                let ctor_term = if selector_sorts.is_empty() {
                    Some(self.terms.mk_fresh_named_var(&ctor.name, sort.clone()))
                } else {
                    None
                };
                self.register_overloadable_symbol(
                    ctor.name.clone(),
                    SymbolInfo {
                        term: ctor_term,
                        sort: sort.clone(),
                        arg_sorts: selector_sorts.clone(),
                    },
                );

                // Selectors: DataType -> field_sort
                for (sel, sel_sort) in ctor.selectors.iter().zip(selector_sorts.iter()) {
                    self.register_overloadable_symbol(
                        sel.name.clone(),
                        SymbolInfo {
                            term: None,
                            sort: sel_sort.clone(),
                            arg_sorts: vec![sort.clone()],
                        },
                    );
                }

                // Tester: DataType -> Bool
                let tester_name = format!("is-{}", ctor.name);
                self.register_overloadable_symbol(
                    tester_name.clone(),
                    SymbolInfo {
                        term: None,
                        sort: Sort::Bool,
                        arg_sorts: vec![sort.clone()],
                    },
                );
            }
        }

        Ok(())
    }
}
