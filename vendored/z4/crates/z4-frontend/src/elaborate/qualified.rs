// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use hashbrown::HashMap;

use crate::command::{self, Term as ParsedTerm};
use z4_core::{Symbol, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    /// Elaborate a qualified application `(as <id> <sort>)` with args.
    ///
    /// Handles structured qualified identifiers parsed by `command.rs`,
    /// avoiding the string-prefix matching that `elaborate_app` uses for
    /// legacy `App` nodes with stringified qualified names.
    pub(super) fn elaborate_qualified_app(
        &mut self,
        name: &str,
        parsed_sort: &command::Sort,
        args: &[ParsedTerm],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        let sort = self.elaborate_sort(parsed_sort)?;
        let arg_ids: Vec<TermId> = args
            .iter()
            .map(|a| self.elaborate_term(a, env))
            .collect::<Result<Vec<_>>>()?;

        match name {
            "seq.empty" => Ok(self.terms.mk_app(Symbol::named("seq.empty"), vec![], sort)),
            "const" => {
                // Constant array: ((as const (Array T1 T2)) value)
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "constant array requires exactly 1 argument".to_string(),
                    ));
                }
                let index_sort = sort.array_index().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "expected Array sort in const, got: {sort:?}"
                    ))
                })?;
                Ok(self.terms.mk_const_array(index_sort, arg_ids[0]))
            }
            _ => {
                // Generic qualified identifier: use sort as return type
                Ok(self.terms.mk_app(Symbol::named(name), arg_ids, sort))
            }
        }
    }
}
