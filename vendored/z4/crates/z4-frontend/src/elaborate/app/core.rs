// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::{Sort, Symbol, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    pub(super) fn try_elaborate_core_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "to_real" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_real requires 1 argument".to_string(),
                    ));
                }
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if arg_sort != Sort::Int {
                    return Err(ElaborateError::SortMismatch {
                        expected: Sort::Int.to_string(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("to_real"),
                    arg_ids.to_vec(),
                    Sort::Real,
                )))
            }
            "to_int" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_int requires 1 argument".to_string(),
                    ));
                }
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if arg_sort != Sort::Real {
                    return Err(ElaborateError::SortMismatch {
                        expected: Sort::Real.to_string(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_to_int(arg_ids[0])))
            }
            "is_int" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "is_int requires 1 argument".to_string(),
                    ));
                }
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if arg_sort != Sort::Real {
                    return Err(ElaborateError::SortMismatch {
                        expected: Sort::Real.to_string(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_is_int(arg_ids[0])))
            }
            "not" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "not requires 1 argument".to_string(),
                    ));
                }
                Ok(Some(self.terms.mk_not(arg_ids[0])))
            }
            "and" => Ok(Some(self.terms.mk_and(arg_ids.to_vec()))),
            "or" => Ok(Some(self.terms.mk_or(arg_ids.to_vec()))),
            "=>" | "implies" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "=> requires at least 2 arguments".to_string(),
                    ));
                }
                let (last, prefix) = arg_ids.split_last().ok_or_else(|| {
                    ElaborateError::InvalidConstant("=> requires at least 2 arguments".to_string())
                })?;
                let mut result = *last;
                for &arg in prefix.iter().rev() {
                    result = self.terms.mk_implies(arg, result);
                }
                Ok(Some(result))
            }
            "xor" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "xor requires at least 2 arguments".to_string(),
                    ));
                }
                let mut result = self.terms.mk_xor(arg_ids[0], arg_ids[1]);
                for &arg in &arg_ids[2..] {
                    result = self.terms.mk_xor(result, arg);
                }
                Ok(Some(result))
            }
            "ite" => {
                if arg_ids.len() != 3 {
                    return Err(ElaborateError::InvalidConstant(
                        "ite requires 3 arguments".to_string(),
                    ));
                }
                self.maybe_promote_numeric_args(&mut arg_ids[1..3])?;
                Ok(Some(self.terms.mk_ite(arg_ids[0], arg_ids[1], arg_ids[2])))
            }
            "=" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "= requires at least 2 arguments".to_string(),
                    ));
                }
                self.maybe_promote_numeric_args(arg_ids)?;
                if arg_ids.len() == 2 {
                    // #5115: coerce BV width mismatches (e.g., #x1 vs extract result)
                    self.maybe_coerce_bv_widths(arg_ids);
                    Ok(Some(self.terms.mk_eq(arg_ids[0], arg_ids[1])))
                } else {
                    let mut eqs = Vec::new();
                    for i in 0..arg_ids.len() - 1 {
                        let mut pair = [arg_ids[i], arg_ids[i + 1]];
                        self.maybe_coerce_bv_widths(&mut pair);
                        eqs.push(self.terms.mk_eq(pair[0], pair[1]));
                    }
                    Ok(Some(self.terms.mk_and(eqs)))
                }
            }
            "distinct" => {
                self.maybe_promote_numeric_args(arg_ids)?;
                // #5115: coerce BV width mismatches for distinct too
                if arg_ids.len() == 2 {
                    self.maybe_coerce_bv_widths(arg_ids);
                }
                Ok(Some(self.terms.mk_distinct(arg_ids.to_vec())))
            }
            "select" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "select requires 2 arguments".to_string(),
                    ));
                }
                Ok(Some(self.terms.mk_select(arg_ids[0], arg_ids[1])))
            }
            "store" => {
                if arg_ids.len() != 3 {
                    return Err(ElaborateError::InvalidConstant(
                        "store requires 3 arguments".to_string(),
                    ));
                }
                Ok(Some(
                    self.terms.mk_store(arg_ids[0], arg_ids[1], arg_ids[2]),
                ))
            }
            _ => Ok(None),
        }
    }
}
