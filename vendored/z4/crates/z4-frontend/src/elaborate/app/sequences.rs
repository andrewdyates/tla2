// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use z4_core::{Sort, Symbol, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    pub(super) fn try_elaborate_sequence_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "seq.unit" => {
                self.expect_exact_arity("seq.unit", arg_ids, 1)?;
                let elem_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.unit"),
                    arg_ids.to_vec(),
                    Sort::seq(elem_sort),
                )))
            }
            "seq.++" => {
                self.expect_min_arity("seq.++", arg_ids, 2)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.++"),
                    arg_ids.to_vec(),
                    seq_sort,
                )))
            }
            "seq.len" => {
                self.expect_exact_arity("seq.len", arg_ids, 1)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.len"),
                    arg_ids.to_vec(),
                    Sort::Int,
                )))
            }
            "seq.nth" => {
                self.expect_exact_arity("seq.nth", arg_ids, 2)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                let elem_sort = seq_sort.seq_element().cloned().unwrap_or(Sort::Int);
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.nth"),
                    arg_ids.to_vec(),
                    elem_sort,
                )))
            }
            "seq.at" => {
                self.expect_exact_arity("seq.at", arg_ids, 2)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                let one = self.terms.mk_int(BigInt::from(1));
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.extract"),
                    vec![arg_ids[0], arg_ids[1], one],
                    seq_sort,
                )))
            }
            "seq.extract" => {
                self.expect_exact_arity("seq.extract", arg_ids, 3)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.extract"),
                    arg_ids.to_vec(),
                    seq_sort,
                )))
            }
            "seq.contains" | "seq.prefixof" | "seq.suffixof" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "seq.indexof" => {
                self.expect_exact_arity("seq.indexof", arg_ids, 3)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.indexof"),
                    arg_ids.to_vec(),
                    Sort::Int,
                )))
            }
            "seq.last_indexof" => {
                self.expect_exact_arity("seq.last_indexof", arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.last_indexof"),
                    arg_ids.to_vec(),
                    Sort::Int,
                )))
            }
            "seq.replace" | "seq.replace_all" => {
                self.expect_exact_arity(name, arg_ids, 3)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    seq_sort,
                )))
            }
            "seq.to.re" | "seq.to_re" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if !arg_sort.is_seq() {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Seq".into(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.to_re"),
                    arg_ids.to_vec(),
                    Sort::RegLan,
                )))
            }
            "seq.in.re" | "seq.in_re" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                let arg0_sort = self.terms.sort(arg_ids[0]).clone();
                if !arg0_sort.is_seq() {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Seq".into(),
                        actual: arg0_sort.to_string(),
                    });
                }
                self.expect_arg_sort(arg_ids[1], &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.in_re"),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "seq.map" => {
                self.expect_exact_arity("seq.map", arg_ids, 2)?;
                let f_sort = self.terms.sort(arg_ids[0]).clone();
                let result_elem = f_sort.array_element().cloned().unwrap_or(Sort::Int);
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.map"),
                    arg_ids.to_vec(),
                    Sort::seq(result_elem),
                )))
            }
            "seq.mapi" => {
                self.expect_exact_arity("seq.mapi", arg_ids, 3)?;
                let f_sort = self.terms.sort(arg_ids[0]).clone();
                let result_elem = f_sort.array_element().cloned().unwrap_or(Sort::Int);
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.mapi"),
                    arg_ids.to_vec(),
                    Sort::seq(result_elem),
                )))
            }
            "seq.foldl" => {
                self.expect_exact_arity("seq.foldl", arg_ids, 3)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.foldl"),
                    arg_ids.to_vec(),
                    self.terms.sort(arg_ids[1]).clone(),
                )))
            }
            "seq.foldli" => {
                self.expect_exact_arity("seq.foldli", arg_ids, 4)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.foldli"),
                    arg_ids.to_vec(),
                    self.terms.sort(arg_ids[2]).clone(),
                )))
            }
            "seq.empty" => {
                self.expect_exact_arity("seq.empty", arg_ids, 0)?;
                Err(ElaborateError::Unsupported(
                    "bare seq.empty requires sort annotation: use (as seq.empty (Seq T))".into(),
                ))
            }
            _ => Ok(None),
        }
    }
}
