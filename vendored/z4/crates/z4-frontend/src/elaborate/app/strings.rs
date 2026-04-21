// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use z4_core::{Constant, Sort, Symbol, TermData, TermId};

use super::{Context, Result};

impl Context {
    pub(super) fn try_elaborate_string_or_regex_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "str.++" => {
                self.expect_min_arity("str.++", arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                let all_const: Option<String> =
                    arg_ids.iter().try_fold(String::new(), |mut acc, &id| {
                        if let TermData::Const(Constant::String(s)) = self.terms.get(id) {
                            acc.push_str(s);
                            Some(acc)
                        } else {
                            None
                        }
                    });
                if let Some(result) = all_const {
                    return Ok(Some(self.terms.mk_string(result)));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.++"),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.len" => {
                self.expect_exact_arity("str.len", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                if let TermData::Const(Constant::String(s)) = self.terms.get(arg_ids[0]) {
                    return Ok(Some(self.terms.mk_int(BigInt::from(s.chars().count()))));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.len"),
                    arg_ids.to_vec(),
                    Sort::Int,
                )))
            }
            "str.at" => {
                self.expect_exact_arity("str.at", arg_ids, 2)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.at"),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.substr" => {
                self.expect_exact_arity("str.substr", arg_ids, 3)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::Int)?;
                self.expect_arg_sort(arg_ids[2], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.substr"),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.contains" | "str.prefixof" | "str.suffixof" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "str.indexof" => {
                self.expect_exact_arity("str.indexof", arg_ids, 3)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::String)?;
                self.expect_arg_sort(arg_ids[2], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.indexof"),
                    arg_ids.to_vec(),
                    Sort::Int,
                )))
            }
            "str.replace" => {
                self.expect_exact_arity("str.replace", arg_ids, 3)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.replace"),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.replace_all" => {
                self.expect_exact_arity("str.replace_all", arg_ids, 3)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                if let (
                    TermData::Const(Constant::String(s)),
                    TermData::Const(Constant::String(t)),
                    TermData::Const(Constant::String(u)),
                ) = (
                    self.terms.get(arg_ids[0]),
                    self.terms.get(arg_ids[1]),
                    self.terms.get(arg_ids[2]),
                ) {
                    let result = if t.is_empty() {
                        s.clone()
                    } else {
                        s.replace(t, u)
                    };
                    return Ok(Some(self.terms.mk_string(result)));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.replace_all"),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.replace_re" | "str.replace_re_all" => {
                self.expect_exact_arity(name, arg_ids, 3)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::RegLan)?;
                self.expect_arg_sort(arg_ids[2], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.to_int" | "str.to.int" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.to_int"),
                    arg_ids.to_vec(),
                    Sort::Int,
                )))
            }
            "str.from_int" | "int.to.str" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.from_int"),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.to_code" => {
                self.expect_exact_arity("str.to_code", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.to_code"),
                    arg_ids.to_vec(),
                    Sort::Int,
                )))
            }
            "str.from_code" => {
                self.expect_exact_arity("str.from_code", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.from_code"),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.to_lower" | "str.to_upper" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::String,
                )))
            }
            "str.<" | "str.<=" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "str.is_digit" => {
                self.expect_exact_arity("str.is_digit", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.is_digit"),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "str.to_re" | "str.to.re" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.to_re"),
                    arg_ids.to_vec(),
                    Sort::RegLan,
                )))
            }
            "str.in_re" | "str.in.re" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.in_re"),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "re.++" | "re.union" | "re.inter" => {
                self.expect_min_arity(name, arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::RegLan,
                )))
            }
            "re.*" | "re.+" | "re.opt" | "re.comp" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::RegLan,
                )))
            }
            "re.range" => {
                self.expect_exact_arity("re.range", arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("re.range"),
                    arg_ids.to_vec(),
                    Sort::RegLan,
                )))
            }
            "re.diff" => {
                self.expect_exact_arity("re.diff", arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("re.diff"),
                    arg_ids.to_vec(),
                    Sort::RegLan,
                )))
            }
            "re.none" | "re.all" | "re.allchar" => {
                self.expect_exact_arity(name, arg_ids, 0)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    vec![],
                    Sort::RegLan,
                )))
            }
            _ => Ok(None),
        }
    }
}
