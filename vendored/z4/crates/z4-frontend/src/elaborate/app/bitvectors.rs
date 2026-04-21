// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::TermId;

use super::{Context, ElaborateError, Result};

impl Context {
    pub(super) fn try_elaborate_bitvector_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor" | "concat" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 2 arguments"
                    )));
                }
                let mut result = match name {
                    "bvadd" => self.terms.mk_bvadd(vec![arg_ids[0], arg_ids[1]]),
                    "bvmul" => self.terms.mk_bvmul(vec![arg_ids[0], arg_ids[1]]),
                    "bvand" => self.terms.mk_bvand(vec![arg_ids[0], arg_ids[1]]),
                    "bvor" => self.terms.mk_bvor(vec![arg_ids[0], arg_ids[1]]),
                    "bvxor" => self.terms.mk_bvxor(vec![arg_ids[0], arg_ids[1]]),
                    _ => self.terms.mk_bvconcat(vec![arg_ids[0], arg_ids[1]]),
                };
                for &arg in &arg_ids[2..] {
                    result = match name {
                        "bvadd" => self.terms.mk_bvadd(vec![result, arg]),
                        "bvmul" => self.terms.mk_bvmul(vec![result, arg]),
                        "bvand" => self.terms.mk_bvand(vec![result, arg]),
                        "bvor" => self.terms.mk_bvor(vec![result, arg]),
                        "bvxor" => self.terms.mk_bvxor(vec![result, arg]),
                        _ => self.terms.mk_bvconcat(vec![result, arg]),
                    };
                }
                Ok(Some(result))
            }
            "bvsub" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr" | "bvashr" | "bvudiv"
            | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                Ok(Some(match name {
                    "bvsub" => self.terms.mk_bvsub(arg_ids.to_vec()),
                    "bvnand" => self.terms.mk_bvnand(arg_ids.to_vec()),
                    "bvnor" => self.terms.mk_bvnor(arg_ids.to_vec()),
                    "bvxnor" => self.terms.mk_bvxnor(arg_ids.to_vec()),
                    "bvshl" => self.terms.mk_bvshl(arg_ids.to_vec()),
                    "bvlshr" => self.terms.mk_bvlshr(arg_ids.to_vec()),
                    "bvashr" => self.terms.mk_bvashr(arg_ids.to_vec()),
                    "bvudiv" => self.terms.mk_bvudiv(arg_ids.to_vec()),
                    "bvurem" => self.terms.mk_bvurem(arg_ids.to_vec()),
                    "bvsdiv" => self.terms.mk_bvsdiv(arg_ids.to_vec()),
                    "bvsrem" => self.terms.mk_bvsrem(arg_ids.to_vec()),
                    _ => self.terms.mk_bvsmod(arg_ids.to_vec()),
                }))
            }
            "bvnot" | "bvneg" | "bv2nat" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                Ok(Some(match name {
                    "bvnot" => self.terms.mk_bvnot(arg_ids[0]),
                    "bvneg" => self.terms.mk_bvneg(arg_ids[0]),
                    _ => self.terms.mk_bv2nat(arg_ids[0]),
                }))
            }
            "bvcomp" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
            | "bvsge" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                Ok(Some(match name {
                    "bvcomp" => self.terms.mk_bvcomp(arg_ids[0], arg_ids[1]),
                    "bvult" => self.terms.mk_bvult(arg_ids[0], arg_ids[1]),
                    "bvule" => self.terms.mk_bvule(arg_ids[0], arg_ids[1]),
                    "bvugt" => self.terms.mk_bvugt(arg_ids[0], arg_ids[1]),
                    "bvuge" => self.terms.mk_bvuge(arg_ids[0], arg_ids[1]),
                    "bvslt" => self.terms.mk_bvslt(arg_ids[0], arg_ids[1]),
                    "bvsle" => self.terms.mk_bvsle(arg_ids[0], arg_ids[1]),
                    "bvsgt" => self.terms.mk_bvsgt(arg_ids[0], arg_ids[1]),
                    _ => self.terms.mk_bvsge(arg_ids[0], arg_ids[1]),
                }))
            }
            _ => Ok(None),
        }
    }
}
