// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::TermId;

use super::{Context, ElaborateError, Result};

impl Context {
    pub(super) fn try_elaborate_arithmetic_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "+" => {
                self.maybe_promote_numeric_args(arg_ids)?;
                Ok(Some(self.terms.mk_add(arg_ids.to_vec())))
            }
            "-" => {
                self.maybe_promote_numeric_args(arg_ids)?;
                Ok(Some(self.terms.mk_sub(arg_ids.to_vec())))
            }
            "*" => {
                self.maybe_promote_numeric_args(arg_ids)?;
                Ok(Some(self.terms.mk_mul(arg_ids.to_vec())))
            }
            "/" => {
                self.promote_int_consts_to_real(arg_ids)?;
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "/ requires 2 arguments, got {}",
                        arg_ids.len()
                    )));
                }
                Ok(Some(self.terms.mk_div(arg_ids[0], arg_ids[1])))
            }
            "div" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "div requires 2 arguments, got {}",
                        arg_ids.len()
                    )));
                }
                Ok(Some(self.terms.mk_intdiv(arg_ids[0], arg_ids[1])))
            }
            "mod" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "mod requires 2 arguments, got {}",
                        arg_ids.len()
                    )));
                }
                Ok(Some(self.terms.mk_mod(arg_ids[0], arg_ids[1])))
            }
            "abs" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "abs requires 1 argument".to_string(),
                    ));
                }
                Ok(Some(self.terms.mk_abs(arg_ids[0])))
            }
            "min" | "max" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires 2 arguments"
                    )));
                }
                self.maybe_promote_numeric_args(arg_ids)?;
                Ok(Some(match name {
                    "min" => self.terms.mk_min(arg_ids[0], arg_ids[1]),
                    _ => self.terms.mk_max(arg_ids[0], arg_ids[1]),
                }))
            }
            "<" | "<=" | ">" | ">=" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 2 arguments"
                    )));
                }
                self.maybe_promote_numeric_args(arg_ids)?;
                if arg_ids.len() == 2 {
                    return Ok(Some(match name {
                        "<" => self.terms.mk_lt(arg_ids[0], arg_ids[1]),
                        "<=" => self.terms.mk_le(arg_ids[0], arg_ids[1]),
                        ">" => self.terms.mk_gt(arg_ids[0], arg_ids[1]),
                        _ => self.terms.mk_ge(arg_ids[0], arg_ids[1]),
                    }));
                }
                let mut cmps = Vec::new();
                for i in 0..arg_ids.len() - 1 {
                    cmps.push(match name {
                        "<" => self.terms.mk_lt(arg_ids[i], arg_ids[i + 1]),
                        "<=" => self.terms.mk_le(arg_ids[i], arg_ids[i + 1]),
                        ">" => self.terms.mk_gt(arg_ids[i], arg_ids[i + 1]),
                        _ => self.terms.mk_ge(arg_ids[i], arg_ids[i + 1]),
                    });
                }
                Ok(Some(self.terms.mk_and(cmps)))
            }
            _ => Ok(None),
        }
    }
}
