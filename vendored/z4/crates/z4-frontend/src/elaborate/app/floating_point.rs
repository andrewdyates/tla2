// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::{Sort, Symbol, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    pub(super) fn try_elaborate_floating_point_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "fp.abs" | "fp.neg" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    self.terms.sort(arg_ids[0]).clone(),
                )))
            }
            "fp.add" | "fp.sub" | "fp.mul" | "fp.div" => {
                self.expect_exact_arity(name, arg_ids, 3)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    self.terms.sort(arg_ids[1]).clone(),
                )))
            }
            "fp.sqrt" | "fp.roundToIntegral" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    self.terms.sort(arg_ids[1]).clone(),
                )))
            }
            "fp.fma" => {
                self.expect_exact_arity("fp.fma", arg_ids, 4)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("fp.fma"),
                    arg_ids.to_vec(),
                    self.terms.sort(arg_ids[1]).clone(),
                )))
            }
            "fp.rem" | "fp.min" | "fp.max" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    self.terms.sort(arg_ids[0]).clone(),
                )))
            }
            "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
            | "fp.isPositive" | "fp.isNegative" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids.to_vec(),
                    Sort::Bool,
                )))
            }
            "fp.to_real" => {
                self.expect_exact_arity("fp.to_real", arg_ids, 1)?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if !matches!(arg_sort, Sort::FloatingPoint(_, _)) {
                    return Err(ElaborateError::SortMismatch {
                        expected: "FloatingPoint".to_string(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("fp.to_real"),
                    arg_ids.to_vec(),
                    Sort::Real,
                )))
            }
            "fp.to_ieee_bv" => {
                self.expect_exact_arity("fp.to_ieee_bv", arg_ids, 1)?;
                match self.terms.sort(arg_ids[0]).clone() {
                    Sort::FloatingPoint(eb, sb) => Ok(Some(self.terms.mk_app(
                        Symbol::named("fp.to_ieee_bv"),
                        arg_ids.to_vec(),
                        Sort::bitvec(eb + sb),
                    ))),
                    actual => Err(ElaborateError::SortMismatch {
                        expected: "FloatingPoint".to_string(),
                        actual: actual.to_string(),
                    }),
                }
            }
            "fp" => {
                self.expect_exact_arity("fp", arg_ids, 3)?;
                let eb = match self.terms.sort(arg_ids[1]) {
                    Sort::BitVec(w) => w.width,
                    _ => {
                        return Err(ElaborateError::InvalidConstant(
                            "fp exponent must be a bitvector".to_string(),
                        ))
                    }
                };
                let sb = match self.terms.sort(arg_ids[2]) {
                    Sort::BitVec(w) => w.width + 1,
                    _ => {
                        return Err(ElaborateError::InvalidConstant(
                            "fp significand must be a bitvector".to_string(),
                        ))
                    }
                };
                Ok(Some(self.terms.mk_app(
                    Symbol::named("fp"),
                    arg_ids.to_vec(),
                    Sort::FloatingPoint(eb, sb),
                )))
            }
            _ => Ok(None),
        }
    }
}
