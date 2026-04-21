// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{Context, ElaborateError, Result};
use crate::command;
use z4_core::Sort;

impl Context {
    /// Convert a parsed sort to internal sort
    pub(crate) fn elaborate_sort(&self, sort: &command::Sort) -> Result<Sort> {
        match sort {
            command::Sort::Simple(name) => match name.as_str() {
                "Bool" => Ok(Sort::Bool),
                "Int" => Ok(Sort::Int),
                "Real" => Ok(Sort::Real),
                "String" => Ok(Sort::String),
                "RegLan" => Ok(Sort::RegLan),
                other => {
                    if let Some(s) = self.sort_defs.get(other) {
                        Ok(s.clone())
                    } else {
                        Ok(Sort::Uninterpreted(other.to_string()))
                    }
                }
            },
            command::Sort::Indexed(name, indices) => match name.as_str() {
                "BitVec" => {
                    let width: u32 =
                        indices
                            .first()
                            .and_then(|s| s.parse().ok())
                            .ok_or_else(|| {
                                ElaborateError::InvalidConstant("BitVec width".to_string())
                            })?;
                    Ok(Sort::bitvec(width))
                }
                "FloatingPoint" => {
                    let eb: u32 =
                        indices
                            .first()
                            .and_then(|s| s.parse().ok())
                            .ok_or_else(|| {
                                ElaborateError::InvalidConstant(
                                    "FloatingPoint exponent bits".to_string(),
                                )
                            })?;
                    let sb: u32 = indices.get(1).and_then(|s| s.parse().ok()).ok_or_else(|| {
                        ElaborateError::InvalidConstant(
                            "FloatingPoint significand bits".to_string(),
                        )
                    })?;
                    Ok(Sort::FloatingPoint(eb, sb))
                }
                other => Err(ElaborateError::Unsupported(format!(
                    "indexed sort: {other}"
                ))),
            },
            command::Sort::Parameterized(name, params) => match name.as_str() {
                "Array" => {
                    if params.len() != 2 {
                        return Err(ElaborateError::InvalidConstant(
                            "Array requires 2 type parameters".to_string(),
                        ));
                    }
                    let index = self.elaborate_sort(&params[0])?;
                    let element = self.elaborate_sort(&params[1])?;
                    Ok(Sort::array(index, element))
                }
                "Seq" => {
                    if params.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(
                            "Seq requires 1 type parameter".to_string(),
                        ));
                    }
                    let element = self.elaborate_sort(&params[0])?;
                    Ok(Sort::seq(element))
                }
                other => Err(ElaborateError::Unsupported(format!(
                    "parameterized sort: {other}"
                ))),
            },
        }
    }
}
