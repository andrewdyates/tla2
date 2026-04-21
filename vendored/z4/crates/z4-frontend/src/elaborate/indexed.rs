// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use hashbrown::HashMap;

use crate::command::Term as ParsedTerm;
use z4_core::{Sort, Symbol, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    /// Elaborate an indexed application `((_ name idx...) arg1 arg2 ...)`.
    ///
    /// Handles structured indexed identifiers parsed by `command.rs` as
    /// `IndexedApp(name, indices, args)`, avoiding the stringify-then-reparse
    /// anti-pattern where `(_ extract 7 0)` was encoded as `App("(_ extract 7 0)", args)`
    /// and re-parsed via `name.starts_with("(_ ")` + `split_whitespace`.
    pub(super) fn elaborate_indexed_app(
        &mut self,
        name: &str,
        str_indices: &[String],
        args: &[ParsedTerm],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        // SMT-LIB datatype tester: (_ is Constructor) → normalize to "is-Ctor"
        // and delegate to elaborate_app which handles function defs and symbol lookup.
        if name == "is" && str_indices.len() == 1 {
            let tester_name = format!("is-{}", str_indices[0]);
            return self.elaborate_app(&tester_name, args, env);
        }

        let arg_ids: Vec<TermId> = args
            .iter()
            .map(|a| self.elaborate_term(a, env))
            .collect::<Result<Vec<_>>>()?;

        let indices: Vec<u32> = str_indices.iter().filter_map(|s| s.parse().ok()).collect();

        match name {
            "extract" => {
                if indices.len() != 2 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "extract requires 2 indices and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_bvextract(indices[0], indices[1], arg_ids[0]))
            }
            "int2bv" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "int2bv requires 1 index and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_int2bv(indices[0], arg_ids[0]))
            }
            "zero_extend" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "zero_extend requires 1 index and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_bvzero_extend(indices[0], arg_ids[0]))
            }
            "sign_extend" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "sign_extend requires 1 index and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_bvsign_extend(indices[0], arg_ids[0]))
            }
            "rotate_left" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "rotate_left requires 1 index and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_bvrotate_left(indices[0], arg_ids[0]))
            }
            "rotate_right" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "rotate_right requires 1 index and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_bvrotate_right(indices[0], arg_ids[0]))
            }
            "repeat" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "repeat requires 1 index and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_bvrepeat(indices[0], arg_ids[0]))
            }
            "re.loop" => {
                if indices.len() != 2 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "re.loop requires 2 indices and 1 argument".to_string(),
                    ));
                }
                Ok(self.terms.mk_app(
                    Symbol::indexed("re.loop", indices),
                    vec![arg_ids[0]],
                    Sort::RegLan,
                ))
            }
            "re.^" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "re.^ requires 1 index and 1 argument".to_string(),
                    ));
                }
                let n = indices[0];
                Ok(self.terms.mk_app(
                    Symbol::indexed("re.loop", vec![n, n]),
                    vec![arg_ids[0]],
                    Sort::RegLan,
                ))
            }
            "to_fp" => {
                if indices.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_fp requires 2 indices (eb sb)".to_string(),
                    ));
                }
                let fp_sort = Sort::FloatingPoint(indices[0], indices[1]);
                Ok(self
                    .terms
                    .mk_app(Symbol::indexed("to_fp", indices), arg_ids, fp_sort))
            }
            "to_fp_unsigned" => {
                if indices.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_fp_unsigned requires 2 indices (eb sb)".to_string(),
                    ));
                }
                let fp_sort = Sort::FloatingPoint(indices[0], indices[1]);
                Ok(self
                    .terms
                    .mk_app(Symbol::indexed("to_fp_unsigned", indices), arg_ids, fp_sort))
            }
            "fp.to_ubv" | "fp.to_sbv" => {
                if indices.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires 1 index (width)"
                    )));
                }
                let bv_sort = Sort::bitvec(indices[0]);
                Ok(self
                    .terms
                    .mk_app(Symbol::indexed(name, indices), arg_ids, bv_sort))
            }
            _ => {
                // Unknown indexed identifier — reconstruct stringified name
                // for symbol table lookup (legacy path).
                let stringified = format!("(_ {} {})", name, str_indices.join(" "));
                let sym = Symbol::indexed(name, indices);
                let result_sort = if let Some(info) = self.symbols.get(&stringified) {
                    info.sort.clone()
                } else {
                    return Err(ElaborateError::Unsupported(format!(
                        "unknown indexed identifier: {name}"
                    )));
                };
                Ok(self.terms.mk_app(sym, arg_ids, result_sort))
            }
        }
    }
}
