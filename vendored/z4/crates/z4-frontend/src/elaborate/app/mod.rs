// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use hashbrown::HashMap;

use crate::command::Term as ParsedTerm;
use z4_core::{Sort, Symbol, TermId};

use super::{Context, ElaborateError, Result};

mod arithmetic;
mod bitvectors;
mod core;
mod floating_point;
mod sequences;
mod strings;

impl Context {
    /// Elaborate a function application
    pub(super) fn elaborate_app(
        &mut self,
        name: &str,
        args: &[ParsedTerm],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        let name = if let Some(ctor_name) = name
            .strip_prefix("(_ is ")
            .and_then(|s| s.strip_suffix(')'))
        {
            format!("is-{ctor_name}")
        } else {
            name.to_string()
        };
        let name = name.as_str();

        if let Some((params, body)) = self.fun_defs.get(name).cloned() {
            if params.len() == args.len() {
                let mut new_env = env.clone();
                for ((param_name, _), arg) in params.iter().zip(args) {
                    let arg_id = self.elaborate_term(arg, env)?;
                    new_env.insert(param_name.clone(), arg_id);
                }
                return self.elaborate_term(&body, &new_env);
            }
        }

        let mut arg_ids: Vec<TermId> = args
            .iter()
            .map(|a| self.elaborate_term(a, env))
            .collect::<Result<Vec<_>>>()?;

        if let Some(info) = self.resolve_overloaded_symbol(name, &arg_ids)? {
            return Ok(self.terms.mk_app(Symbol::named(name), arg_ids, info.sort));
        }

        if let Some(info) = self.symbols.get(name) {
            if !info.arg_sorts.is_empty() {
                return Ok(self
                    .terms
                    .mk_app(Symbol::named(name), arg_ids, info.sort.clone()));
            }
        }

        if let Some(term) = self.try_elaborate_core_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_string_or_regex_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_sequence_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_arithmetic_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_bitvector_app(name, &arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_floating_point_app(name, &arg_ids)? {
            return Ok(term);
        }

        if name.starts_with("(_ ") {
            let parts: Vec<&str> = name
                .trim_start_matches("(_ ")
                .trim_end_matches(')')
                .split_whitespace()
                .collect();
            if parts.is_empty() {
                return Err(ElaborateError::InvalidConstant(name.to_string()));
            }

            let indices: Vec<u32> = parts[1..].iter().filter_map(|s| s.parse().ok()).collect();

            match parts[0] {
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
                    Ok(self.terms.mk_app(
                        Symbol::indexed("to_fp_unsigned", indices),
                        arg_ids,
                        fp_sort,
                    ))
                }
                "fp.to_ubv" | "fp.to_sbv" => {
                    if indices.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(format!(
                            "{} requires 1 index (width)",
                            parts[0]
                        )));
                    }
                    Ok(self.terms.mk_app(
                        Symbol::indexed(parts[0], indices.clone()),
                        arg_ids,
                        Sort::bitvec(indices[0]),
                    ))
                }
                _ => {
                    let result_sort = if let Some(info) = self.symbols.get(name) {
                        info.sort.clone()
                    } else {
                        return Err(ElaborateError::Unsupported(format!(
                            "unknown indexed identifier: {}",
                            parts[0]
                        )));
                    };
                    Ok(self
                        .terms
                        .mk_app(Symbol::indexed(parts[0], indices), arg_ids, result_sort))
                }
            }
        } else {
            let result_sort = if let Some(info) = self.symbols.get(name) {
                info.sort.clone()
            } else {
                return Err(ElaborateError::UndefinedSymbol(name.to_string()));
            };
            Ok(self.terms.mk_app(Symbol::named(name), arg_ids, result_sort))
        }
    }
}
