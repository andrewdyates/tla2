// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! z4 ALL-SAT Init state enumeration entry point.

use std::collections::HashMap;
use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::eval::{eval_entry, EvalCtx};
use crate::state::State;

use super::value_convert::{collect_referenced_zero_arg_ops, try_value_to_z4_spanned_expr};
use super::{VarInfo, VarSort, Z4EnumConfig, Z4EnumError, Z4EnumResult};

#[cfg(feature = "z4")]
use super::model::{add_blocking_clause, model_to_state};
#[cfg(feature = "z4")]
use super::type_inference::infer_var_types;

/// Convert VarSort to TlaSort for z4 translator
#[cfg(feature = "z4")]
fn varsort_to_tlasort(sort: &VarSort) -> Result<tla_z4::TlaSort, String> {
    use tla_z4::TlaSort;
    match sort {
        VarSort::Bool => Ok(TlaSort::Bool),
        VarSort::Int => Ok(TlaSort::Int),
        VarSort::String { .. } => Ok(TlaSort::String),
        VarSort::Function { .. } => Err("nested function types not supported in tuple".to_string()),
        VarSort::Tuple { element_sorts } => {
            let tla_sorts: Vec<TlaSort> = element_sorts
                .iter()
                .map(varsort_to_tlasort)
                .collect::<Result<_, _>>()?;
            Ok(TlaSort::Tuple {
                element_sorts: tla_sorts,
            })
        }
        VarSort::Heterogeneous { reason } => Err(format!("heterogeneous set: {}", reason)),
    }
}

/// Enumerate Init states using z4 SMT solver.
///
/// This is the main entry point for z4-based Init enumeration.
/// It translates the Init predicate to z4 constraints and uses
/// ALL-SAT with blocking clauses to enumerate all satisfying models.
///
/// # Arguments
/// * `ctx` - Evaluation context with operator definitions
/// * `init_expr` - The Init predicate expression
/// * `vars` - State variables to enumerate
/// * `var_types` - Optional type information for variables
/// * `config` - Enumeration configuration
///
/// # Returns
/// Vector of all States satisfying Init, or error
#[cfg(feature = "z4")]
pub(crate) fn enumerate_init_states_z4(
    ctx: &EvalCtx,
    init_expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    var_types: Option<&HashMap<String, VarInfo>>,
    config: &Z4EnumConfig,
) -> Z4EnumResult<Vec<State>> {
    use tla_z4::{SolveResult, TlaSort, Z4Translator};

    if config.debug {
        eprintln!(
            "[z4-enum] Starting z4-based Init enumeration for {} variables",
            vars.len()
        );
    }

    // Create translator
    let mut translator = Z4Translator::new();

    // Part of #522/#515: Pass constant definitions to translator, pre-evaluating where safe.
    // We only attempt pre-evaluation for constants referenced by Init,
    // since evaluating every constant can be expensive (and can materialize huge sets).
    let mut constant_defs: HashMap<String, Spanned<Expr>> = HashMap::new();
    for (name, def) in ctx.shared().ops.iter() {
        if !def.params.is_empty() {
            continue; // Only zero-arg operators (constants)
        }
        constant_defs.insert(name.clone(), def.body.clone());
    }

    let mut referenced_constants = std::collections::BTreeSet::new();
    collect_referenced_zero_arg_ops(init_expr, ctx, &mut referenced_constants);

    let mut pre_eval_count = 0;
    let mut fallback_count = 0;
    for name in referenced_constants {
        let Some(def) = ctx.shared().ops.get(&name) else {
            continue;
        };

        let evaluated_expr = match eval_entry(ctx, &def.body) {
            Ok(value) => match try_value_to_z4_spanned_expr(&value, def.body.span) {
                Some(expr) => {
                    if config.debug {
                        eprintln!(
                            "[z4-enum] Pre-evaluated constant '{}' to z4-safe Expr",
                            name
                        );
                    }
                    pre_eval_count += 1;
                    expr
                }
                None => {
                    if config.debug {
                        eprintln!(
                            "[z4-enum] Constant '{}' not representable for z4, using raw expr",
                            name
                        );
                    }
                    fallback_count += 1;
                    def.body.clone()
                }
            },
            Err(e) => {
                if config.debug {
                    eprintln!(
                        "[z4-enum] Constant '{}' eval failed ({}), using raw expr",
                        name, e
                    );
                }
                fallback_count += 1;
                def.body.clone()
            }
        };
        constant_defs.insert(name, evaluated_expr);
    }

    if config.debug && (pre_eval_count > 0 || fallback_count > 0) {
        eprintln!(
            "[z4-enum] Constants: {} pre-evaluated, {} fallback",
            pre_eval_count, fallback_count
        );
    }

    // Step 1: Declare variables
    // If we have type info, use it. Otherwise, infer from Init predicate.
    // Pass constant_defs to resolve Ident references during type inference.
    // Must happen BEFORE we move constant_defs to the translator.
    let var_infos = match var_types {
        Some(types) => types.clone(),
        None => infer_var_types(init_expr, vars, &constant_defs)?,
    };

    // Now pass constant_defs to the translator for Ident resolution.
    translator.set_constant_defs(constant_defs);

    for (name, info) in &var_infos {
        match &info.sort {
            VarSort::Bool => {
                translator.declare_var(name, TlaSort::Bool).map_err(|e| {
                    Z4EnumError::TranslationFailed(format!("declare {} failed: {}", name, e))
                })?;
            }
            VarSort::Int => {
                translator.declare_var(name, TlaSort::Int).map_err(|e| {
                    Z4EnumError::TranslationFailed(format!("declare {} failed: {}", name, e))
                })?;
            }
            VarSort::String { .. } => {
                translator.declare_var(name, TlaSort::String).map_err(|e| {
                    Z4EnumError::TranslationFailed(format!("declare {} failed: {}", name, e))
                })?;
            }
            VarSort::Function { domain_keys, range } => {
                let range_sort = match range.as_ref() {
                    VarSort::Bool => TlaSort::Bool,
                    VarSort::Int => TlaSort::Int,
                    VarSort::String { .. } => TlaSort::String,
                    VarSort::Function { .. }
                    | VarSort::Tuple { .. }
                    | VarSort::Heterogeneous { .. } => {
                        return Err(Z4EnumError::UnsupportedVarType {
                            var: name.clone(),
                            reason: "nested function/tuple/heterogeneous types not supported"
                                .to_string(),
                        });
                    }
                };
                translator
                    .declare_func_var(name, domain_keys.clone(), range_sort)
                    .map_err(|e| {
                        Z4EnumError::TranslationFailed(format!(
                            "declare func {} failed: {}",
                            name, e
                        ))
                    })?;
            }
            VarSort::Tuple { element_sorts } => {
                let tla_sorts: Vec<TlaSort> = element_sorts
                    .iter()
                    .map(|s| varsort_to_tlasort(s))
                    .collect::<Result<_, _>>()
                    .map_err(|reason| Z4EnumError::UnsupportedVarType {
                        var: name.clone(),
                        reason,
                    })?;
                translator.declare_tuple_var(name, tla_sorts).map_err(|e| {
                    Z4EnumError::TranslationFailed(format!("declare tuple {} failed: {}", name, e))
                })?;
            }
            // Part of #523: Heterogeneous sets cannot be represented in z4
            // Return error to force fallback to brute-force enumeration
            VarSort::Heterogeneous { reason } => {
                return Err(Z4EnumError::UnsupportedVarType {
                    var: name.clone(),
                    reason: format!("heterogeneous set membership: {}", reason),
                });
            }
        }
    }

    // Step 2: Translate Init predicate to z4 formula
    let init_term = translator
        .translate_bool(init_expr)
        .map_err(|e| Z4EnumError::TranslationFailed(format!("Init translation failed: {}", e)))?;

    translator.assert(init_term);

    // Part of #2826: Install solve timeout before the enumeration loop.
    if let Some(timeout) = config.solve_timeout {
        translator.set_timeout(Some(timeout));
    }

    // Step 3: Enumerate all solutions using blocking clauses
    let mut states = Vec::new();
    let mut solution_count = 0;

    loop {
        if solution_count >= config.max_solutions {
            return Err(Z4EnumError::MaxSolutionsExceeded(config.max_solutions));
        }

        // Part of #2826: Use try_check_sat for panic protection and typed errors.
        let sat_result = translator
            .try_check_sat()
            .map_err(|e| Z4EnumError::SolverFailed(format!("{}", e)))?;
        match sat_result {
            SolveResult::Sat => {
                // Part of #2826: Use try_get_model for typed model errors.
                let model = translator
                    .try_get_model()
                    .map_err(|e| Z4EnumError::InvalidModel(format!("{}", e)))?;

                // Get string reverse map for converting interned IDs back to strings
                let string_reverse_map = translator.get_string_reverse_map();

                let state = model_to_state(&model, &var_infos, &string_reverse_map)?;

                if config.debug && solution_count < 10 {
                    eprintln!("[z4-enum] Solution {}: {:?}", solution_count, state);
                }

                // Add blocking clause to exclude this solution
                add_blocking_clause(&mut translator, &model, &var_infos, &string_reverse_map)?;

                states.push(state);
                solution_count += 1;
            }
            SolveResult::Unsat(_) => {
                // No more solutions
                break;
            }
            SolveResult::Unknown => {
                // Part of #2826: Distinguish timeout from other unknown reasons.
                let is_timeout = translator
                    .last_unknown_reason()
                    .map_or(false, |r| matches!(r, tla_z4::UnknownReason::Timeout));
                if is_timeout {
                    return Err(Z4EnumError::SolverTimeout);
                }
                return Err(Z4EnumError::SolverUnknown);
            }
            _ => {
                return Err(Z4EnumError::SolverUnknown);
            }
        }
    }

    if config.debug {
        eprintln!("[z4-enum] Found {} Init states", states.len());
    }

    Ok(states)
}
