// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::config::Config;
use crate::constants::{parse_constant_value, ConstantParseError};
use crate::Value;
use num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use tla_core::ast::{Expr, Module, Unit};
use tla_core::name_intern::NameId;
use tla_core::{
    compute_contains_prime, compute_guards_depend_on_prime, compute_has_primed_param,
    compute_is_recursive, Span, Spanned,
};

/// Errors from applying module-scoped config overrides and assignments.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum ConfigOverrideError {
    /// Config references a module that is not in the loaded module set.
    #[error("Config refers to unknown module '{0}'")]
    UnknownModule(String),

    /// An override chain exists (A overrides B, and B is also overridden).
    #[error("Config override chain in module '{module}': '{lhs}' is overridden by '{rhs}', but '{rhs}' is also overridden")]
    OverrideChain {
        module: String,
        lhs: String,
        rhs: String,
    },

    /// Override refers to an operator not visible in the target module (LHS).
    #[error("Config module override refers to unknown operator '{op}' in module '{module}'")]
    UnknownOverrideTarget { op: String, module: String },

    /// Override LHS and RHS have different arities.
    #[error("Config module override arity mismatch in module '{module}': '{lhs}' has {lhs_arity} args but '{rhs}' has {rhs_arity} args")]
    ArityMismatch {
        module: String,
        lhs: String,
        lhs_arity: usize,
        rhs: String,
        rhs_arity: usize,
    },

    /// Override RHS operator is not visible in the root module scope.
    #[error("Config module override refers to unknown operator '{rhs}' (RHS) when overriding '{lhs}' in module '{module}'")]
    UnknownOverrideRhs {
        rhs: String,
        lhs: String,
        module: String,
    },

    /// Assignment refers to an operator not visible in the target module.
    #[error("Config module assignment refers to unknown operator '{op}' in module '{module}'")]
    UnknownAssignment { op: String, module: String },

    /// Assignment target has non-zero arity (only nullary operators can be assigned values).
    #[error("Config module assignment refers to operator '{op}' in module '{module}' with {arity} args (expected 0)")]
    AssignmentNonZeroArity {
        op: String,
        module: String,
        arity: usize,
    },

    /// Could not parse the assignment value string as a constant.
    #[error("Config module assignment parse error in module '{module}', '{op}': {source}")]
    AssignmentParseError {
        module: String,
        op: String,
        #[source]
        source: ConstantParseError,
    },

    /// Value type not supported for AST conversion in module-scoped assignments.
    #[error("Unsupported config value for module-scoped assignment: {value_debug}")]
    UnsupportedValue { value_debug: String },
}

fn builtin_arity(name: &str) -> Option<usize> {
    match name {
        // Part of #826: TLC treats these as builtins (and configs override them to become enumerable).
        "Nat" | "Int" | "Real" | "Infinity" | "BOOLEAN" => Some(0),
        _ => None,
    }
}

pub(crate) fn rewrite_modules_for_cfg_scoped_overrides(
    main_module: &Module,
    extended_modules: &[&Module],
    unqualified_modules: &HashSet<&str>,
    config: &Config,
) -> Result<(Module, Vec<Module>), ConfigOverrideError> {
    if config.module_overrides.is_empty() && config.module_assignments.is_empty() {
        return Ok((
            main_module.clone(),
            extended_modules.iter().map(|m| (*m).clone()).collect(),
        ));
    }

    let mut available_modules: HashSet<&str> = HashSet::new();
    available_modules.insert(main_module.name.node.as_str());
    for m in extended_modules {
        available_modules.insert(m.name.node.as_str());
    }

    for mod_name in config
        .module_overrides
        .keys()
        .chain(config.module_assignments.keys())
    {
        if !available_modules.contains(mod_name.as_str()) {
            return Err(ConfigOverrideError::UnknownModule(mod_name.clone()));
        }
    }

    // Approximate TLC's root defns lookup for RHS by using the operator namespace visible to the
    // root module: EXTENDS + standalone INSTANCE closure (unqualified) plus the main module.
    let visible_op_arities =
        collect_visible_op_arities(main_module, extended_modules, unqualified_modules);
    let modules_by_name: HashMap<&str, &Module> = std::iter::once(main_module)
        .map(|m| (m.name.node.as_str(), m))
        .chain(extended_modules.iter().map(|m| (m.name.node.as_str(), *m)))
        .collect();

    let mut rewritten_main = main_module.clone();
    let mut rewritten_exts: Vec<Module> = extended_modules.iter().map(|m| (*m).clone()).collect();

    // Apply module-scoped entries to extended modules first (doesn't matter semantically, but
    // keeps deterministic behavior consistent with how modules are loaded).
    for m in &mut rewritten_exts {
        let lhs_visible_op_arities = collect_module_visible_op_arities(m, &modules_by_name);
        let changed =
            apply_cfg_scoped_to_module(m, &visible_op_arities, &lhs_visible_op_arities, config)?;
        if changed {
            compute_contains_prime(m);
            compute_guards_depend_on_prime(m);
            compute_has_primed_param(m);
            compute_is_recursive(m);
        }
    }

    let lhs_visible_op_arities =
        collect_module_visible_op_arities(&rewritten_main, &modules_by_name);
    let changed = apply_cfg_scoped_to_module(
        &mut rewritten_main,
        &visible_op_arities,
        &lhs_visible_op_arities,
        config,
    )?;
    if changed {
        compute_contains_prime(&mut rewritten_main);
        compute_guards_depend_on_prime(&mut rewritten_main);
        compute_has_primed_param(&mut rewritten_main);
        compute_is_recursive(&mut rewritten_main);
    }

    Ok((rewritten_main, rewritten_exts))
}

fn collect_visible_op_arities(
    main_module: &Module,
    extended_modules: &[&Module],
    unqualified_modules: &HashSet<&str>,
) -> HashMap<String, usize> {
    let mut arities: HashMap<String, usize> = HashMap::new();

    // Builtins are always root-visible (TLC includes them in root defns).
    for name in ["Nat", "Int", "Real", "Infinity", "BOOLEAN"] {
        arities.insert(name.to_string(), 0);
    }

    // Unqualified imports first (in order), then main module shadows.
    for m in extended_modules {
        if !unqualified_modules.contains(m.name.node.as_str()) {
            continue;
        }
        for unit in &m.units {
            if let Unit::Operator(def) = &unit.node {
                arities.insert(def.name.node.clone(), def.params.len());
            }
        }
    }
    for unit in &main_module.units {
        if let Unit::Operator(def) = &unit.node {
            arities.insert(def.name.node.clone(), def.params.len());
        }
    }

    arities
}

fn apply_cfg_scoped_to_module(
    module: &mut Module,
    visible_op_arities: &HashMap<String, usize>,
    lhs_visible_op_arities: &HashMap<String, usize>,
    config: &Config,
) -> Result<bool, ConfigOverrideError> {
    let module_name = module.name.node.as_str();
    let overrides = config.module_overrides.get(module_name);
    let assignments = config.module_assignments.get(module_name);
    if overrides.is_none() && assignments.is_none() {
        return Ok(false);
    }

    let mut op_index: HashMap<String, usize> = HashMap::new();
    for (idx, unit) in module.units.iter().enumerate() {
        if let Unit::Operator(def) = &unit.node {
            op_index.insert(def.name.node.clone(), idx);
        }
    }

    let mut changed = false;

    if let Some(ov) = overrides {
        // Deterministic iteration: `HashMap` order is randomized.
        let mut lhs_keys: Vec<&String> = ov.keys().collect();
        lhs_keys.sort();
        for lhs in lhs_keys {
            let rhs = &ov[lhs];
            if ov.contains_key(rhs) {
                return Err(ConfigOverrideError::OverrideChain {
                    module: module_name.to_string(),
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                });
            }

            let unit_idx = if let Some(&idx) = op_index.get(lhs.as_str()) {
                idx
            } else {
                // TLC allows overriding symbols visible via EXTENDS (and builtins like Nat/Int)
                // even if they are not locally defined. Model this by inserting a local operator
                // definition that shadows the imported/builtin symbol in this module's scope.
                let Some(lhs_arity) = lhs_visible_op_arities.get(lhs) else {
                    return Err(ConfigOverrideError::UnknownOverrideTarget {
                        op: lhs.clone(),
                        module: module_name.to_string(),
                    });
                };

                let params = (0..*lhs_arity)
                    .map(|i| tla_core::ast::OpParam {
                        name: Spanned::dummy(format!("p{}", i + 1)),
                        arity: 0,
                    })
                    .collect();

                let def = tla_core::ast::OperatorDef {
                    name: Spanned::dummy(lhs.clone()),
                    params,
                    body: Spanned::new(Expr::Ident(lhs.clone(), NameId::INVALID), Span::dummy()),
                    local: false,
                    contains_prime: false,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                };

                let idx = module.units.len();
                module
                    .units
                    .push(Spanned::new(Unit::Operator(def), Span::dummy()));
                op_index.insert(lhs.clone(), idx);
                idx
            };

            let Unit::Operator(def) = &mut module.units[unit_idx].node else {
                continue;
            };

            let lhs_arity = def.params.len();
            let rhs_arity = visible_op_arities
                .get(rhs)
                .copied()
                .or_else(|| builtin_arity(rhs));
            match rhs_arity {
                Some(rhs_arity) if rhs_arity == lhs_arity => {}
                Some(rhs_arity) => {
                    return Err(ConfigOverrideError::ArityMismatch {
                        module: module_name.to_string(),
                        lhs: lhs.clone(),
                        lhs_arity,
                        rhs: rhs.clone(),
                        rhs_arity,
                    });
                }
                None => {
                    return Err(ConfigOverrideError::UnknownOverrideRhs {
                        rhs: rhs.clone(),
                        lhs: lhs.clone(),
                        module: module_name.to_string(),
                    });
                }
            }

            let span = def.body.span;
            def.body = rewrite_body_for_override(def, rhs, span, visible_op_arities);
            changed = true;
        }
    }

    if let Some(asg) = assignments {
        // Deterministic iteration: `HashMap` order is randomized.
        let mut lhs_keys: Vec<&String> = asg.keys().collect();
        lhs_keys.sort();
        for lhs in lhs_keys {
            let value_str = &asg[lhs];
            let unit_idx = if let Some(&idx) = op_index.get(lhs.as_str()) {
                idx
            } else {
                let Some(lhs_arity) = lhs_visible_op_arities.get(lhs) else {
                    return Err(ConfigOverrideError::UnknownAssignment {
                        op: lhs.clone(),
                        module: module_name.to_string(),
                    });
                };
                if *lhs_arity != 0 {
                    return Err(ConfigOverrideError::AssignmentNonZeroArity {
                        op: lhs.clone(),
                        module: module_name.to_string(),
                        arity: *lhs_arity,
                    });
                }

                let def = tla_core::ast::OperatorDef {
                    name: Spanned::dummy(lhs.clone()),
                    params: Vec::new(),
                    body: Spanned::new(Expr::Ident(lhs.clone(), NameId::INVALID), Span::dummy()),
                    local: false,
                    contains_prime: false,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                };

                let idx = module.units.len();
                module
                    .units
                    .push(Spanned::new(Unit::Operator(def), Span::dummy()));
                op_index.insert(lhs.clone(), idx);
                idx
            };

            let Unit::Operator(def) = &mut module.units[unit_idx].node else {
                continue;
            };

            let value = parse_constant_value(value_str).map_err(|source| {
                ConfigOverrideError::AssignmentParseError {
                    module: module_name.to_string(),
                    op: lhs.clone(),
                    source,
                }
            })?;

            let span = def.body.span;
            def.body = value_to_spanned_expr(&value, span)?;
            changed = true;
        }
    }

    Ok(changed)
}

fn collect_module_visible_op_arities(
    module: &Module,
    modules_by_name: &HashMap<&str, &Module>,
) -> HashMap<String, usize> {
    let mut arities: HashMap<String, usize> = HashMap::new();

    // Builtins are always visible (and can be overridden to become enumerable).
    for name in ["Nat", "Int", "Real", "Infinity", "BOOLEAN"] {
        arities.insert(name.to_string(), 0);
    }

    fn visit(
        m: &Module,
        modules_by_name: &HashMap<&str, &Module>,
        visited: &mut HashSet<String>,
        arities: &mut HashMap<String, usize>,
    ) {
        if !visited.insert(m.name.node.clone()) {
            return;
        }

        for ext in &m.extends {
            if let Some(ext_mod) = modules_by_name.get(ext.node.as_str()) {
                visit(ext_mod, modules_by_name, visited, arities);
            }
        }

        // Standalone INSTANCE imports also contribute to the module's unqualified operator scope
        // (TLC includes these in ModuleNode.getOpDefs).
        for unit in &m.units {
            let Unit::Instance(inst) = &unit.node else {
                continue;
            };
            if let Some(inst_mod) = modules_by_name.get(inst.module.node.as_str()) {
                visit(inst_mod, modules_by_name, visited, arities);
            }
        }

        for unit in &m.units {
            if let Unit::Operator(def) = &unit.node {
                arities.insert(def.name.node.clone(), def.params.len());
            }
        }
    }

    let mut visited: HashSet<String> = HashSet::new();
    visit(module, modules_by_name, &mut visited, &mut arities);
    arities
}

fn rewrite_body_for_override(
    def: &tla_core::ast::OperatorDef,
    rhs: &str,
    span: Span,
    visible_op_arities: &HashMap<String, usize>,
) -> Spanned<Expr> {
    let rhs_arity = visible_op_arities.get(rhs).copied();

    // If RHS is a visible operator with matching arity, rewrite `lhs(p1..pk) == rhs(p1..pk)`.
    // Otherwise, treat RHS as a value identifier and ignore LHS args (TLC sets the body tool object).
    let expr = match rhs_arity {
        Some(0) => Expr::Ident(rhs.to_string(), NameId::INVALID),
        Some(_) => {
            let args: Vec<Spanned<Expr>> = def
                .params
                .iter()
                .map(|p| Spanned::new(Expr::Ident(p.name.node.clone(), NameId::INVALID), span))
                .collect();
            Expr::Apply(
                Box::new(Spanned::new(
                    Expr::Ident(rhs.to_string(), NameId::INVALID),
                    span,
                )),
                args,
            )
        }
        None => Expr::Ident(rhs.to_string(), NameId::INVALID),
    };

    Spanned::new(expr, span)
}

fn value_to_spanned_expr(value: &Value, span: Span) -> Result<Spanned<Expr>, ConfigOverrideError> {
    Ok(Spanned::new(value_to_expr(value, span)?, span))
}

fn value_to_expr(value: &Value, span: Span) -> Result<Expr, ConfigOverrideError> {
    match value {
        Value::Bool(b) => Ok(Expr::Bool(*b)),
        Value::SmallInt(n) => Ok(Expr::Int(BigInt::from(*n))),
        Value::Int(n) => Ok(Expr::Int((**n).clone())),
        Value::String(s) => Ok(Expr::String(s.as_ref().to_string())),
        Value::ModelValue(name) => Ok(Expr::Ident(name.as_ref().to_string(), NameId::INVALID)),
        Value::Tuple(elems) => {
            let elems = elems
                .iter()
                .map(|v| Ok(Spanned::new(value_to_expr(v, span)?, span)))
                .collect::<Result<Vec<_>, ConfigOverrideError>>()?;
            Ok(Expr::Tuple(elems))
        }
        Value::Set(set) => {
            let elems = set
                .iter()
                .map(|v| Ok(Spanned::new(value_to_expr(v, span)?, span)))
                .collect::<Result<Vec<_>, ConfigOverrideError>>()?;
            Ok(Expr::SetEnum(elems))
        }
        Value::Record(rec) => {
            let fields = rec
                .iter_str()
                .map(|(k, v)| {
                    Ok((
                        Spanned::new(k.to_string(), Span::dummy()),
                        Spanned::new(value_to_expr(v, span)?, span),
                    ))
                })
                .collect::<Result<Vec<_>, ConfigOverrideError>>()?;
            Ok(Expr::Record(fields))
        }
        other => Err(ConfigOverrideError::UnsupportedValue {
            value_debug: format!("{:?}", other),
        }),
    }
}
