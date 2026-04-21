// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA model evaluation and recovery helpers.
//!
//! Free functions for evaluating integer/boolean terms under a model
//! and recovering variable values from asserted equalities and
//! variable substitutions. Used by `lia.rs` and `combined.rs`.
//!
//! Split from `lia.rs` for code health (#7006, #5970).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::TermId;
use z4_lia::LiaModel;

use crate::preprocess::VariableSubstitution;

/// SMT-LIB integer division: floor division for positive divisor,
/// negated floor division for negative divisor.
fn smtlib_div(n: &num_bigint::BigInt, d: &num_bigint::BigInt) -> num_bigint::BigInt {
    use num_integer::Integer;
    use num_traits::Signed;
    if d.is_positive() {
        n.div_floor(d)
    } else {
        // (div n d) = -(div n (-d)) for d < 0
        -n.div_floor(&(-d))
    }
}

/// Evaluate a boolean condition under the current integer model values.
fn eval_lia_bool_under_values(
    terms: &z4_core::TermStore,
    tid: TermId,
    values: &HashMap<TermId, num_bigint::BigInt>,
) -> Option<bool> {
    use z4_core::term::{Constant, TermData};

    match terms.get(tid) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        TermData::Not(inner) => eval_lia_bool_under_values(terms, *inner, values).map(|b| !b),
        TermData::App(sym, args) => {
            let name = sym.name();
            match name {
                "and" => {
                    for &arg in args {
                        if !eval_lia_bool_under_values(terms, arg, values)? {
                            return Some(false);
                        }
                    }
                    Some(true)
                }
                "or" => {
                    for &arg in args {
                        if eval_lia_bool_under_values(terms, arg, values)? {
                            return Some(true);
                        }
                    }
                    Some(false)
                }
                "<" if args.len() == 2 => {
                    let a = eval_lia_int_under_values(terms, args[0], values)?;
                    let b = eval_lia_int_under_values(terms, args[1], values)?;
                    Some(a < b)
                }
                "<=" if args.len() == 2 => {
                    let a = eval_lia_int_under_values(terms, args[0], values)?;
                    let b = eval_lia_int_under_values(terms, args[1], values)?;
                    Some(a <= b)
                }
                ">" if args.len() == 2 => {
                    let a = eval_lia_int_under_values(terms, args[0], values)?;
                    let b = eval_lia_int_under_values(terms, args[1], values)?;
                    Some(a > b)
                }
                ">=" if args.len() == 2 => {
                    let a = eval_lia_int_under_values(terms, args[0], values)?;
                    let b = eval_lia_int_under_values(terms, args[1], values)?;
                    Some(a >= b)
                }
                "=" if args.len() == 2 => {
                    if let (Some(a), Some(b)) = (
                        eval_lia_int_under_values(terms, args[0], values),
                        eval_lia_int_under_values(terms, args[1], values),
                    ) {
                        Some(a == b)
                    } else if let (Some(a), Some(b)) = (
                        eval_lia_bool_under_values(terms, args[0], values),
                        eval_lia_bool_under_values(terms, args[1], values),
                    ) {
                        Some(a == b)
                    } else {
                        None
                    }
                }
                "distinct" if args.len() == 2 => {
                    if let (Some(a), Some(b)) = (
                        eval_lia_int_under_values(terms, args[0], values),
                        eval_lia_int_under_values(terms, args[1], values),
                    ) {
                        Some(a != b)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn eval_lia_int_under_values(
    terms: &z4_core::TermStore,
    tid: TermId,
    values: &HashMap<TermId, num_bigint::BigInt>,
) -> Option<num_bigint::BigInt> {
    use z4_core::term::{Constant, TermData};

    match terms.get(tid) {
        TermData::Const(Constant::Int(n)) => Some(n.clone()),
        TermData::Var(_, _) => values.get(&tid).cloned(),
        TermData::Ite(cond, then_t, else_t) => {
            let cond_val = eval_lia_bool_under_values(terms, *cond, values)?;
            if cond_val {
                eval_lia_int_under_values(terms, *then_t, values)
            } else {
                eval_lia_int_under_values(terms, *else_t, values)
            }
        }
        TermData::App(sym, args) => {
            let name = sym.name();
            match name {
                "+" => {
                    let mut sum = num_bigint::BigInt::from(0);
                    for &arg in args {
                        sum += eval_lia_int_under_values(terms, arg, values)?;
                    }
                    Some(sum)
                }
                "-" if args.len() == 2 => {
                    let a = eval_lia_int_under_values(terms, args[0], values)?;
                    let b = eval_lia_int_under_values(terms, args[1], values)?;
                    Some(a - b)
                }
                "-" if args.len() == 1 => {
                    let a = eval_lia_int_under_values(terms, args[0], values)?;
                    Some(-a)
                }
                "*" => {
                    let mut prod = num_bigint::BigInt::from(1);
                    for &arg in args {
                        prod *= eval_lia_int_under_values(terms, arg, values)?;
                    }
                    Some(prod)
                }
                "div" if args.len() == 2 => {
                    let lhs = eval_lia_int_under_values(terms, args[0], values)?;
                    let rhs = eval_lia_int_under_values(terms, args[1], values)?;
                    if rhs == num_bigint::BigInt::from(0) {
                        return None;
                    }
                    Some(smtlib_div(&lhs, &rhs))
                }
                "mod" if args.len() == 2 => {
                    let lhs = eval_lia_int_under_values(terms, args[0], values)?;
                    let rhs = eval_lia_int_under_values(terms, args[1], values)?;
                    if rhs == num_bigint::BigInt::from(0) {
                        return None;
                    }
                    let q = smtlib_div(&lhs, &rhs);
                    Some(lhs - &rhs * q)
                }
                "abs" if args.len() == 1 => {
                    let v = eval_lia_int_under_values(terms, args[0], values)?;
                    Some(if v < num_bigint::BigInt::from(0) {
                        -v
                    } else {
                        v
                    })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Recover variable values from direct asserted equalities in the original formula.
pub(in crate::executor) fn recover_lia_equalities_from_assertions(
    terms: &z4_core::TermStore,
    assertions: &[TermId],
    model: &mut LiaModel,
) {
    use z4_core::term::TermData;

    let max_passes = assertions.len().max(1);
    for _ in 0..max_passes {
        let mut progress = false;
        for &assertion in assertions {
            let TermData::App(sym, args) = terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }

            for &(var, expr) in &[(args[0], args[1]), (args[1], args[0])] {
                if !matches!(terms.get(var), TermData::Var(_, _))
                    || !matches!(terms.sort(var), z4_core::Sort::Int)
                {
                    continue;
                }
                // Packet 3 (#6698): Fill-only — never overwrite an existing
                // model value. When a variable already has a value from the
                // theory solver or trusted substitution recovery, that value
                // is stronger evidence than a symmetric equality walk.
                if model.values.contains_key(&var) {
                    continue;
                }
                let Some(value) = eval_lia_int_under_values(terms, expr, &model.values) else {
                    continue;
                };
                model.values.insert(var, value);
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
}

/// Recover model values for variables eliminated by variable substitution (#2767).
///
/// When `VariableSubstitution` replaces `result_a -> (+ self_a 1)`, the LIA model
/// only has a value for `self_a`. This function evaluates the replacement expression
/// to compute `result_a`'s value.
pub(in crate::executor) fn recover_substituted_lia_values(
    terms: &z4_core::TermStore,
    var_subst: &VariableSubstitution,
    model: &mut LiaModel,
) {
    use z4_core::term::TermData;

    // Collect leaf variables from substitution RHS expressions.
    fn collect_vars(terms: &z4_core::TermStore, tid: TermId, vars: &mut HashSet<TermId>) {
        match terms.get(tid) {
            TermData::Var(_, _) => {
                vars.insert(tid);
            }
            TermData::App(_, args) => {
                for &arg in args {
                    collect_vars(terms, arg, vars);
                }
            }
            TermData::Ite(cond, then_t, else_t) => {
                collect_vars(terms, *cond, vars);
                collect_vars(terms, *then_t, vars);
                collect_vars(terms, *else_t, vars);
            }
            TermData::Not(inner) => {
                collect_vars(terms, *inner, vars);
            }
            _ => {}
        }
    }

    let substituted_from: HashSet<TermId> = var_subst.substitutions().keys().copied().collect();

    // Seed default values (0) for free integer variables referenced in substitution
    // expressions but not present in the model (#3201).
    let mut rhs_vars = HashSet::new();
    for &to in var_subst.substitutions().values() {
        collect_vars(terms, to, &mut rhs_vars);
    }
    for var_tid in rhs_vars {
        if substituted_from.contains(&var_tid) {
            continue;
        }
        if matches!(terms.sort(var_tid), z4_core::Sort::Int) && !model.values.contains_key(&var_tid)
        {
            model.values.insert(var_tid, num_bigint::BigInt::from(0));
        }
    }

    // Process substitutions in multiple passes to handle transitive chains.
    let subs: Vec<_> = var_subst
        .substitutions()
        .iter()
        .map(|(&from, &to)| (from, to))
        .collect();
    let mut remaining = subs;
    let max_passes = remaining.len();
    for _ in 0..max_passes {
        if remaining.is_empty() {
            break;
        }
        let prev_len = remaining.len();
        let mut next = Vec::new();
        for (from, to) in remaining {
            if let Some(val) = eval_lia_int_under_values(terms, to, &model.values) {
                model.values.insert(from, val);
            } else {
                next.push((from, to));
            }
        }
        if next.len() == prev_len {
            break;
        }
        remaining = next;
    }
}
