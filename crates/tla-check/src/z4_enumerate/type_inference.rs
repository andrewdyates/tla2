// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use super::{extract_var_name, VarInfo, VarSort, Z4EnumResult};

/// Infer variable types from Init predicate structure.
///
/// This analyzes the Init expression to determine variable sorts:
/// - `x = 0` or `x \in 1..10` -> Int
/// - `x = TRUE` or `x \in BOOLEAN` -> Bool
/// - `f \in [D -> R]` -> Function
///
/// Part of #515: constant_defs is passed to resolve Ident references.
/// This allows `x \in Arrangements` to infer tuple type from the pre-evaluated
/// Arrangements constant.
pub(super) fn infer_var_types(
    init_expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    constant_defs: &HashMap<String, Spanned<Expr>>,
) -> Z4EnumResult<HashMap<String, VarInfo>> {
    let mut var_infos = HashMap::new();

    // Initialize all vars as Int by default (most common case)
    for var in vars {
        var_infos.insert(
            var.to_string(),
            VarInfo {
                name: var.clone(),
                sort: VarSort::Int,
                domain_keys: None,
            },
        );
    }

    // Walk Init expression to refine type information
    infer_types_from_expr(&init_expr.node, vars, &mut var_infos, constant_defs);

    Ok(var_infos)
}

/// Walk expression to infer variable types
///
/// Part of #515: constant_defs is passed to resolve Ident references.
/// Resolve an expression through constant definitions.
/// If the expression is an `Ident` referencing a known constant, return the constant's definition.
/// Otherwise return the original expression.
fn resolve_through_constants<'a>(
    expr: &'a Expr,
    constant_defs: &'a HashMap<String, Spanned<Expr>>,
) -> &'a Expr {
    if let Expr::Ident(const_name, _) = expr {
        if let Some(def) = constant_defs.get(const_name) {
            return &def.node;
        }
    }
    expr
}

/// Infer a VarInfo from a set enumeration expression (e.g., `{"a", "b"}`, `{<<1,2>>}`).
/// Returns None if the set is empty or the element type yields the default Int sort.
fn infer_var_info_from_set_enum(name: &str, elements: &[Spanned<Expr>]) -> Option<VarInfo> {
    if elements.is_empty() {
        return None;
    }
    // Part of #523: Check for heterogeneous sets first
    if let Some(reason) = check_heterogeneous_set_enum(elements) {
        return Some(VarInfo {
            name: Arc::from(name),
            sort: VarSort::Heterogeneous { reason },
            domain_keys: None,
        });
    }
    // Homogeneous set - infer type from first element
    match &elements[0].node {
        Expr::String(_) => {
            let domain: Vec<String> = elements
                .iter()
                .filter_map(|e| match &e.node {
                    Expr::String(s) => Some(s.clone()),
                    _ => None,
                })
                .collect();
            Some(VarInfo {
                name: Arc::from(name),
                sort: VarSort::String { domain },
                domain_keys: None,
            })
        }
        Expr::Tuple(tuple_elems) => {
            let element_sorts: Vec<VarSort> = tuple_elems
                .iter()
                .map(|e| infer_sort_from_expr(&e.node))
                .collect();
            Some(VarInfo {
                name: Arc::from(name),
                sort: VarSort::Tuple { element_sorts },
                domain_keys: None,
            })
        }
        Expr::Bool(_) => Some(VarInfo {
            name: Arc::from(name),
            sort: VarSort::Bool,
            domain_keys: None,
        }),
        // Homogeneous Int sets and others - leave as default Int
        _ => None,
    }
}

/// Infer a VarInfo from the resolved RHS of an `x \in S` expression.
/// Handles BOOLEAN, FuncSet, SetFilter, and SetEnum patterns.
fn infer_var_info_from_membership(
    name: &str,
    resolved_rhs: &Expr,
    constant_defs: &HashMap<String, Spanned<Expr>>,
) -> Option<VarInfo> {
    match resolved_rhs {
        Expr::Ident(set_name, _) if set_name == "BOOLEAN" => Some(VarInfo {
            name: Arc::from(name),
            sort: VarSort::Bool,
            domain_keys: None,
        }),
        // x \in [D -> R] -> Function type
        Expr::FuncSet(domain, range) => {
            let domain_keys = extract_finite_domain(&domain.node)?;
            let range_sort = infer_sort_from_set(&range.node);
            Some(VarInfo {
                name: Arc::from(name),
                sort: VarSort::Function {
                    domain_keys: domain_keys.clone(),
                    range: Box::new(range_sort),
                },
                domain_keys: Some(domain_keys),
            })
        }
        // Part of #515: x \in { y \in S : P(y) } -> infer type from S
        Expr::SetFilter(bound, _pred) => {
            let domain = bound.domain.as_ref()?;
            let resolved_domain = resolve_through_constants(&domain.node, constant_defs);
            if let Expr::SetEnum(elements) = resolved_domain {
                infer_var_info_from_set_enum(name, elements)
            } else {
                None
            }
        }
        // x \in {"a", "b", "c"} -> String with domain
        // x \in {<<1,2>>, <<3,4>>} -> Tuple with element sorts
        // x \in {1, "a"} -> Heterogeneous (Part of #523)
        Expr::SetEnum(elements) => infer_var_info_from_set_enum(name, elements),
        _ => None,
    }
}

fn infer_types_from_expr(
    expr: &Expr,
    vars: &[Arc<str>],
    var_infos: &mut HashMap<String, VarInfo>,
    constant_defs: &HashMap<String, Spanned<Expr>>,
) {
    match expr {
        // x \in BOOLEAN -> Bool
        // x \in {"a", "b"} -> String
        // x \in ConstantName -> resolve and recurse
        // Part of #532: Handle StateVar in addition to Ident for end-to-end parsing
        Expr::In(lhs, rhs) => {
            if let Some(name) = extract_var_name(&lhs.node) {
                if vars.iter().any(|v| v.as_ref() == name.as_str()) {
                    // Part of #515: Resolve the RHS through constants (handles
                    // `t \in Arrangements` where Arrangements is pre-evaluated).
                    let resolved_rhs = resolve_through_constants(&rhs.node, constant_defs);
                    if let Some(info) =
                        infer_var_info_from_membership(&name, resolved_rhs, constant_defs)
                    {
                        var_infos.insert(name, info);
                    }
                }
            }
            infer_types_from_expr(&lhs.node, vars, var_infos, constant_defs);
            infer_types_from_expr(&rhs.node, vars, var_infos, constant_defs);
        }

        // x = TRUE or x = FALSE -> Bool
        // Part of #532: Handle StateVar in addition to Ident for end-to-end parsing
        Expr::Eq(lhs, rhs) => {
            if let Some(name) = extract_var_name(&lhs.node) {
                if vars.iter().any(|v| v.as_ref() == name.as_str()) {
                    if matches!(rhs.node, Expr::Bool(_)) {
                        var_infos.insert(
                            name.clone(),
                            VarInfo {
                                name: Arc::from(name.as_str()),
                                sort: VarSort::Bool,
                                domain_keys: None,
                            },
                        );
                    }
                }
            }
            // Also check RHS = var case
            if let Some(name) = extract_var_name(&rhs.node) {
                if vars.iter().any(|v| v.as_ref() == name.as_str()) {
                    if matches!(lhs.node, Expr::Bool(_)) {
                        var_infos.insert(
                            name.clone(),
                            VarInfo {
                                name: Arc::from(name.as_str()),
                                sort: VarSort::Bool,
                                domain_keys: None,
                            },
                        );
                    }
                }
            }
            infer_types_from_expr(&lhs.node, vars, var_infos, constant_defs);
            infer_types_from_expr(&rhs.node, vars, var_infos, constant_defs);
        }

        // Recurse into subexpressions
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) => {
            infer_types_from_expr(&a.node, vars, var_infos, constant_defs);
            infer_types_from_expr(&b.node, vars, var_infos, constant_defs);
        }
        Expr::Not(a) => {
            infer_types_from_expr(&a.node, vars, var_infos, constant_defs);
        }
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bv in bounds {
                if let Some(domain) = &bv.domain {
                    infer_types_from_expr(&domain.node, vars, var_infos, constant_defs);
                }
            }
            infer_types_from_expr(&body.node, vars, var_infos, constant_defs);
        }
        _ => {}
    }
}

/// Element type tag for heterogeneity detection
/// Part of #523: detect mixed-type SetEnum
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ElemTypeTag {
    Int,
    Bool,
    String,
    Tuple,
    Other,
}

/// Get the type tag for an expression element
fn get_elem_type_tag(expr: &Expr) -> ElemTypeTag {
    match expr {
        Expr::Int(_) => ElemTypeTag::Int,
        Expr::Bool(_) => ElemTypeTag::Bool,
        Expr::String(_) => ElemTypeTag::String,
        Expr::Tuple(_) => ElemTypeTag::Tuple,
        _ => ElemTypeTag::Other,
    }
}

/// Check if a SetEnum is heterogeneous (mixed types)
/// Returns Some(reason) if heterogeneous, None if homogeneous
/// Part of #523: soundness fix
fn check_heterogeneous_set_enum(elements: &[Spanned<Expr>]) -> Option<String> {
    if elements.is_empty() {
        return None;
    }

    let first_tag = get_elem_type_tag(&elements[0].node);

    for (i, elem) in elements.iter().enumerate().skip(1) {
        let tag = get_elem_type_tag(&elem.node);
        if tag != first_tag {
            return Some(format!(
                "set contains mixed types: element 0 is {:?}, element {} is {:?}",
                first_tag, i, tag
            ));
        }
    }

    // Also check for Other type which we can't handle
    if first_tag == ElemTypeTag::Other {
        return Some("set contains unsupported element type".to_string());
    }

    // Part of #546: Check for heterogeneous tuple arities
    // All tuples must have the same number of elements
    if first_tag == ElemTypeTag::Tuple {
        if let Expr::Tuple(first_elems) = &elements[0].node {
            let first_arity = first_elems.len();
            for (i, elem) in elements.iter().enumerate().skip(1) {
                if let Expr::Tuple(elems) = &elem.node {
                    if elems.len() != first_arity {
                        return Some(format!(
                            "set contains tuples with different arities: element 0 has {} elements, element {} has {} elements",
                            first_arity, i, elems.len()
                        ));
                    }
                }
            }
        }
    }

    None
}

/// Extract finite domain elements from a set expression
fn extract_finite_domain(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::SetEnum(elements) => {
            let mut keys = Vec::new();
            for e in elements {
                match &e.node {
                    Expr::Int(n) => keys.push(n.to_string()),
                    Expr::Bool(b) => keys.push(b.to_string()),
                    Expr::String(s) => keys.push(s.clone()),
                    Expr::Ident(name, _) => keys.push(name.clone()),
                    _ => return None, // Non-constant element
                }
            }
            Some(keys)
        }
        Expr::Range(lo, hi) => {
            // Extract integer range
            if let (Expr::Int(lo_val), Expr::Int(hi_val)) = (&lo.node, &hi.node) {
                let lo_i64: i64 = lo_val.try_into().ok()?;
                let hi_i64: i64 = hi_val.try_into().ok()?;
                if hi_i64 - lo_i64 > 1000 {
                    return None; // Too large
                }
                let keys: Vec<String> = (lo_i64..=hi_i64).map(|i| i.to_string()).collect();
                Some(keys)
            } else {
                None
            }
        }
        Expr::Ident(name, _) if name == "BOOLEAN" => {
            Some(vec!["false".to_string(), "true".to_string()])
        }
        _ => None,
    }
}

/// Infer sort from a single expression (for tuple elements)
pub(super) fn infer_sort_from_expr(expr: &Expr) -> VarSort {
    match expr {
        Expr::Bool(_) => VarSort::Bool,
        Expr::Int(_) => VarSort::Int,
        Expr::String(s) => VarSort::String {
            domain: vec![s.clone()],
        },
        Expr::Tuple(elems) => {
            let element_sorts: Vec<VarSort> = elems
                .iter()
                .map(|e| infer_sort_from_expr(&e.node))
                .collect();
            VarSort::Tuple { element_sorts }
        }
        _ => VarSort::Int, // Default to Int
    }
}

/// Infer sort from a set expression (for function ranges)
pub(super) fn infer_sort_from_set(expr: &Expr) -> VarSort {
    match expr {
        Expr::Ident(name, _) if name == "BOOLEAN" => VarSort::Bool,
        Expr::Ident(name, _) if name == "Int" || name == "Nat" => VarSort::Int,
        Expr::SetEnum(elements) if !elements.is_empty() => match &elements[0].node {
            Expr::Bool(_) => VarSort::Bool,
            Expr::String(_) => {
                // Extract string domain
                let domain: Vec<String> = elements
                    .iter()
                    .filter_map(|e| match &e.node {
                        Expr::String(s) => Some(s.clone()),
                        _ => None,
                    })
                    .collect();
                VarSort::String { domain }
            }
            Expr::Tuple(tuple_elems) => {
                // Infer element sorts from the first tuple's structure
                let element_sorts: Vec<VarSort> = tuple_elems
                    .iter()
                    .map(|e| infer_sort_from_expr(&e.node))
                    .collect();
                VarSort::Tuple { element_sorts }
            }
            _ => VarSort::Int,
        },
        Expr::Range(_, _) => VarSort::Int,
        _ => VarSort::Int, // Default to Int
    }
}
