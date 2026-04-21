// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;

use super::{ColorExpr, ColorTerm, GuardExpr};

/// Parse a multiset color expression from an XML node.
///
/// Fail-closed: propagates errors from `parse_color_term` and
/// `parse_color_expr` instead of silently dropping malformed elements.
pub(super) fn parse_color_expr(node: &roxmltree::Node) -> Result<ColorExpr, PnmlError> {
    match node.tag_name().name() {
        "all" => {
            let sort_id = node
                .children()
                .find(|child| child.is_element() && child.has_tag_name("usersort"))
                .and_then(|child| child.attribute("declaration"))
                .map(str::to_string)
                .unwrap_or_default();
            Ok(ColorExpr::All { sort_id })
        }
        "numberof" => {
            let subterms: Vec<_> = node
                .children()
                .filter(|child| child.is_element() && child.has_tag_name("subterm"))
                .collect();

            if subterms.len() < 2 {
                return Err(PnmlError::MissingElement(String::from(
                    "numberof requires at least 2 subterms",
                )));
            }

            let count = subterms[0]
                .children()
                .find(|child| child.is_element())
                .and_then(|child| {
                    if child.has_tag_name("numberconstant") {
                        child
                            .attribute("value")
                            .and_then(|value| value.parse::<u64>().ok())
                    } else {
                        None
                    }
                })
                .unwrap_or(1);

            let color_node = subterms[1]
                .children()
                .find(|child| child.is_element())
                .ok_or_else(|| {
                    PnmlError::MissingElement(String::from("numberof color term element"))
                })?;
            let color = parse_color_term(&color_node)?;

            Ok(ColorExpr::NumberOf {
                count,
                color: Box::new(color),
            })
        }
        "add" => {
            let mut children = Vec::new();
            for subterm in node
                .children()
                .filter(|child| child.has_tag_name("subterm"))
            {
                if let Some(first_child) = subterm.children().find(|child| child.is_element()) {
                    children.push(parse_color_expr(&first_child)?);
                }
            }
            Ok(ColorExpr::Add(children))
        }
        _ => {
            let term = parse_color_term(node)?;
            Ok(ColorExpr::NumberOf {
                count: 1,
                color: Box::new(term),
            })
        }
    }
}

/// Parse a single color term from an XML node.
///
/// Fail-closed: unrecognized tags return `Err`, not silently `None`.
pub(super) fn parse_color_term(node: &roxmltree::Node) -> Result<ColorTerm, PnmlError> {
    match node.tag_name().name() {
        "variable" => {
            let variable_id = node
                .attribute("refvariable")
                .ok_or_else(|| {
                    PnmlError::MissingElement(String::from("variable refvariable attribute"))
                })?
                .to_string();
            Ok(ColorTerm::Variable(variable_id))
        }
        "tuple" => {
            let mut terms = Vec::new();
            for subterm in node
                .children()
                .filter(|child| child.is_element() && child.has_tag_name("subterm"))
            {
                if let Some(child) = subterm
                    .children()
                    .find(|grandchild| grandchild.is_element())
                {
                    terms.push(parse_color_term(&child)?);
                }
            }
            Ok(ColorTerm::Tuple(terms))
        }
        "predecessor" => {
            let inner_node = node
                .children()
                .find(|child| child.has_tag_name("subterm"))
                .and_then(|child| child.children().find(|grandchild| grandchild.is_element()))
                .ok_or_else(|| PnmlError::MissingElement(String::from("predecessor subterm")))?;
            Ok(ColorTerm::Predecessor(Box::new(parse_color_term(
                &inner_node,
            )?)))
        }
        "successor" => {
            let inner_node = node
                .children()
                .find(|child| child.has_tag_name("subterm"))
                .and_then(|child| child.children().find(|grandchild| grandchild.is_element()))
                .ok_or_else(|| PnmlError::MissingElement(String::from("successor subterm")))?;
            Ok(ColorTerm::Successor(Box::new(parse_color_term(
                &inner_node,
            )?)))
        }
        "useroperator" => {
            let declaration = node
                .attribute("declaration")
                .ok_or_else(|| {
                    PnmlError::MissingElement(String::from("useroperator declaration attribute"))
                })?
                .to_string();
            Ok(ColorTerm::UserConstant(declaration))
        }
        "dotconstant" => Ok(ColorTerm::DotConstant),
        _ => Err(PnmlError::UnsupportedNetType {
            net_type: format!("unsupported color term: {}", node.tag_name().name()),
        }),
    }
}

/// Parse a guard expression from an XML node.
///
/// Fail-closed: unrecognized operators return `Err` instead of being
/// silently dropped. This prevents over-permissive guards in the
/// unfolded net (which would cause wrong answers).
pub(super) fn parse_guard_expr(node: &roxmltree::Node) -> Result<GuardExpr, PnmlError> {
    match node.tag_name().name() {
        "and" => {
            let mut children = Vec::new();
            for subterm in node
                .children()
                .filter(|child| child.has_tag_name("subterm"))
            {
                if let Some(first_child) = subterm.children().find(|child| child.is_element()) {
                    children.push(parse_guard_expr(&first_child)?);
                }
            }
            Ok(GuardExpr::And(children))
        }
        "or" => {
            let mut children = Vec::new();
            for subterm in node
                .children()
                .filter(|child| child.has_tag_name("subterm"))
            {
                if let Some(first_child) = subterm.children().find(|child| child.is_element()) {
                    children.push(parse_guard_expr(&first_child)?);
                }
            }
            Ok(GuardExpr::Or(children))
        }
        "not" => {
            let inner_node = node
                .children()
                .find(|child| child.has_tag_name("subterm"))
                .and_then(|child| child.children().find(|grandchild| grandchild.is_element()))
                .ok_or_else(|| PnmlError::MissingElement(String::from("not guard subterm")))?;
            Ok(GuardExpr::Not(Box::new(parse_guard_expr(&inner_node)?)))
        }
        "equality" | "inequality" | "lessthan" | "lessthanorequal" | "greaterthan"
        | "greaterthanorequal" => {
            let tag = node.tag_name().name();
            let subterms: Vec<_> = node
                .children()
                .filter(|child| child.has_tag_name("subterm"))
                .collect();
            if subterms.len() < 2 {
                return Err(PnmlError::MissingElement(format!(
                    "{tag} guard requires 2 subterms, got {}",
                    subterms.len()
                )));
            }
            let lhs_node = subterms[0]
                .children()
                .find(|child| child.is_element())
                .ok_or_else(|| PnmlError::MissingElement(format!("{tag} guard LHS element")))?;
            let rhs_node = subterms[1]
                .children()
                .find(|child| child.is_element())
                .ok_or_else(|| PnmlError::MissingElement(format!("{tag} guard RHS element")))?;
            let lhs = Box::new(parse_color_term(&lhs_node)?);
            let rhs = Box::new(parse_color_term(&rhs_node)?);
            match tag {
                "equality" => Ok(GuardExpr::Equality(lhs, rhs)),
                "inequality" => Ok(GuardExpr::Inequality(lhs, rhs)),
                "lessthan" => Ok(GuardExpr::LessThan(lhs, rhs)),
                "lessthanorequal" => Ok(GuardExpr::LessThanOrEqual(lhs, rhs)),
                "greaterthan" => Ok(GuardExpr::GreaterThan(lhs, rhs)),
                "greaterthanorequal" => Ok(GuardExpr::GreaterThanOrEqual(lhs, rhs)),
                _ => unreachable!(),
            }
        }
        "booleanconstant" if node.attribute("value") == Some("true") => Ok(GuardExpr::True),
        "true" => Ok(GuardExpr::True),
        _ => Err(PnmlError::UnsupportedNetType {
            net_type: format!("unsupported guard operator: {}", node.tag_name().name()),
        }),
    }
}
