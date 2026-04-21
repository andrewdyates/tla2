// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;

use super::ast::{CtlFormula, Formula};
use super::parse_common::{
    collect_element_children, only_element_child, parse_state_predicate, parse_until_children,
};

pub(super) fn parse_root_formula(node: &roxmltree::Node) -> Result<Formula, PnmlError> {
    let child = only_element_child(node, "formula")?;
    Ok(Formula::Ctl(parse_ctl_formula(&child)?))
}

/// Parse a CTL formula from an XML node.
///
/// Handles path quantifiers (`exists-path`, `all-paths`), temporal operators
/// (`finally`, `globally`, `next`, `until`), boolean connectives, and atoms.
pub(super) fn parse_ctl_formula(node: &roxmltree::Node) -> Result<CtlFormula, PnmlError> {
    match node.tag_name().name() {
        "exists-path" => {
            let inner = only_element_child(node, "exists-path")?;
            parse_ctl_path_temporal(&inner, false)
        }
        "all-paths" => {
            let inner = only_element_child(node, "all-paths")?;
            parse_ctl_path_temporal(&inner, true)
        }
        "conjunction" => {
            let children = collect_element_children(node, "conjunction")?;
            let parsed: Result<Vec<_>, _> = children.iter().map(|n| parse_ctl_formula(n)).collect();
            Ok(CtlFormula::And(parsed?))
        }
        "disjunction" => {
            let children = collect_element_children(node, "disjunction")?;
            let parsed: Result<Vec<_>, _> = children.iter().map(|n| parse_ctl_formula(n)).collect();
            Ok(CtlFormula::Or(parsed?))
        }
        "negation" => {
            let inner = only_element_child(node, "negation")?;
            Ok(CtlFormula::Not(Box::new(parse_ctl_formula(&inner)?)))
        }
        "integer-le" | "is-fireable" | "true" | "false" => {
            Ok(CtlFormula::Atom(parse_state_predicate(node)?))
        }
        other => Err(PnmlError::MissingElement(format!(
            "unsupported CTL formula element: {other}"
        ))),
    }
}

/// Parse the temporal operator inside a path quantifier for CTL.
fn parse_ctl_path_temporal(
    node: &roxmltree::Node,
    universal: bool,
) -> Result<CtlFormula, PnmlError> {
    match node.tag_name().name() {
        "finally" => {
            let child = only_element_child(node, "finally")?;
            let inner = parse_ctl_formula(&child)?;
            Ok(if universal {
                CtlFormula::AF(Box::new(inner))
            } else {
                CtlFormula::EF(Box::new(inner))
            })
        }
        "globally" => {
            let child = only_element_child(node, "globally")?;
            let inner = parse_ctl_formula(&child)?;
            Ok(if universal {
                CtlFormula::AG(Box::new(inner))
            } else {
                CtlFormula::EG(Box::new(inner))
            })
        }
        "next" => {
            let child = only_element_child(node, "next")?;
            let inner = parse_ctl_formula(&child)?;
            Ok(if universal {
                CtlFormula::AX(Box::new(inner))
            } else {
                CtlFormula::EX(Box::new(inner))
            })
        }
        "until" => {
            let (before_node, reach_node) = parse_until_children(node)?;
            let before = parse_ctl_formula(&before_node)?;
            let reach = parse_ctl_formula(&reach_node)?;
            Ok(if universal {
                CtlFormula::AU(Box::new(before), Box::new(reach))
            } else {
                CtlFormula::EU(Box::new(before), Box::new(reach))
            })
        }
        other => Err(PnmlError::MissingElement(format!(
            "unsupported temporal operator inside path quantifier: {other}"
        ))),
    }
}
