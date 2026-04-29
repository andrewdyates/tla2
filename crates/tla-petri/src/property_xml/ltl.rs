// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;

use super::ast::{Formula, LtlFormula};
use super::parse_common::{
    collect_element_children, only_element_child, parse_state_predicate, parse_until_children,
};

pub(super) fn parse_root_formula(node: &roxmltree::Node) -> Result<Formula, PnmlError> {
    let child = only_element_child(node, "formula")?;
    if child.tag_name().name() != "all-paths" {
        return Err(PnmlError::MissingElement(format!(
            "LTL formula root must be <all-paths>, got <{}>",
            child.tag_name().name()
        )));
    }

    let inner = only_element_child(&child, "all-paths")?;
    Ok(Formula::Ltl(parse_ltl_formula(&inner)?))
}

/// Parse an LTL formula from an XML node (inside the root `<all-paths>`).
pub(super) fn parse_ltl_formula(node: &roxmltree::Node) -> Result<LtlFormula, PnmlError> {
    match node.tag_name().name() {
        "finally" => {
            let child = only_element_child(node, "finally")?;
            Ok(LtlFormula::Finally(Box::new(parse_ltl_formula(&child)?)))
        }
        "globally" => {
            let child = only_element_child(node, "globally")?;
            Ok(LtlFormula::Globally(Box::new(parse_ltl_formula(&child)?)))
        }
        "next" => {
            let child = only_element_child(node, "next")?;
            Ok(LtlFormula::Next(Box::new(parse_ltl_formula(&child)?)))
        }
        "until" => {
            let (before_node, reach_node) = parse_until_children(node)?;
            let before = parse_ltl_formula(&before_node)?;
            let reach = parse_ltl_formula(&reach_node)?;
            Ok(LtlFormula::Until(Box::new(before), Box::new(reach)))
        }
        "conjunction" => {
            let children = collect_element_children(node, "conjunction")?;
            let parsed: Result<Vec<_>, _> = children.iter().map(|n| parse_ltl_formula(n)).collect();
            Ok(LtlFormula::And(parsed?))
        }
        "disjunction" => {
            let children = collect_element_children(node, "disjunction")?;
            let parsed: Result<Vec<_>, _> = children.iter().map(|n| parse_ltl_formula(n)).collect();
            Ok(LtlFormula::Or(parsed?))
        }
        "negation" => {
            let inner = only_element_child(node, "negation")?;
            Ok(LtlFormula::Not(Box::new(parse_ltl_formula(&inner)?)))
        }
        "integer-le" | "is-fireable" | "true" | "false" => {
            Ok(LtlFormula::Atom(parse_state_predicate(node)?))
        }
        other => Err(PnmlError::MissingElement(format!(
            "unsupported LTL formula element: {other}"
        ))),
    }
}
