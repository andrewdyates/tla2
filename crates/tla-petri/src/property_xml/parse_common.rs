// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;

use super::ast::{Formula, IntExpr, Property, StatePredicate};

pub(super) fn parse_property_set<'a, 'input, F>(
    root: roxmltree::Node<'a, 'input>,
    mut parse_formula: F,
) -> Result<Vec<Property>, PnmlError>
where
    F: FnMut(&roxmltree::Node<'a, 'input>) -> Result<Formula, PnmlError>,
{
    // Validate the root element is <property-set>.
    if root.tag_name().name() != "property-set" {
        return Err(PnmlError::MissingElement(format!(
            "expected <property-set> root, got <{}>",
            root.tag_name().name()
        )));
    }

    let mut properties = Vec::new();

    for prop_node in root.children().filter(|n| n.has_tag_name("property")) {
        let id_node = only_named_child(&prop_node, "id", "property")?;
        let id = id_node
            .text()
            .ok_or_else(|| PnmlError::MissingElement("property/id".into()))?
            .to_string();

        let formula_node = only_named_child(&prop_node, "formula", "property")?;

        let formula = parse_formula(&formula_node)?;
        properties.push(Property { id, formula });
    }

    // Reject empty property documents so examination runners cannot silently
    // drop an entire examination.
    if properties.is_empty() {
        return Err(PnmlError::MissingElement(
            "property-set: missing <property>".into(),
        ));
    }

    Ok(properties)
}

/// Require exactly one element child, rejecting zero or multiple children.
pub(super) fn only_element_child<'a, 'input>(
    node: &roxmltree::Node<'a, 'input>,
    context: &'static str,
) -> Result<roxmltree::Node<'a, 'input>, PnmlError> {
    let mut elems = node.children().filter(|n| n.is_element());
    let first = elems.next().ok_or_else(|| {
        PnmlError::MissingElement(format!("{context}: expected exactly one child element"))
    })?;
    if elems.next().is_some() {
        return Err(PnmlError::MissingElement(format!(
            "{context}: expected exactly one child element"
        )));
    }
    Ok(first)
}

/// Require exactly one named child element, rejecting zero or duplicates.
pub(super) fn only_named_child<'a, 'input>(
    node: &roxmltree::Node<'a, 'input>,
    child_tag: &'static str,
    context: &'static str,
) -> Result<roxmltree::Node<'a, 'input>, PnmlError> {
    let mut matches = node.children().filter(|n| n.has_tag_name(child_tag));
    let first = matches.next().ok_or_else(|| {
        PnmlError::MissingElement(format!("{context}: expected exactly one <{child_tag}>"))
    })?;
    if matches.next().is_some() {
        return Err(PnmlError::MissingElement(format!(
            "{context}: expected exactly one <{child_tag}>"
        )));
    }
    Ok(first)
}

/// Collect named text children (e.g. `<place>` or `<transition>`) and reject
/// empty results.  The `context` string identifies the parent construct for
/// error messages.
pub(super) fn collect_named_children(
    node: &roxmltree::Node,
    child_tag: &str,
    context: &'static str,
) -> Result<Vec<String>, PnmlError> {
    let mut items = Vec::new();
    for child in node.children().filter(|n| n.has_tag_name(child_tag)) {
        let text = child.text().ok_or_else(|| {
            PnmlError::MissingElement(format!(
                "{context}: <{child_tag}> element has no text content"
            ))
        })?;
        items.push(text.to_string());
    }
    if items.is_empty() {
        return Err(PnmlError::MissingElement(format!(
            "{context}: missing <{child_tag}>"
        )));
    }
    Ok(items)
}

/// Collect element children and reject empty results.  The `context` string
/// identifies the parent construct for error messages.
pub(super) fn collect_element_children<'a, 'input>(
    node: &roxmltree::Node<'a, 'input>,
    context: &'static str,
) -> Result<Vec<roxmltree::Node<'a, 'input>>, PnmlError> {
    let children: Vec<_> = node.children().filter(|n| n.is_element()).collect();
    if children.is_empty() {
        return Err(PnmlError::MissingElement(format!(
            "{context}: missing child elements"
        )));
    }
    Ok(children)
}

/// Parse a boolean state predicate from XML.
pub(super) fn parse_state_predicate(node: &roxmltree::Node) -> Result<StatePredicate, PnmlError> {
    match node.tag_name().name() {
        "conjunction" => {
            let children = collect_element_children(node, "conjunction")?;
            let parsed: Result<Vec<_>, _> =
                children.iter().map(|n| parse_state_predicate(n)).collect();
            Ok(StatePredicate::And(parsed?))
        }
        "disjunction" => {
            let children = collect_element_children(node, "disjunction")?;
            let parsed: Result<Vec<_>, _> =
                children.iter().map(|n| parse_state_predicate(n)).collect();
            Ok(StatePredicate::Or(parsed?))
        }
        "negation" => {
            let inner = only_element_child(node, "negation")?;
            Ok(StatePredicate::Not(Box::new(parse_state_predicate(
                &inner,
            )?)))
        }
        "integer-le" => {
            let mut elems = node.children().filter(|n| n.is_element());
            let left = elems.next().ok_or_else(|| {
                PnmlError::MissingElement("integer-le: missing left operand".into())
            })?;
            let right = elems.next().ok_or_else(|| {
                PnmlError::MissingElement("integer-le: missing right operand".into())
            })?;
            if elems.next().is_some() {
                return Err(PnmlError::MissingElement(
                    "integer-le: expected exactly two operands".into(),
                ));
            }
            Ok(StatePredicate::IntLe(
                parse_int_expr(&left)?,
                parse_int_expr(&right)?,
            ))
        }
        "is-fireable" => {
            let transitions = collect_named_children(node, "transition", "is-fireable")?;
            Ok(StatePredicate::IsFireable(transitions))
        }
        "true" => Ok(StatePredicate::True),
        "false" => Ok(StatePredicate::False),
        other => Err(PnmlError::MissingElement(format!(
            "unsupported state predicate: {other}"
        ))),
    }
}

/// Parse an integer expression from XML.
pub(super) fn parse_int_expr(node: &roxmltree::Node) -> Result<IntExpr, PnmlError> {
    match node.tag_name().name() {
        "integer-constant" => {
            let text = node
                .text()
                .ok_or_else(|| PnmlError::MissingElement("integer-constant has no text".into()))?;
            let val: u64 = text.trim().parse().map_err(|_| {
                PnmlError::MissingElement(format!("invalid integer-constant: {text}"))
            })?;
            Ok(IntExpr::Constant(val))
        }
        "tokens-count" => {
            let places = collect_named_children(node, "place", "tokens-count")?;
            Ok(IntExpr::TokensCount(places))
        }
        other => Err(PnmlError::MissingElement(format!(
            "unsupported integer expression: {other}"
        ))),
    }
}

/// Extract `<before>` and `<reach>` children from an `<until>` node.
/// Rejects duplicate wrappers and multiple formulas inside each wrapper.
pub(super) fn parse_until_children<'a, 'input>(
    node: &roxmltree::Node<'a, 'input>,
) -> Result<(roxmltree::Node<'a, 'input>, roxmltree::Node<'a, 'input>), PnmlError> {
    let before = only_named_child(node, "before", "until")?;
    let reach = only_named_child(node, "reach", "until")?;
    let before_formula = only_element_child(&before, "before")?;
    let reach_formula = only_element_child(&reach, "reach")?;
    Ok((before_formula, reach_formula))
}
