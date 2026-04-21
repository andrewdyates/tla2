// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;

use super::{
    expr::{parse_color_expr, parse_guard_expr},
    ColorExpr, ColorTerm, ColoredArc, ColoredPlace, ColoredTransition,
};

/// Parse a `<place>` element with HLPNML type and initial marking.
pub(super) fn parse_colored_place(
    node: &roxmltree::Node,
) -> Result<Option<ColoredPlace>, PnmlError> {
    let id = match node.attribute("id") {
        Some(id) => id.to_string(),
        None => return Ok(None),
    };
    let name = get_name_text(node);

    let sort_id = node
        .children()
        .find(|child| child.has_tag_name("type"))
        .and_then(|type_node| {
            type_node
                .descendants()
                .find(|descendant| descendant.is_element() && descendant.has_tag_name("usersort"))
        })
        .and_then(|usersort| usersort.attribute("declaration"))
        .map(str::to_string)
        .unwrap_or_default();

    let marking_expr_node = node
        .children()
        .find(|child| child.has_tag_name("hlinitialMarking"))
        .and_then(|marking_node| {
            marking_node
                .children()
                .find(|child| child.has_tag_name("structure"))
        })
        .and_then(|structure| structure.children().find(|child| child.is_element()));
    let initial_marking = match marking_expr_node {
        Some(expr_node) => Some(parse_color_expr(&expr_node)?),
        None => None,
    };

    Ok(Some(ColoredPlace {
        id,
        name,
        sort_id,
        initial_marking,
    }))
}

/// Parse a `<transition>` element with optional guard.
pub(super) fn parse_colored_transition(
    node: &roxmltree::Node,
) -> Result<Option<ColoredTransition>, PnmlError> {
    let id = match node.attribute("id") {
        Some(id) => id.to_string(),
        None => return Ok(None),
    };
    let name = get_name_text(node);

    let guard_node = node
        .children()
        .find(|child| child.has_tag_name("condition"))
        .and_then(|condition_node| {
            condition_node
                .children()
                .find(|child| child.has_tag_name("structure"))
        })
        .and_then(|structure| structure.children().find(|child| child.is_element()));
    let guard = match guard_node {
        Some(expr_node) => Some(parse_guard_expr(&expr_node)?),
        None => None,
    };

    Ok(Some(ColoredTransition { id, name, guard }))
}

/// Parse an `<arc>` element with HLPNML inscription.
pub(super) fn parse_colored_arc(node: &roxmltree::Node) -> Result<Option<ColoredArc>, PnmlError> {
    let id = node.attribute("id").unwrap_or("").to_string();
    let source = match node.attribute("source") {
        Some(source) => source.to_string(),
        None => return Ok(None),
    };
    let target = match node.attribute("target") {
        Some(target) => target.to_string(),
        None => return Ok(None),
    };

    let inscription_node = node
        .children()
        .find(|child| child.has_tag_name("hlinscription"))
        .and_then(|inscription_node| {
            inscription_node
                .children()
                .find(|child| child.has_tag_name("structure"))
        })
        .and_then(|structure| structure.children().find(|child| child.is_element()));
    let inscription = match inscription_node {
        Some(expr_node) => parse_color_expr(&expr_node)?,
        None => ColorExpr::NumberOf {
            count: 1,
            color: Box::new(ColorTerm::DotConstant),
        },
    };

    Ok(Some(ColoredArc {
        id,
        source,
        target,
        inscription,
    }))
}

/// Extract `<name><text>...</text></name>` from a node.
pub(super) fn get_name_text(node: &roxmltree::Node) -> Option<String> {
    node.children()
        .find(|child| child.has_tag_name("name"))
        .and_then(|name_node| {
            name_node
                .children()
                .find(|child| child.has_tag_name("text"))
                .and_then(|text_node| text_node.text().map(str::to_string))
        })
}
