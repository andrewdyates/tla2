// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;

use super::{ColorConstant, ColorSort, VariableDecl};

/// Parse `<declaration><structure><declarations>` block.
pub(super) fn parse_declarations(
    net: &roxmltree::Node,
) -> Result<(Vec<ColorSort>, Vec<VariableDecl>), PnmlError> {
    let mut sorts = Vec::new();
    let mut variables = Vec::new();

    let declarations_node = net
        .descendants()
        .find(|node| node.has_tag_name("declarations"));
    let declarations_node = match declarations_node {
        Some(node) => node,
        None => return Ok((sorts, variables)),
    };

    for child in declarations_node.children() {
        if !child.is_element() {
            continue;
        }
        match child.tag_name().name() {
            "namedsort" => {
                if let Some(sort) = parse_named_sort(&child)? {
                    sorts.push(sort);
                }
            }
            "variabledecl" => {
                if let Some(variable) = parse_variable_decl(&child) {
                    variables.push(variable);
                }
            }
            _ => {}
        }
    }

    Ok((sorts, variables))
}

fn parse_named_sort(node: &roxmltree::Node) -> Result<Option<ColorSort>, PnmlError> {
    let id = match node.attribute("id") {
        Some(id) => id.to_string(),
        None => return Ok(None),
    };
    let name = node.attribute("name").unwrap_or(&id).to_string();

    for child in node.children() {
        if !child.is_element() {
            continue;
        }
        match child.tag_name().name() {
            "dot" => return Ok(Some(ColorSort::Dot { id, name })),
            "cyclicenumeration" | "finiteenumeration" => {
                let mut constants = Vec::new();
                for constant_node in child.children() {
                    if constant_node.is_element() && constant_node.has_tag_name("feconstant") {
                        if let Some(constant_id) = constant_node.attribute("id") {
                            let constant_name = constant_node
                                .attribute("name")
                                .unwrap_or(constant_id)
                                .to_string();
                            constants.push(ColorConstant {
                                id: constant_id.to_string(),
                                name: constant_name,
                            });
                        }
                    }
                }
                return Ok(Some(ColorSort::CyclicEnum {
                    id,
                    name,
                    constants,
                }));
            }
            "productsort" => {
                let components = child
                    .children()
                    .filter(|component| {
                        component.is_element() && component.has_tag_name("usersort")
                    })
                    .filter_map(|component| component.attribute("declaration").map(str::to_string))
                    .collect();
                return Ok(Some(ColorSort::Product {
                    id,
                    name,
                    components,
                }));
            }
            _ => {
                return Err(PnmlError::UnsupportedNetType {
                    net_type: format!("unsupported color sort: {}", child.tag_name().name()),
                });
            }
        }
    }

    Ok(None)
}

fn parse_variable_decl(node: &roxmltree::Node) -> Option<VariableDecl> {
    let id = node.attribute("id")?.to_string();
    let name = node.attribute("name").unwrap_or(&id).to_string();
    let sort_id = node
        .children()
        .find(|child| child.is_element() && child.has_tag_name("usersort"))
        .and_then(|child| child.attribute("declaration"))
        .map(str::to_string)?;

    Some(VariableDecl { id, name, sort_id })
}
