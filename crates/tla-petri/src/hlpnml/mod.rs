// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! HLPNML parser for colored (symmetric) Petri net PNML.
//!
//! Parses the PNML 2009 symmetric net format into a [`ColoredNet`] IR
//! that can be unfolded into a standard P/T net by [`crate::unfold`].
//!
//! Phase 2: handles `cyclicenumeration`, `finiteenumeration`, and
//! `productsort` over those base sorts.

use std::path::Path;

use crate::error::PnmlError;

pub(crate) mod ast;
mod declarations;
mod expr;
mod net;

pub(crate) use self::ast::{
    ColorConstant, ColorExpr, ColorSort, ColorTerm, ColoredArc, ColoredNet, ColoredPlace,
    ColoredTransition, GuardExpr, VariableDecl,
};

/// Parse a colored net from a model directory.
pub(crate) fn parse_hlpnml_dir(dir: &Path) -> Result<ColoredNet, PnmlError> {
    let pnml_path = dir.join("model.pnml");
    let content = std::fs::read_to_string(&pnml_path).map_err(|source| PnmlError::Io {
        path: pnml_path.clone(),
        source,
    })?;
    parse_hlpnml(&content)
}

/// Parse HLPNML XML content into a [`ColoredNet`].
pub(crate) fn parse_hlpnml(content: &str) -> Result<ColoredNet, PnmlError> {
    let doc =
        roxmltree::Document::parse(content).map_err(|e| PnmlError::XmlParse(e.to_string()))?;

    let root = doc.root_element();
    let net = root
        .children()
        .find(|node| node.has_tag_name("net"))
        .ok_or_else(|| PnmlError::MissingElement(String::from("net")))?;

    let net_name = net::get_name_text(&net);
    let (sorts, variables) = declarations::parse_declarations(&net)?;
    let (places, transitions, arcs) = parse_net_nodes(&net)?;

    Ok(ColoredNet {
        name: net_name,
        sorts,
        variables,
        places,
        transitions,
        arcs,
    })
}

fn parse_net_nodes(
    net: &roxmltree::Node,
) -> Result<(Vec<ColoredPlace>, Vec<ColoredTransition>, Vec<ColoredArc>), PnmlError> {
    let mut places = Vec::new();
    let mut transitions = Vec::new();
    let mut arcs = Vec::new();

    for node in net.descendants() {
        if !node.is_element() {
            continue;
        }
        match node.tag_name().name() {
            "place" => {
                if let Some(place) = net::parse_colored_place(&node)? {
                    places.push(place);
                }
            }
            "transition" => {
                if let Some(transition) = net::parse_colored_transition(&node)? {
                    transitions.push(transition);
                }
            }
            "arc" => {
                if let Some(arc) = net::parse_colored_arc(&node)? {
                    arcs.push(arc);
                }
            }
            _ => {}
        }
    }

    Ok((places, transitions, arcs))
}

#[cfg(test)]
#[path = "../hlpnml_tests.rs"]
mod tests;
