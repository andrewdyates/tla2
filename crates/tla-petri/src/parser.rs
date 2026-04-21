// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PNML XML parser for Place/Transition nets.
//!
//! Parses the PNML 2009 format into a [`PetriNet`] structure.
//! Only supports P/T nets (type `ptnet`); colored nets (`symmetricnet`)
//! are rejected with [`PnmlError::UnsupportedNetType`]. Call
//! [`crate::model::load_model_dir`] instead when the higher-level MCC loading
//! path should attempt support for the currently supported colored-net subset.
//!
//! Uses roxmltree for zero-copy read-only DOM parsing.

use std::collections::HashMap;
use std::path::Path;

use crate::error::PnmlError;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

/// Parse a PNML model from a directory containing `model.pnml`.
///
/// This is the strict low-level P/T parser. It returns
/// [`PnmlError::UnsupportedNetType`] for `symmetricnet` models; callers that
/// want the high-level MCC loader with supported colored-net unfolding should
/// use [`crate::model::load_model_dir`] instead.
pub fn parse_pnml_dir(dir: &Path) -> Result<PetriNet, PnmlError> {
    let pnml_path = dir.join("model.pnml");
    parse_pnml_file(&pnml_path)
}

/// Parse a PNML file at the given path.
pub(crate) fn parse_pnml_file(path: &Path) -> Result<PetriNet, PnmlError> {
    let content = std::fs::read_to_string(path).map_err(|e| PnmlError::Io {
        path: path.to_path_buf(),
        source: e,
    })?;
    parse_pnml(&content)
}

/// Parse PNML XML content into a PetriNet.
///
/// Three-pass approach over descendants:
/// 1. Collect places with initial markings
/// 2. Collect transitions
/// 3. Resolve arcs to place/transition indices
pub(crate) fn parse_pnml(content: &str) -> Result<PetriNet, PnmlError> {
    let doc =
        roxmltree::Document::parse(content).map_err(|e| PnmlError::XmlParse(e.to_string()))?;

    let root = doc.root_element();
    let net = root
        .children()
        .find(|n| n.has_tag_name("net"))
        .ok_or_else(|| PnmlError::MissingElement("net".into()))?;

    // Check net type — only P/T nets supported
    let net_type = net.attribute("type").unwrap_or("");
    if !net_type.contains("ptnet") {
        return Err(PnmlError::UnsupportedNetType {
            net_type: net_type.into(),
        });
    }

    let net_name = get_name_text(&net);

    let mut place_id_to_idx: HashMap<String, PlaceIdx> = HashMap::new();
    let mut places: Vec<PlaceInfo> = Vec::new();
    let mut initial_marking: Vec<u64> = Vec::new();

    let mut trans_id_to_idx: HashMap<String, TransitionIdx> = HashMap::new();
    let mut transitions: Vec<TransitionInfo> = Vec::new();

    let mut raw_arcs: Vec<(String, String, u64)> = Vec::new();

    // Single pass over all descendants — works regardless of page nesting depth
    for node in net.descendants() {
        if !node.is_element() {
            continue;
        }
        match node.tag_name().name() {
            "place" => {
                if let Some(id) = node.attribute("id") {
                    let idx = PlaceIdx(places.len() as u32);
                    place_id_to_idx.insert(id.to_string(), idx);
                    places.push(PlaceInfo {
                        id: id.to_string(),
                        name: get_name_text(&node),
                    });
                    initial_marking.push(get_initial_marking(&node));
                }
            }
            "transition" => {
                if let Some(id) = node.attribute("id") {
                    let idx = TransitionIdx(transitions.len() as u32);
                    trans_id_to_idx.insert(id.to_string(), idx);
                    transitions.push(TransitionInfo {
                        id: id.to_string(),
                        name: get_name_text(&node),
                        inputs: Vec::new(),
                        outputs: Vec::new(),
                    });
                }
            }
            "arc" => {
                if let (Some(src), Some(tgt)) = (node.attribute("source"), node.attribute("target"))
                {
                    raw_arcs.push((src.to_string(), tgt.to_string(), get_arc_weight(&node)));
                }
            }
            _ => {}
        }
    }

    // Resolve arcs to typed indices
    for (source, target, weight) in &raw_arcs {
        if let Some(&pidx) = place_id_to_idx.get(source) {
            // Place → Transition (input arc: transition consumes from place)
            if let Some(&tidx) = trans_id_to_idx.get(target) {
                transitions[tidx.0 as usize].inputs.push(Arc {
                    place: pidx,
                    weight: *weight,
                });
            } else {
                return Err(PnmlError::InvalidArc {
                    src_id: source.clone(),
                    tgt_id: target.clone(),
                    reason: "target is not a known transition".into(),
                });
            }
        } else if let Some(&tidx) = trans_id_to_idx.get(source) {
            // Transition → Place (output arc: transition produces to place)
            if let Some(&pidx) = place_id_to_idx.get(target) {
                transitions[tidx.0 as usize].outputs.push(Arc {
                    place: pidx,
                    weight: *weight,
                });
            } else {
                return Err(PnmlError::InvalidArc {
                    src_id: source.clone(),
                    tgt_id: target.clone(),
                    reason: "target is not a known place".into(),
                });
            }
        } else {
            return Err(PnmlError::InvalidArc {
                src_id: source.clone(),
                tgt_id: target.clone(),
                reason: "source is neither a known place nor transition".into(),
            });
        }
    }

    Ok(PetriNet {
        name: net_name,
        places,
        transitions,
        initial_marking,
    })
}

/// Extract `<name><text>...</text></name>` from a node.
fn get_name_text(node: &roxmltree::Node) -> Option<String> {
    node.children()
        .find(|n| n.has_tag_name("name"))
        .and_then(|name_node| {
            name_node
                .children()
                .find(|n| n.has_tag_name("text"))
                .and_then(|text_node| text_node.text().map(|t| t.to_string()))
        })
}

/// Extract initial marking from `<initialMarking><text>N</text></initialMarking>`.
/// Returns 0 if absent or unparseable.
fn get_initial_marking(node: &roxmltree::Node) -> u64 {
    node.children()
        .find(|n| n.has_tag_name("initialMarking"))
        .and_then(|m| {
            m.children()
                .find(|n| n.has_tag_name("text"))
                .and_then(|t| t.text())
        })
        .and_then(|text| text.trim().parse::<u64>().ok())
        .unwrap_or(0)
}

/// Extract arc weight from `<inscription><text>N</text></inscription>`.
/// Returns 1 if absent (default arc weight per PNML spec).
fn get_arc_weight(node: &roxmltree::Node) -> u64 {
    node.children()
        .find(|n| n.has_tag_name("inscription"))
        .and_then(|m| {
            m.children()
                .find(|n| n.has_tag_name("text"))
                .and_then(|t| t.text())
        })
        .and_then(|text| text.trim().parse::<u64>().ok())
        .unwrap_or(1)
}

#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;
