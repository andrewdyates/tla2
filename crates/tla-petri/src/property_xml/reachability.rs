// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;

use super::ast::{Formula, PathQuantifier, ReachabilityFormula};
use super::parse_common::{collect_named_children, only_element_child, parse_state_predicate};

pub(super) fn parse_root_formula(node: &roxmltree::Node) -> Result<Formula, PnmlError> {
    let child = only_element_child(node, "formula")?;

    match child.tag_name().name() {
        "place-bound" => {
            let places = collect_named_children(&child, "place", "place-bound")?;
            Ok(Formula::PlaceBound(places))
        }
        "exists-path" => {
            let inner = only_element_child(&child, "exists-path")?;
            if inner.tag_name().name() != "finally" {
                return Err(PnmlError::MissingElement(format!(
                    "expected <finally> inside <exists-path>, got <{}>",
                    inner.tag_name().name()
                )));
            }
            let pred_node = only_element_child(&inner, "finally")?;
            let predicate = parse_state_predicate(&pred_node)?;
            Ok(Formula::Reachability(ReachabilityFormula {
                quantifier: PathQuantifier::EF,
                predicate,
            }))
        }
        "all-paths" => {
            let inner = only_element_child(&child, "all-paths")?;
            if inner.tag_name().name() != "globally" {
                return Err(PnmlError::MissingElement(format!(
                    "expected <globally> inside <all-paths>, got <{}>",
                    inner.tag_name().name()
                )));
            }
            let pred_node = only_element_child(&inner, "globally")?;
            let predicate = parse_state_predicate(&pred_node)?;
            Ok(Formula::Reachability(ReachabilityFormula {
                quantifier: PathQuantifier::AG,
                predicate,
            }))
        }
        _ => Err(PnmlError::MissingElement(format!(
            "unsupported formula element: {}",
            child.tag_name().name()
        ))),
    }
}
