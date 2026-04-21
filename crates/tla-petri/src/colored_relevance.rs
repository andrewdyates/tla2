// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-driven relevance reduction for colored Petri nets.
//!
//! Removes places and transitions that cannot affect the query formula
//! via backward closure on the `ColoredNet` graph. Applied *before*
//! unfolding so that irrelevant color domains are never expanded.
//!
//! Algorithm:
//! 1. Extract place/transition name references from the formula
//! 2. Backward closure: seed referenced places/transitions, then
//!    iteratively add input places of added transitions and
//!    transitions that output to added places, until fixpoint
//! 3. Remove all places and transitions NOT in the closure
//!
//! Part of #1438 (colored reduction Tier 1).

use std::collections::HashSet;

use crate::hlpnml::{ColoredArc, ColoredNet};
use crate::property_xml::{CtlFormula, Formula, IntExpr, LtlFormula, StatePredicate};

/// References extracted from a formula: place names and transition names.
#[derive(Debug, Default)]
pub(crate) struct FormulaRefs {
    pub places: HashSet<String>,
    pub transitions: HashSet<String>,
}

/// Extract all place and transition name references from a formula.
pub(crate) fn extract_refs(formula: &Formula) -> FormulaRefs {
    let mut refs = FormulaRefs::default();
    match formula {
        Formula::PlaceBound(names) => {
            refs.places.extend(names.iter().cloned());
        }
        Formula::Reachability(rf) => extract_state_pred_refs(&rf.predicate, &mut refs),
        Formula::Ctl(cf) => extract_ctl_refs(cf, &mut refs),
        Formula::Ltl(lf) => extract_ltl_refs(lf, &mut refs),
    }
    refs
}

fn extract_state_pred_refs(pred: &StatePredicate, refs: &mut FormulaRefs) {
    match pred {
        StatePredicate::And(children) | StatePredicate::Or(children) => {
            for child in children {
                extract_state_pred_refs(child, refs);
            }
        }
        StatePredicate::Not(inner) => extract_state_pred_refs(inner, refs),
        StatePredicate::IntLe(left, right) => {
            extract_int_expr_refs(left, refs);
            extract_int_expr_refs(right, refs);
        }
        StatePredicate::IsFireable(names) => {
            refs.transitions.extend(names.iter().cloned());
        }
        StatePredicate::True | StatePredicate::False => {}
    }
}

fn extract_int_expr_refs(expr: &IntExpr, refs: &mut FormulaRefs) {
    match expr {
        IntExpr::Constant(_) => {}
        IntExpr::TokensCount(names) => {
            refs.places.extend(names.iter().cloned());
        }
    }
}

fn extract_ctl_refs(formula: &CtlFormula, refs: &mut FormulaRefs) {
    match formula {
        CtlFormula::Atom(pred) => extract_state_pred_refs(pred, refs),
        CtlFormula::Not(inner) => extract_ctl_refs(inner, refs),
        CtlFormula::And(children) | CtlFormula::Or(children) => {
            for child in children {
                extract_ctl_refs(child, refs);
            }
        }
        CtlFormula::EX(f)
        | CtlFormula::AX(f)
        | CtlFormula::EF(f)
        | CtlFormula::AF(f)
        | CtlFormula::EG(f)
        | CtlFormula::AG(f) => extract_ctl_refs(f, refs),
        CtlFormula::EU(f1, f2) | CtlFormula::AU(f1, f2) => {
            extract_ctl_refs(f1, refs);
            extract_ctl_refs(f2, refs);
        }
    }
}

fn extract_ltl_refs(formula: &LtlFormula, refs: &mut FormulaRefs) {
    match formula {
        LtlFormula::Atom(pred) => extract_state_pred_refs(pred, refs),
        LtlFormula::Not(inner) => extract_ltl_refs(inner, refs),
        LtlFormula::And(children) | LtlFormula::Or(children) => {
            for child in children {
                extract_ltl_refs(child, refs);
            }
        }
        LtlFormula::Next(f) | LtlFormula::Finally(f) | LtlFormula::Globally(f) => {
            extract_ltl_refs(f, refs)
        }
        LtlFormula::Until(f1, f2) => {
            extract_ltl_refs(f1, refs);
            extract_ltl_refs(f2, refs);
        }
    }
}

/// Apply query-driven relevance reduction to a colored net.
///
/// Keeps only places and transitions reachable via backward closure
/// from the formula-referenced places/transitions. Returns the number
/// of places removed.
pub(crate) fn reduce(net: &mut ColoredNet, formula: &Formula) -> RelevanceReport {
    let refs = extract_refs(formula);

    // If the formula references nothing (e.g., constants), keep everything.
    if refs.places.is_empty() && refs.transitions.is_empty() {
        return RelevanceReport::default();
    }

    // Build place-id and transition-id lookup sets.
    let place_id_set: HashSet<&str> = net.places.iter().map(|p| p.id.as_str()).collect();
    let trans_id_set: HashSet<&str> = net.transitions.iter().map(|t| t.id.as_str()).collect();

    // Seed the closure with formula-referenced elements.
    // Match by both id and name fields.
    let mut kept_places: HashSet<String> = HashSet::new();
    let mut kept_transitions: HashSet<String> = HashSet::new();

    for name in &refs.places {
        if place_id_set.contains(name.as_str()) {
            kept_places.insert(name.clone());
        } else {
            // Try matching by name field.
            for p in &net.places {
                if p.name.as_deref() == Some(name.as_str()) {
                    kept_places.insert(p.id.clone());
                }
            }
        }
    }

    for name in &refs.transitions {
        if trans_id_set.contains(name.as_str()) {
            kept_transitions.insert(name.clone());
            // For fireable transitions, also seed their input places.
            add_input_places_of_transition(name, &net.arcs, &mut kept_places);
        } else {
            // Try matching by name field.
            for t in &net.transitions {
                if t.name.as_deref() == Some(name.as_str()) {
                    kept_transitions.insert(t.id.clone());
                    add_input_places_of_transition(&t.id, &net.arcs, &mut kept_places);
                }
            }
        }
    }

    // Backward closure to fixpoint.
    loop {
        let prev_places = kept_places.len();
        let prev_trans = kept_transitions.len();

        // For each kept place, add all transitions that have an arc TO this place.
        for arc in &net.arcs {
            if kept_places.contains(&arc.target)
                && trans_id_set.contains(arc.source.as_str())
                && !kept_transitions.contains(&arc.source)
            {
                kept_transitions.insert(arc.source.clone());
            }
        }

        // For each kept transition, add all its input places.
        for arc in &net.arcs {
            if kept_transitions.contains(&arc.target)
                && place_id_set.contains(arc.source.as_str())
                && !kept_places.contains(&arc.source)
            {
                kept_places.insert(arc.source.clone());
            }
        }

        if kept_places.len() == prev_places && kept_transitions.len() == prev_trans {
            break;
        }
    }

    let orig_places = net.places.len();
    let orig_transitions = net.transitions.len();

    // Remove unreferenced elements.
    net.places.retain(|p| kept_places.contains(&p.id));
    net.transitions.retain(|t| kept_transitions.contains(&t.id));
    net.arcs.retain(|a| {
        let src_ok = kept_places.contains(&a.source) || kept_transitions.contains(&a.source);
        let tgt_ok = kept_places.contains(&a.target) || kept_transitions.contains(&a.target);
        src_ok && tgt_ok
    });

    RelevanceReport {
        places_removed: orig_places - net.places.len(),
        transitions_removed: orig_transitions - net.transitions.len(),
    }
}

fn add_input_places_of_transition(
    trans_id: &str,
    arcs: &[ColoredArc],
    kept_places: &mut HashSet<String>,
) {
    for arc in arcs {
        if arc.target == trans_id {
            kept_places.insert(arc.source.clone());
        }
    }
}

/// Report from relevance reduction.
#[derive(Debug, Default)]
pub(crate) struct RelevanceReport {
    pub places_removed: usize,
    pub transitions_removed: usize,
}

impl RelevanceReport {
    pub(crate) fn is_reduction(&self) -> bool {
        self.places_removed > 0 || self.transitions_removed > 0
    }
}
