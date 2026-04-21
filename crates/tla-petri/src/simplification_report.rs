// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed report model for formula-simplification impact.

use serde::Serialize;

use crate::property_xml::{CtlFormula, Formula, IntExpr, LtlFormula, StatePredicate};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub enum SimplificationOutcome {
    Unchanged,
    Simplified,
    ResolvedTrue,
    ResolvedFalse,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct PropertySimplificationReport {
    pub property_id: String,
    pub outcome: SimplificationOutcome,
    pub original_nodes: usize,
    pub simplified_nodes: usize,
}

impl PropertySimplificationReport {
    #[must_use]
    pub(crate) fn from_formulas(
        property_id: &str,
        original: &Formula,
        simplified: &Formula,
    ) -> Self {
        Self {
            property_id: property_id.to_string(),
            outcome: classify_outcome(original, simplified),
            original_nodes: count_formula_nodes(original),
            simplified_nodes: count_formula_nodes(simplified),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct SimplificationSummary {
    pub total_properties: usize,
    pub changed_properties: usize,
    pub unchanged_properties: usize,
    pub resolved_true_properties: usize,
    pub resolved_false_properties: usize,
}

impl SimplificationSummary {
    fn from_properties(properties: &[PropertySimplificationReport]) -> Self {
        let mut unchanged_properties = 0;
        let mut resolved_true_properties = 0;
        let mut resolved_false_properties = 0;

        for property in properties {
            match property.outcome {
                SimplificationOutcome::Unchanged => unchanged_properties += 1,
                SimplificationOutcome::ResolvedTrue => resolved_true_properties += 1,
                SimplificationOutcome::ResolvedFalse => resolved_false_properties += 1,
                SimplificationOutcome::Simplified => {}
            }
        }

        let total_properties = properties.len();
        let changed_properties = total_properties.saturating_sub(unchanged_properties);

        Self {
            total_properties,
            changed_properties,
            unchanged_properties,
            resolved_true_properties,
            resolved_false_properties,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub struct SimplificationReport {
    pub properties: Vec<PropertySimplificationReport>,
    pub summary: SimplificationSummary,
}

impl SimplificationReport {
    #[must_use]
    pub(crate) fn from_properties(properties: Vec<PropertySimplificationReport>) -> Self {
        let summary = SimplificationSummary::from_properties(&properties);
        Self {
            properties,
            summary,
        }
    }
}

#[must_use]
pub(crate) fn classify_outcome(original: &Formula, simplified: &Formula) -> SimplificationOutcome {
    if original == simplified {
        return SimplificationOutcome::Unchanged;
    }

    match simplified {
        Formula::Reachability(reachability) => match &reachability.predicate {
            StatePredicate::True => SimplificationOutcome::ResolvedTrue,
            StatePredicate::False => SimplificationOutcome::ResolvedFalse,
            _ => SimplificationOutcome::Simplified,
        },
        Formula::Ctl(CtlFormula::Atom(StatePredicate::True))
        | Formula::Ltl(LtlFormula::Atom(StatePredicate::True)) => {
            SimplificationOutcome::ResolvedTrue
        }
        Formula::Ctl(CtlFormula::Atom(StatePredicate::False))
        | Formula::Ltl(LtlFormula::Atom(StatePredicate::False)) => {
            SimplificationOutcome::ResolvedFalse
        }
        _ => SimplificationOutcome::Simplified,
    }
}

fn count_formula_nodes(formula: &Formula) -> usize {
    match formula {
        Formula::PlaceBound(_) => 1,
        Formula::Reachability(reachability) => {
            1 + count_state_predicate_nodes(&reachability.predicate)
        }
        Formula::Ctl(ctl) => count_ctl_nodes(ctl),
        Formula::Ltl(ltl) => count_ltl_nodes(ltl),
    }
}

fn count_state_predicate_nodes(predicate: &StatePredicate) -> usize {
    match predicate {
        StatePredicate::And(children) | StatePredicate::Or(children) => {
            1 + children
                .iter()
                .map(count_state_predicate_nodes)
                .sum::<usize>()
        }
        StatePredicate::Not(inner) => 1 + count_state_predicate_nodes(inner),
        StatePredicate::IntLe(left, right) => {
            1 + count_int_expr_nodes(left) + count_int_expr_nodes(right)
        }
        StatePredicate::IsFireable(_) | StatePredicate::True | StatePredicate::False => 1,
    }
}

fn count_int_expr_nodes(expr: &IntExpr) -> usize {
    match expr {
        IntExpr::Constant(_) | IntExpr::TokensCount(_) => 1,
    }
}

fn count_ctl_nodes(formula: &CtlFormula) -> usize {
    match formula {
        CtlFormula::Atom(predicate) => 1 + count_state_predicate_nodes(predicate),
        CtlFormula::Not(inner)
        | CtlFormula::EX(inner)
        | CtlFormula::AX(inner)
        | CtlFormula::EF(inner)
        | CtlFormula::AF(inner)
        | CtlFormula::EG(inner)
        | CtlFormula::AG(inner) => 1 + count_ctl_nodes(inner),
        CtlFormula::And(children) | CtlFormula::Or(children) => {
            1 + children.iter().map(count_ctl_nodes).sum::<usize>()
        }
        CtlFormula::EU(left, right) | CtlFormula::AU(left, right) => {
            1 + count_ctl_nodes(left) + count_ctl_nodes(right)
        }
    }
}

fn count_ltl_nodes(formula: &LtlFormula) -> usize {
    match formula {
        LtlFormula::Atom(predicate) => 1 + count_state_predicate_nodes(predicate),
        LtlFormula::Not(inner)
        | LtlFormula::Next(inner)
        | LtlFormula::Finally(inner)
        | LtlFormula::Globally(inner) => 1 + count_ltl_nodes(inner),
        LtlFormula::And(children) | LtlFormula::Or(children) => {
            1 + children.iter().map(count_ltl_nodes).sum::<usize>()
        }
        LtlFormula::Until(left, right) => 1 + count_ltl_nodes(left) + count_ltl_nodes(right),
    }
}

#[cfg(test)]
mod tests {
    use crate::formula_simplify::simplify_properties_with_report;
    use crate::model::PropertyAliases;
    use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
    use crate::property_xml::{
        Formula, IntExpr, PathQuantifier, Property, ReachabilityFormula, StatePredicate,
    };

    use super::SimplificationOutcome;

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    fn mutex_net() -> PetriNet {
        PetriNet {
            name: Some(String::from("mutex")),
            places: vec![place("p_free"), place("p_cs")],
            transitions: vec![
                trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        }
    }

    #[test]
    fn test_simplification_report_tracks_outcomes_and_node_counts() {
        let net = mutex_net();
        let aliases = PropertyAliases::identity(&net);
        let properties = vec![
            Property {
                id: String::from("unchanged"),
                formula: Formula::PlaceBound(vec![String::from("p_free")]),
            },
            Property {
                id: String::from("resolved-true"),
                formula: Formula::Reachability(ReachabilityFormula {
                    quantifier: PathQuantifier::AG,
                    predicate: StatePredicate::IntLe(
                        IntExpr::TokensCount(vec![String::from("p_free")]),
                        IntExpr::Constant(1),
                    ),
                }),
            },
            Property {
                id: String::from("resolved-false"),
                formula: Formula::Reachability(ReachabilityFormula {
                    quantifier: PathQuantifier::EF,
                    predicate: StatePredicate::IntLe(
                        IntExpr::Constant(2),
                        IntExpr::TokensCount(vec![String::from("p_free")]),
                    ),
                }),
            },
            Property {
                id: String::from("simplified"),
                formula: Formula::Reachability(ReachabilityFormula {
                    quantifier: PathQuantifier::EF,
                    predicate: StatePredicate::And(vec![
                        StatePredicate::True,
                        StatePredicate::IsFireable(vec![String::from("t_enter")]),
                    ]),
                }),
            },
        ];

        let run = simplify_properties_with_report(&net, &properties, &aliases);
        let report = run.report;

        assert_eq!(report.summary.total_properties, 4);
        assert_eq!(report.summary.changed_properties, 3);
        assert_eq!(report.summary.unchanged_properties, 1);
        assert_eq!(report.summary.resolved_true_properties, 1);
        assert_eq!(report.summary.resolved_false_properties, 1);

        assert_eq!(
            report.properties[0].outcome,
            SimplificationOutcome::Unchanged
        );
        assert_eq!(
            report.properties[1].outcome,
            SimplificationOutcome::ResolvedTrue
        );
        assert_eq!(
            report.properties[2].outcome,
            SimplificationOutcome::ResolvedFalse
        );
        assert_eq!(
            report.properties[3].outcome,
            SimplificationOutcome::Simplified
        );

        for property in &report.properties[1..] {
            assert!(
                property.simplified_nodes < property.original_nodes,
                "changed property should shrink: {property:?}"
            );
        }
    }
}
