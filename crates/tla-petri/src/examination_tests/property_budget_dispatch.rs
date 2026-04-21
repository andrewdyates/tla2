// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-examination dispatch smoke tests for property-driven MCC examinations.
//!
//! Each test fires one small deterministic property under a sufficient budget and
//! asserts a definitive verdict. The only question this file answers is:
//!
//!   "Does the property-driven dispatch path still execute each examination on a
//!    small deterministic fixture?"
//!
//! Tight-budget (CannotCompute) semantics are owned by the examination-native
//! test modules:
//!   - upper bounds: `examinations/upper_bounds/tests/exactness.rs`
//!   - reachability: `examinations/reachability_tests.rs`
//!   - CTL: `examinations/ctl/tests.rs`
//!   - LTL: `examinations/ltl_tests.rs` and `model_ltl_budget_tests.rs`

use crate::examinations::ctl::check_ctl_properties;
use crate::examinations::ltl::check_ltl_properties;
use crate::examinations::reachability::check_reachability_properties;
use crate::examinations::upper_bounds::check_upper_bounds_properties;
use crate::explorer::ExplorationConfig;
use crate::output::Verdict;
use crate::property_xml::{
    CtlFormula, Formula, LtlFormula, PathQuantifier, Property, ReachabilityFormula, StatePredicate,
};

use super::fixtures::{cyclic_safe_net, linear_deadlock_net};

fn make_ag_prop(id: &str, pred: StatePredicate) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Reachability(ReachabilityFormula {
            quantifier: PathQuantifier::AG,
            predicate: pred,
        }),
    }
}

#[test]
fn test_upper_bounds_dispatch_smoke_resolves() {
    let props = vec![Property {
        id: "smoke-upper-bounds".to_string(),
        formula: Formula::PlaceBound(vec!["P1".to_string()]),
    }];
    let results =
        check_upper_bounds_properties(&linear_deadlock_net(), &props, &ExplorationConfig::new(2));
    assert_eq!(results, vec![(String::from("smoke-upper-bounds"), Some(1))]);
}

#[test]
fn test_reachability_dispatch_smoke_resolves() {
    let pred = StatePredicate::Or(vec![
        StatePredicate::IsFireable(vec!["T0".to_string()]),
        StatePredicate::IsFireable(vec!["T1".to_string()]),
    ]);
    let props = vec![make_ag_prop("smoke-reachability", pred)];
    let results =
        check_reachability_properties(&cyclic_safe_net(), &props, &ExplorationConfig::new(2));
    assert_eq!(
        results,
        vec![(String::from("smoke-reachability"), Verdict::True)]
    );
}

#[test]
fn test_ctl_dispatch_smoke_resolves() {
    let ctl_always_some_fireable = CtlFormula::AG(Box::new(CtlFormula::Or(vec![
        CtlFormula::Atom(StatePredicate::IsFireable(vec!["T0".to_string()])),
        CtlFormula::Atom(StatePredicate::IsFireable(vec!["T1".to_string()])),
    ])));
    let props = vec![Property {
        id: "smoke-ctl".to_string(),
        formula: Formula::Ctl(ctl_always_some_fireable),
    }];
    let results = check_ctl_properties(&cyclic_safe_net(), &props, &ExplorationConfig::new(2));
    assert_eq!(results, vec![(String::from("smoke-ctl"), Verdict::True)]);
}

#[test]
fn test_ltl_dispatch_smoke_resolves() {
    let props = vec![Property {
        id: "smoke-ltl".to_string(),
        formula: Formula::Ltl(LtlFormula::Next(Box::new(LtlFormula::Atom(
            StatePredicate::IsFireable(vec!["T1".to_string()]),
        )))),
    }];
    let results = check_ltl_properties(&cyclic_safe_net(), &props, &ExplorationConfig::new(2));
    assert_eq!(results, vec![(String::from("smoke-ltl"), Verdict::True)]);
}
