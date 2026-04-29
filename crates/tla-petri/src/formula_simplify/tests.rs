// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::model::PropertyAliases;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::{
    CtlFormula, Formula, IntExpr, LtlFormula, PathQuantifier, Property, ReachabilityFormula,
    StatePredicate,
};

use super::facts::compute_facts;
use super::predicate::simplify_predicate;
use super::simplify_properties_with_aliases;
use super::temporal::simplify_formula;

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

/// Build a simple net: p0 →(1) t0 →(1) p1, p0 initial=5.
fn simple_chain_net() -> PetriNet {
    PetriNet {
        name: Some("simple-chain".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![5, 0],
    }
}

/// Mutex net: p_free ↔ p_cs (conservation: p_free + p_cs = 1).
fn mutex_net() -> PetriNet {
    PetriNet {
        name: Some("mutex".into()),
        places: vec![place("p_free"), place("p_cs")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    }
}

// ---------------------------------------------------------------------------
// Tier 1: Pure boolean folding
// ---------------------------------------------------------------------------

#[test]
fn test_boolean_fold_and_with_false_short_circuits() {
    let net = simple_chain_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::And(vec![
        StatePredicate::IntLe(IntExpr::Constant(0), IntExpr::Constant(1)),
        StatePredicate::False,
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(matches!(result, StatePredicate::False));
}

#[test]
fn test_boolean_fold_and_drops_true() {
    let net = simple_chain_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let inner = StatePredicate::IsFireable(vec!["t0".to_string()]);
    let pred = StatePredicate::And(vec![StatePredicate::True, inner.clone()]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    // Should unwrap singleton And → the inner predicate.
    assert!(matches!(result, StatePredicate::IsFireable(_)));
}

#[test]
fn test_boolean_fold_or_with_true_short_circuits() {
    let net = simple_chain_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::Or(vec![StatePredicate::False, StatePredicate::True]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(matches!(result, StatePredicate::True));
}

#[test]
fn test_boolean_fold_not_of_constant() {
    let net = simple_chain_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::Not(Box::new(StatePredicate::True));
    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(matches!(result, StatePredicate::False));

    let pred = StatePredicate::Not(Box::new(StatePredicate::False));
    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(matches!(result, StatePredicate::True));
}

#[test]
fn test_boolean_fold_double_negation() {
    let net = simple_chain_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let inner = StatePredicate::IsFireable(vec!["t0".to_string()]);
    let pred = StatePredicate::Not(Box::new(StatePredicate::Not(Box::new(inner.clone()))));

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(matches!(result, StatePredicate::IsFireable(_)));
}

// ---------------------------------------------------------------------------
// Tier 2: LP-backed proofs
// ---------------------------------------------------------------------------

#[test]
fn test_lp_proves_always_true_predicate() {
    // In the mutex net: p_free + p_cs = 1, so p_free <= 1 is always true.
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::IntLe(
        IntExpr::TokensCount(vec!["p_free".to_string()]),
        IntExpr::Constant(1),
    );

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::True),
        "LP should prove p_free <= 1 is always true; got: {result:?}"
    );
}

#[test]
fn test_lp_proves_unreachable_predicate() {
    // In the mutex net: p_free + p_cs = 1, so p_free >= 2 is unreachable.
    // Encode as: 2 <= TokensCount(p_free).
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::IntLe(
        IntExpr::Constant(2),
        IntExpr::TokensCount(vec!["p_free".to_string()]),
    );

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::False),
        "LP should prove 2 <= p_free is unreachable; got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Tier 3: Structural fireability pruning
// ---------------------------------------------------------------------------

#[test]
fn test_fireability_prune_removes_structurally_disabled_transition() {
    // t_needs_many: p0→(10) t→(10) p1.  t_cheap: p1→(1) t→(1) p0.
    // P-invariant: p0 + p1 = 1, so p0 <= 1 < 10 (t_needs_many disabled).
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_needs_many", vec![arc(0, 10)], vec![arc(1, 10)]),
            trans("t_cheap", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    // t_needs_many is structurally disabled (needs 10 from p0, bound is 1).
    assert!(facts.structurally_disabled[0]);
    assert!(!facts.structurally_disabled[1]);

    let pred = StatePredicate::IsFireable(vec!["t_needs_many".to_string(), "t_cheap".to_string()]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    match result {
        StatePredicate::IsFireable(names) => {
            assert_eq!(names, vec!["t_cheap".to_string()]);
        }
        other => panic!("expected pruned IsFireable, got: {other:?}"),
    }
}

#[test]
fn test_fireability_all_disabled_becomes_false() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t_heavy", vec![arc(0, 100)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::IsFireable(vec!["t_heavy".to_string()]);
    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::False),
        "all disabled → False; got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Tier 4: Deadlock-pattern collapse
// ---------------------------------------------------------------------------

#[test]
fn test_deadlock_collapse_in_deadlock_free_net() {
    // Mutex net is deadlock-free (free-choice, all minimal siphons contain
    // marked traps).
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);
    assert_eq!(facts.deadlock_free, Some(true));

    // Not(IsFireable(all)) = "a deadlock exists" → False.
    let pred = StatePredicate::Not(Box::new(StatePredicate::IsFireable(vec![
        "t_enter".to_string(),
        "t_exit".to_string(),
    ])));

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::False),
        "deadlock pattern in deadlock-free net → False; got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Temporal formula simplification
// ---------------------------------------------------------------------------

#[test]
fn test_reachability_ef_false_simplifies() {
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    // EF(2 <= p_free) → EF(False) because LP proves it unreachable.
    let formula = Formula::Reachability(ReachabilityFormula {
        quantifier: PathQuantifier::EF,
        predicate: StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p_free".to_string()]),
        ),
    });

    let result = simplify_formula(&formula, &net, &facts, &aliases);
    match result {
        Formula::Reachability(r) => {
            assert!(
                matches!(r.predicate, StatePredicate::False),
                "predicate should be False; got: {:?}",
                r.predicate
            );
        }
        other => panic!("expected Reachability, got: {other:?}"),
    }
}

#[test]
fn test_reachability_ag_true_simplifies() {
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    // AG(p_free <= 1) → AG(True) because LP proves it always holds.
    let formula = Formula::Reachability(ReachabilityFormula {
        quantifier: PathQuantifier::AG,
        predicate: StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p_free".to_string()]),
            IntExpr::Constant(1),
        ),
    });

    let result = simplify_formula(&formula, &net, &facts, &aliases);
    match result {
        Formula::Reachability(r) => {
            assert!(
                matches!(r.predicate, StatePredicate::True),
                "predicate should be True; got: {:?}",
                r.predicate
            );
        }
        other => panic!("expected Reachability, got: {other:?}"),
    }
}

#[test]
fn test_ctl_ef_false_folds() {
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    // EF(Atom(False)) → Atom(False).
    let ctl = CtlFormula::EF(Box::new(CtlFormula::Atom(StatePredicate::False)));
    let formula = Formula::Ctl(ctl);

    let result = simplify_formula(&formula, &net, &facts, &aliases);
    match result {
        Formula::Ctl(CtlFormula::Atom(StatePredicate::False)) => {}
        other => panic!("expected Atom(False), got: {other:?}"),
    }
}

#[test]
fn test_ctl_ag_true_folds() {
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    // AG(Atom(True)) → Atom(True).
    let ctl = CtlFormula::AG(Box::new(CtlFormula::Atom(StatePredicate::True)));
    let formula = Formula::Ctl(ctl);

    let result = simplify_formula(&formula, &net, &facts, &aliases);
    match result {
        Formula::Ctl(CtlFormula::Atom(StatePredicate::True)) => {}
        other => panic!("expected Atom(True), got: {other:?}"),
    }
}

#[test]
fn test_ltl_globally_false_folds() {
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    // G(Atom(False)) → Atom(False).
    let ltl = LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::False)));
    let formula = Formula::Ltl(ltl);

    let result = simplify_formula(&formula, &net, &facts, &aliases);
    match result {
        Formula::Ltl(LtlFormula::Atom(StatePredicate::False)) => {}
        other => panic!("expected Atom(False), got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// Per-atom LP decomposition: boolean-shape wins
// ---------------------------------------------------------------------------

#[test]
fn test_lp_false_or_branch_drops_to_remaining_branch() {
    // In the mutex net: p_free + p_cs = 1, so 2 <= p_free is LP-false.
    // Or([2 <= p_free, IsFireable(t_enter)]) -> IsFireable(t_enter).
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::Or(vec![
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p_free".to_string()]),
        ),
        StatePredicate::IsFireable(vec!["t_enter".to_string()]),
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::IsFireable(_)),
        "LP-false Or branch should be dropped; got: {result:?}"
    );
}

#[test]
fn test_not_of_lp_false_atom_becomes_true() {
    // In the mutex net: 2 <= p_free is LP-false.
    // Not(2 <= p_free) -> Not(False) -> True.
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::Not(Box::new(StatePredicate::IntLe(
        IntExpr::Constant(2),
        IntExpr::TokensCount(vec!["p_free".to_string()]),
    )));

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::True),
        "Not(LP-false) should become True; got: {result:?}"
    );
}

#[test]
fn test_conjunction_level_lp_proof_survives_atom_pass() {
    // Three-place conserving net: p0 + p1 + p2 = 3 (one transition cycles tokens).
    // Each of 2 <= p0 and 2 <= p1 is individually possible but together they
    // require p0 + p1 >= 4 > 3. Neither atom is LP-false on its own, but the
    // conjunction is LP-unreachable.
    let net = PetriNet {
        name: Some("three-conserve".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t01", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t12", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t20", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 0, 0],
    };
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::And(vec![
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p0".to_string()]),
        ),
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        ),
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::False),
        "conjunction-level LP should prove unreachable; got: {result:?}"
    );
}

#[test]
fn test_lp_atom_cache_reused_across_properties() {
    // Two properties containing the same IntLe atom should hit the cache.
    use super::temporal::simplify_formula_ctx;
    use super::SimplificationContext;

    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let shared_atom = StatePredicate::IntLe(
        IntExpr::Constant(2),
        IntExpr::TokensCount(vec!["p_free".to_string()]),
    );

    let props = vec![
        Property {
            id: "prop-a".to_string(),
            formula: Formula::Reachability(ReachabilityFormula {
                quantifier: PathQuantifier::EF,
                predicate: shared_atom.clone(),
            }),
        },
        Property {
            id: "prop-b".to_string(),
            formula: Formula::Reachability(ReachabilityFormula {
                quantifier: PathQuantifier::AG,
                predicate: shared_atom,
            }),
        },
    ];

    let mut ctx = SimplificationContext::new(&net, &aliases, facts);
    for prop in &props {
        let _ = simplify_formula_ctx(&prop.formula, &mut ctx);
    }

    assert_eq!(
        ctx.lp_atom_cache_len(),
        1,
        "same IntLe atom across two properties should produce exactly 1 cache entry"
    );
}

#[test]
fn test_ctl_formula_with_lp_false_atom_collapses() {
    // CTL: EF(Atom(2 <= p_free)) on mutex net -> EF(Atom(False)) -> Atom(False).
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let ctl = CtlFormula::EF(Box::new(CtlFormula::Atom(StatePredicate::IntLe(
        IntExpr::Constant(2),
        IntExpr::TokensCount(vec!["p_free".to_string()]),
    ))));
    let formula = Formula::Ctl(ctl);

    let result = simplify_formula(&formula, &net, &facts, &aliases);
    match result {
        Formula::Ctl(CtlFormula::Atom(StatePredicate::False)) => {}
        other => panic!("expected Ctl(Atom(False)); got: {other:?}"),
    }
}

// Facade function
// ---------------------------------------------------------------------------

#[test]
fn test_simplify_properties_preserves_ids() {
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);

    let props = vec![
        Property {
            id: "prop-0".to_string(),
            formula: Formula::Reachability(ReachabilityFormula {
                quantifier: PathQuantifier::EF,
                predicate: StatePredicate::And(vec![StatePredicate::True, StatePredicate::False]),
            }),
        },
        Property {
            id: "prop-1".to_string(),
            formula: Formula::PlaceBound(vec!["p_free".to_string()]),
        },
    ];

    let result = simplify_properties_with_aliases(&net, &props, &aliases);
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].id, "prop-0");
    assert_eq!(result[1].id, "prop-1");

    // prop-0: EF(And(True, False)) → EF(False).
    match &result[0].formula {
        Formula::Reachability(r) => {
            assert!(matches!(r.predicate, StatePredicate::False));
        }
        other => panic!("expected Reachability, got: {other:?}"),
    }

    // prop-1: PlaceBound unchanged.
    assert!(matches!(&result[1].formula, Formula::PlaceBound(_)));
}

// ---------------------------------------------------------------------------
// Tier 5: P-invariant implication fold
// ---------------------------------------------------------------------------

#[test]
fn test_implication_fold_redundant_conjunct_drops() {
    // Mutex net: p_free + p_cs = 1.
    // And(1 <= p_free, p_cs <= 0) — the first atom implies the second.
    // Should simplify to just the first atom.
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::And(vec![
        StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p_free".to_string()]),
        ),
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p_cs".to_string()]),
            IntExpr::Constant(0),
        ),
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    // The second child is redundant (implied by the first via invariant).
    // Result should be the first atom alone (unwrapped from singleton And).
    match &result {
        StatePredicate::IntLe(IntExpr::Constant(1), IntExpr::TokensCount(names))
            if names == &["p_free".to_string()] => {}
        StatePredicate::True => {
            // Also acceptable: LP may prove the first atom always true on this net.
        }
        other => {
            panic!("expected first atom or True after redundant conjunct drop; got: {other:?}")
        }
    }
}

#[test]
fn test_implication_fold_implied_disjunct_drops() {
    // Mutex net: p_free + p_cs = 1.
    // Or(1 <= p_free, p_cs <= 0) — the first implies the second.
    // In Or, if A implies B then A is subsumed: drop A, keep B.
    // Result: p_cs <= 0 (or True if LP resolves).
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::Or(vec![
        StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p_free".to_string()]),
        ),
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p_cs".to_string()]),
            IntExpr::Constant(0),
        ),
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    match &result {
        StatePredicate::IntLe(IntExpr::TokensCount(names), IntExpr::Constant(0))
            if names == &["p_cs".to_string()] => {}
        StatePredicate::True => {
            // LP may prove the remaining atom always true.
        }
        other => panic!("expected second atom or True after implied disjunct drop; got: {other:?}"),
    }
}

#[test]
fn test_implication_fold_contradictory_conjunction_becomes_false() {
    // Mutex net: p_free + p_cs = 1.
    // And(1 <= p_free, 1 <= p_cs) — contradictory via invariant.
    // p_free >= 1 implies p_cs <= 0, which contradicts p_cs >= 1.
    let net = mutex_net();
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    let pred = StatePredicate::And(vec![
        StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p_free".to_string()]),
        ),
        StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p_cs".to_string()]),
        ),
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::False),
        "contradictory conjunction via invariant should become False; got: {result:?}"
    );
}

#[test]
fn test_implication_fold_weighted_invariant() {
    // Net with invariant 2*p0 + p1 = 4.
    // p0: initial=2, p1: initial=0.
    // Transition cycles: t0 takes 1 from p0, puts 2 in p1. t1 reverse.
    let net = PetriNet {
        name: Some("weighted-conservation".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 2)]),
            trans("t1", vec![arc(1, 2)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![2, 0],
    };
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    // Verify the invariant was extracted: 2*p0 + 1*p1 = 4.
    assert!(
        !facts.binary_invariants.is_empty(),
        "should extract a binary invariant from weighted conservation net"
    );

    // p0 >= 2 implies p1 <= 4 - 2*2 = 0.
    // And(2 <= p0, 1 <= p1) should be contradictory: p0>=2 → p1<=0, but p1>=1.
    let pred = StatePredicate::And(vec![
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p0".to_string()]),
        ),
        StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        ),
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    assert!(
        matches!(result, StatePredicate::False),
        "weighted invariant contradiction should become False; got: {result:?}"
    );
}

#[test]
fn test_implication_fold_weighted_upper_bound_uses_ceil_rounding() {
    // Net with invariant p0 + 2*p1 = 5.
    // The forward transition consumes 1 from p1 and produces 2 in p0;
    // the reverse transition consumes 2 from p0 and produces 1 in p1.
    let net = PetriNet {
        name: Some("weighted-ceil".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(1, 1)], vec![arc(0, 2)]),
            trans("t1", vec![arc(0, 2)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 2],
    };
    let aliases = PropertyAliases::identity(&net);
    let facts = compute_facts(&net);

    assert!(
        !facts.binary_invariants.is_empty(),
        "should extract a binary invariant from weighted ceil net"
    );

    // p0 <= 2 implies p1 >= ceil((5 - 2) / 2) = 2.
    // This specifically exercises the Upper -> Lower implication path:
    // using floor here would derive only p1 >= 1 and fail to simplify.
    let pred = StatePredicate::Or(vec![
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string()]),
            IntExpr::Constant(2),
        ),
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        ),
    ]);

    let result = simplify_predicate(&pred, &net, &facts, &aliases);
    match &result {
        StatePredicate::IntLe(IntExpr::Constant(2), IntExpr::TokensCount(names))
            if names == &["p1".to_string()] => {}
        other => panic!("expected p1 >= 2 after ceil-rounded implication fold; got: {other:?}"),
    }
}
