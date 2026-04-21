// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermStore};

use crate::ematching::pattern::{EMatchArg, EMatchPattern};

#[test]
fn test_contains_quantifier_no_quantifiers() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);

    assert!(!contains_quantifier(&terms, eq));
}

#[test]
fn test_contains_quantifier_with_forall() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let body = terms.mk_eq(x, five);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    assert!(contains_quantifier(&terms, forall));
}

#[test]
fn test_extract_patterns_prefers_user_triggers() {
    let mut terms = TermStore::new();

    let p_sym = Symbol::named("P");
    let q_sym = Symbol::named("Q");
    let f_sym = Symbol::named("f");
    let g_sym = Symbol::named("g");

    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(f_sym, vec![x], Sort::Int);
    let g_x = terms.mk_app(g_sym, vec![x], Sort::Int);

    let p_f_x = terms.mk_app(p_sym, vec![f_x], Sort::Bool);
    let q_g_x = terms.mk_app(q_sym, vec![g_x], Sort::Bool);

    let body = terms.mk_and(vec![p_f_x, q_g_x]);

    // User trigger: Q(g(x)) only.
    let forall =
        terms.mk_forall_with_triggers(vec![("x".to_string(), Sort::Int)], body, vec![vec![q_g_x]]);

    let groups = extract_patterns(&terms, forall);
    assert!(!groups.is_empty(), "expected at least one trigger group");
    // Single trigger: Q(g(x)). All patterns within the group should be Q.
    assert!(
        groups
            .iter()
            .all(|g| g.patterns.iter().all(|p| p.symbol.name() == "Q")),
        "expected only Q patterns from user triggers, got {:?}",
        groups
            .iter()
            .flat_map(|g| g.patterns.iter().map(|p| p.symbol.name()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_extract_patterns_falls_back_when_user_triggers_yield_no_patterns() {
    let mut terms = TermStore::new();

    let p_sym = Symbol::named("P");
    let x = terms.mk_var("x", Sort::Int);

    // Body contains a usable pattern: P(x).
    let body = terms.mk_app(p_sym, vec![x], Sort::Bool);

    // User trigger is unusable (non-App), so it will be filtered out.
    let forall =
        terms.mk_forall_with_triggers(vec![("x".to_string(), Sort::Int)], body, vec![vec![x]]);

    let groups = extract_patterns(&terms, forall);
    assert!(
        groups
            .iter()
            .any(|g| g.patterns.iter().any(|p| p.symbol.name() == "P")),
        "expected fallback to auto-extracted P pattern, got {:?}",
        groups
            .iter()
            .flat_map(|g| g.patterns.iter().map(|p| p.symbol.name()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_extract_patterns_resolve_let_aliases() {
    let mut terms = TermStore::new();

    let p_sym = Symbol::named("P");
    let f_sym = Symbol::named("f");

    let x = terms.mk_var("x", Sort::Int);
    let t = terms.mk_var("t", Sort::Int);
    let f_x = terms.mk_app(f_sym, vec![x], Sort::Int);
    let p_t = terms.mk_app(p_sym, vec![t], Sort::Bool);
    let body = terms.mk_let(vec![("t".to_string(), f_x)], p_t);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let groups = extract_patterns(&terms, forall);

    assert!(
        groups.iter().any(|group| {
            group.patterns.iter().any(|pattern| {
                pattern.symbol.name() == "P"
                    && matches!(
                        pattern.args.as_slice(),
                        [EMatchArg::Nested(nested)]
                            if nested.symbol.name() == "f"
                                && matches!(nested.args.as_slice(), [EMatchArg::Var(0)])
                    )
            })
        }),
        "expected P(f(x)) trigger after let-alias expansion, got {:?}",
        groups
            .iter()
            .flat_map(|g| g.patterns.iter().map(|p| format!("{p:?}")))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_extract_patterns_respect_let_shadowing() {
    let mut terms = TermStore::new();

    let p_sym = Symbol::named("P");

    let x = terms.mk_var("x", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let p_x = terms.mk_app(p_sym, vec![x], Sort::Bool);
    let body = terms.mk_let(vec![("x".to_string(), c)], p_x);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let groups = extract_patterns(&terms, forall);

    assert!(
        groups.is_empty(),
        "expected no triggers because let-shadowed x is ground, got {:?}",
        groups
            .iter()
            .flat_map(|g| g.patterns.iter().map(|p| format!("{p:?}")))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_ematching_matches_let_wrapped_multi_var_body() {
    let mut terms = TermStore::new();

    let r_sym = Symbol::named("R");
    let f_sym = Symbol::named("f");
    let g_sym = Symbol::named("g");

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let tx = terms.mk_var("tx", Sort::Int);
    let ty = terms.mk_var("ty", Sort::Int);

    let f_x = terms.mk_app(f_sym.clone(), vec![x], Sort::Int);
    let g_y = terms.mk_app(g_sym.clone(), vec![y], Sort::Int);
    let r_tx_ty = terms.mk_app(r_sym.clone(), vec![tx, ty], Sort::Bool);
    let body = terms.mk_let(
        vec![("tx".to_string(), f_x), ("ty".to_string(), g_y)],
        r_tx_ty,
    );
    let forall = terms.mk_forall(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let f_a = terms.mk_app(f_sym, vec![a], Sort::Int);
    let g_b = terms.mk_app(g_sym, vec![b], Sort::Int);
    let ground = terms.mk_app(r_sym, vec![f_a, g_b], Sort::Bool);

    let result = perform_ematching(&mut terms, &[forall, ground]);
    assert_eq!(
        result.instantiations.len(),
        1,
        "expected one let-driven instantiation, got {:?}",
        result.instantiations
    );

    assert_eq!(
        result.instantiations[0], ground,
        "let-wrapped quantifier bodies should instantiate to a let-free ground term"
    );
}

#[test]
fn test_contains_quantifier_nested_in_not() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let body = terms.mk_eq(x, five);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let not_forall = terms.mk_not(forall);

    assert!(contains_quantifier(&terms, not_forall));
}

#[test]
fn test_instantiation_limit_prevents_runaway() {
    // Create a pattern that could loop infinitely: (forall ((x Int)) (P (f x)))
    // With multiple ground terms f(a), f(f(a)), f(f(f(a))), this could
    // produce unbounded instantiations.
    let mut terms = TermStore::new();

    // Create symbols
    let p_sym = Symbol::named("P");
    let f_sym = Symbol::named("f");

    // Bound variable x
    let x = terms.mk_var("x", Sort::Int);

    // f(x)
    let f_x = terms.mk_app(f_sym.clone(), vec![x], Sort::Int);

    // P(f(x))
    let p_f_x = terms.mk_app(p_sym.clone(), vec![f_x], Sort::Bool);

    // forall x. P(f(x))
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_f_x);

    // Ground term: constant a
    let a = terms.mk_var("a", Sort::Int);

    // Create nested f applications: f(a), f(f(a)), f(f(f(a))), ... f^10(a)
    let mut ground_terms = vec![a];
    let mut current = a;
    for _ in 0..10 {
        let f_current = terms.mk_app(f_sym.clone(), vec![current], Sort::Int);
        ground_terms.push(f_current);
        current = f_current;
    }

    // Create P(ground) assertions for each
    let mut assertions: Vec<TermId> = ground_terms
        .iter()
        .map(|&t| terms.mk_app(p_sym.clone(), vec![t], Sort::Bool))
        .collect();
    assertions.push(forall);

    // With a low limit, E-matching should stop early
    let config = EMatchingConfig {
        max_per_quantifier: 5,
        max_total: 100,
        ..Default::default()
    };

    let result = perform_ematching_with_config(&mut terms, &assertions, &config);

    // Should hit the per-quantifier limit (5) before processing all 11 ground terms
    assert!(
        result.instantiations.len() <= 5,
        "Expected at most 5 instantiations, got {}",
        result.instantiations.len()
    );
    assert!(
        result.reached_limit,
        "Should have reached per-quantifier limit"
    );
}

#[test]
fn test_instantiation_global_limit() {
    // Test that global limit works across multiple quantifiers
    let mut terms = TermStore::new();

    let p_sym = Symbol::named("P");
    let q_sym = Symbol::named("Q");

    // Bound variables
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    // P(x) and Q(y) for forall bodies
    let p_x = terms.mk_app(p_sym.clone(), vec![x], Sort::Bool);
    let q_y = terms.mk_app(q_sym.clone(), vec![y], Sort::Bool);

    // Two quantifiers: forall x. P(x) and forall y. Q(y)
    let forall_p = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_x);
    let forall_q = terms.mk_forall(vec![("y".to_string(), Sort::Int)], q_y);

    // Create 10 P ground terms and 10 Q ground terms
    let mut assertions = vec![forall_p, forall_q];
    for i in 0..10 {
        let c = terms.mk_int(BigInt::from(i));
        assertions.push(terms.mk_app(p_sym.clone(), vec![c], Sort::Bool));
        assertions.push(terms.mk_app(q_sym.clone(), vec![c], Sort::Bool));
    }

    // Global limit of 8 should stop before all 20 instantiations
    let config = EMatchingConfig {
        max_per_quantifier: 100,
        max_total: 8,
        ..Default::default()
    };

    let result = perform_ematching_with_config(&mut terms, &assertions, &config);

    assert!(
        result.instantiations.len() <= 8,
        "Expected at most 8 instantiations, got {}",
        result.instantiations.len()
    );
    assert!(result.reached_limit, "Should have reached global limit");
}

#[test]
fn test_generation_tracking_basic() {
    let mut tracker = GenerationTracker::new();

    // Initial terms have generation 0
    let t1 = TermId(1);
    let t2 = TermId(2);
    assert_eq!(tracker.get(t1), 0);
    assert_eq!(tracker.get(t2), 0);

    // Set generation for t1
    tracker.set(t1, 1);
    assert_eq!(tracker.get(t1), 1);
    assert_eq!(tracker.get(t2), 0);

    // Test max_generation
    let t3 = TermId(3);
    tracker.set(t3, 5);
    assert_eq!(tracker.max_generation(&[t1, t2, t3]), 5);
    assert_eq!(tracker.max_generation(&[t1, t2]), 1);

    // Test instantiation cost (weight + max_gen)
    assert_eq!(tracker.instantiation_cost(&[t1, t2], 1.0), 2.0);
    assert_eq!(tracker.instantiation_cost(&[t2, t3], 2.0), 7.0);
}

#[test]
fn test_generation_tracking_prevents_deep_chains() {
    let mut terms = TermStore::new();

    let p_sym = Symbol::named("P");
    let f_sym = Symbol::named("f");

    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(f_sym.clone(), vec![x], Sort::Int);
    let p_f_x = terms.mk_app(p_sym.clone(), vec![f_x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_f_x);

    let a = terms.mk_var("a", Sort::Int);
    let mut ground_terms = vec![a];
    let mut current = a;
    for _ in 0..15 {
        let f_current = terms.mk_app(f_sym.clone(), vec![current], Sort::Int);
        ground_terms.push(f_current);
        current = f_current;
    }

    let mut assertions: Vec<TermId> = ground_terms
        .iter()
        .map(|&t| terms.mk_app(p_sym.clone(), vec![t], Sort::Bool))
        .collect();
    assertions.push(forall);

    // Pre-set generations to simulate previous instantiation rounds
    let mut tracker = GenerationTracker::new();
    for (i, &term) in ground_terms.iter().enumerate() {
        if i > 0 {
            tracker.set(term, i as u32);
        }
    }

    // With eager_threshold=5, only terms with generation <= 4 should be instantiated
    let config = EMatchingConfig {
        max_per_quantifier: 1000,
        max_total: 1000,
        eager_threshold: 5.0,
        lazy_threshold: 10.0,
        default_weight: 1.0,
    };

    let result =
        perform_ematching_with_generations(&mut terms, &assertions, &config, tracker, None);

    // Generations 0-4 have cost 1-5, which are <= eager_threshold
    assert!(
        result.instantiations.len() <= 5,
        "Expected at most 5 eager instantiations, got {}",
        result.instantiations.len()
    );

    // Generations 5-9 have cost 6-10, should be deferred
    assert!(
        !result.deferred.is_empty(),
        "Expected some deferred instantiations"
    );
}

#[test]
fn test_generation_increments_on_instantiation() {
    let mut terms = TermStore::new();
    let p_sym = Symbol::named("P");
    let x = terms.mk_var("x", Sort::Int);
    let p_x = terms.mk_app(p_sym.clone(), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_x);

    let c1 = terms.mk_int(BigInt::from(1));
    let c2 = terms.mk_int(BigInt::from(2));
    let p_c1 = terms.mk_app(p_sym.clone(), vec![c1], Sort::Bool);
    let p_c2 = terms.mk_app(p_sym, vec![c2], Sort::Bool);

    let assertions = vec![forall, p_c1, p_c2];

    let mut tracker = GenerationTracker::new();
    tracker.set(c2, 3);

    let config = EMatchingConfig::default();
    let result =
        perform_ematching_with_generations(&mut terms, &assertions, &config, tracker, None);

    assert_eq!(result.generation_tracker.current_round(), 1);
}

#[test]
fn test_subst_vars_simplifies_bvadd_zero() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::bitvec(64));
    let zero = terms.mk_bitvec(BigInt::from(0u8), 64);
    let one = terms.mk_bitvec(BigInt::from(1u8), 64);
    let add = terms.mk_app(Symbol::named("bvadd"), vec![x, zero], Sort::bitvec(64));

    let mut subst = HashMap::new();
    subst.insert("x".to_string(), one);
    let instantiated = subst_vars(&mut terms, add, &subst);

    assert_eq!(
        instantiated, one,
        "subst_vars must simplify bvadd(x, 0) to x for API-path parity"
    );
}

#[test]
fn test_subst_vars_simplifies_zero_extend_constant() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::bitvec(32));
    let five_32 = terms.mk_bitvec(BigInt::from(5u8), 32);
    let expected = terms.mk_bitvec(BigInt::from(5u8), 64);
    let zero_extend = terms.mk_app(
        Symbol::Indexed("zero_extend".to_string(), vec![32]),
        vec![x],
        Sort::bitvec(64),
    );

    let mut subst = HashMap::new();
    subst.insert("x".to_string(), five_32);
    let instantiated = subst_vars(&mut terms, zero_extend, &subst);

    assert_eq!(
        instantiated, expected,
        "subst_vars must simplify zero_extend on constants"
    );
}

#[test]
fn test_subst_vars_simplifies_certus_style_bv_index_alias() {
    let mut terms = TermStore::new();

    let index32_sort = Sort::bitvec(32);
    let index64_sort = Sort::bitvec(64);
    let elem_sort = Sort::bitvec(8);
    let array_sort = Sort::array(index64_sort.clone(), elem_sort.clone());

    let arr = terms.mk_var("arr", array_sort.clone());
    let i32 = terms.mk_var("i", index32_sort.clone());
    let val = terms.mk_bitvec(BigInt::from(0xabu8), 8);
    let zero32 = terms.mk_bitvec(BigInt::from(0u8), 32);

    let store_idx = terms.mk_app(
        Symbol::Indexed("zero_extend".to_string(), vec![32]),
        vec![i32],
        index64_sort.clone(),
    );
    let plus_zero = terms.mk_app(Symbol::named("bvadd"), vec![i32, zero32], index32_sort);
    let select_idx = terms.mk_app(
        Symbol::Indexed("zero_extend".to_string(), vec![32]),
        vec![plus_zero],
        index64_sort,
    );

    let store_term = terms.mk_app(
        Symbol::named("store"),
        vec![arr, store_idx, val],
        array_sort,
    );
    let select_term = terms.mk_app(
        Symbol::named("select"),
        vec![store_term, select_idx],
        elem_sort,
    );

    let mut subst = HashMap::new();
    subst.insert("i".to_string(), terms.mk_bitvec(BigInt::from(3u8), 32));
    let instantiated = subst_vars(&mut terms, select_term, &subst);

    assert_eq!(
        instantiated, val,
        "subst_vars must preserve store/select aliasing after bvadd+zero_extend simplification"
    );
}

/// Test for issue #1891: E-matching must not confuse free variables (constants)
/// with bound variables when they have the same sort.
///
/// This regression test verifies that `extract_patterns` correctly identifies
/// bound variables by name rather than by sort.
#[test]
fn test_issue_1891_free_vs_bound_vars_same_sort() {
    let mut terms = TermStore::new();

    // Create uninterpreted function f: Int -> Int
    let f_sym = Symbol::named("f");

    // Bound variable x for the axiom (forall x. f(x) = x*2)
    let x = terms.mk_var("x", Sort::Int);

    // Build axiom body: f(x) = x * 2
    let f_x = terms.mk_app(f_sym.clone(), vec![x], Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let x_times_2 = terms.mk_mul(vec![x, two]);
    let eq_body = terms.mk_eq(f_x, x_times_2);

    // Create quantified axiom: forall x. f(x) = x * 2
    let axiom = terms.mk_forall(vec![("x".to_string(), Sort::Int)], eq_body);

    // Free constant c (also Int sort, same as bound variable x)
    let c = terms.mk_var("c", Sort::Int);

    // Ground term f(c) that should trigger the pattern
    let f_c = terms.mk_app(f_sym.clone(), vec![c], Sort::Int);

    // Assertions include both the axiom and a term containing f(c)
    let ten = terms.mk_int(BigInt::from(10));
    let f_c_eq_10 = terms.mk_eq(f_c, ten);
    let assertions = vec![axiom, terms.mk_not(f_c_eq_10)];

    // Run E-matching
    let result = perform_ematching(&mut terms, &assertions);

    // E-matching should:
    // 1. Extract pattern f(BoundVar(0)) from the axiom
    // 2. Match against ground term f(c)
    // 3. Produce instantiation with x -> c
    //
    // Before the fix for #1891, if c was mistakenly identified as the bound
    // variable (because it has the same Int sort), no pattern would be extracted
    // and no instantiation would occur.
    assert!(
        !result.instantiations.is_empty(),
        "E-matching should produce at least one instantiation for f(c)"
    );

    // Verify the instantiation is the axiom body with x substituted by c
    // The instantiation should be: f(c) = c * 2
    let instantiated = result.instantiations[0];
    if let TermData::App(sym, args) = terms.get(instantiated) {
        assert_eq!(
            sym,
            &Symbol::named("="),
            "Instantiation should be an equality"
        );
        // First arg should be f(c)
        if let TermData::App(f_sym_check, f_args) = terms.get(args[0]) {
            assert_eq!(f_sym_check, &f_sym, "LHS should be f(...)");
            // f's argument should be c
            if let TermData::Var(name, _) = terms.get(f_args[0]) {
                assert_eq!(name, "c", "f's argument should be c, not x");
            } else {
                panic!("f's argument should be a variable");
            }
        } else {
            panic!("LHS should be f(c)");
        }
    } else {
        panic!("Instantiation should be an equality term");
    }
}

/// Test for issue #1891: Multiple bound variables with multiple free variables
/// of the same sort should not confuse the pattern extraction.
#[test]
fn test_issue_1891_multiple_vars_same_sort() {
    let mut terms = TermStore::new();

    // Create binary uninterpreted function g: Int x Int -> Int
    let g_sym = Symbol::named("g");

    // Bound variables x, y (both Int)
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    // Build axiom body: g(x, y) = g(y, x) (symmetry)
    let g_xy = terms.mk_app(g_sym.clone(), vec![x, y], Sort::Int);
    let g_yx = terms.mk_app(g_sym.clone(), vec![y, x], Sort::Int);
    let eq_body = terms.mk_eq(g_xy, g_yx);

    // Create quantified axiom: forall x y. g(x, y) = g(y, x)
    let axiom = terms.mk_forall(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        eq_body,
    );

    // Free constants a, b (also Int sort)
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);

    // Ground term g(a, b) that should trigger the pattern
    let g_ab = terms.mk_app(g_sym, vec![a, b], Sort::Int);

    // Assertion includes both the axiom and a term containing g(a, b)
    let zero = terms.mk_int(BigInt::from(0));
    let g_ab_eq_0 = terms.mk_eq(g_ab, zero);
    let assertions = vec![axiom, g_ab_eq_0];

    // Run E-matching
    let result = perform_ematching(&mut terms, &assertions);

    // Should find pattern g(BoundVar(0), BoundVar(1)) and match against g(a, b)
    // Producing instantiation: g(a, b) = g(b, a)
    assert!(
        !result.instantiations.is_empty(),
        "E-matching should produce instantiation for g(a, b)"
    );
}

/// Regression test for #3593: NOT(exists x. phi) must be NNF-converted to
/// forall x. NOT(phi) before E-matching. Without this, collect_quantifiers
/// strips the negation and instantiates the body with wrong polarity.
#[test]
fn test_collect_quantifiers_nnf_negated_exists() {
    let mut terms = TermStore::new();

    // Build: exists x:Int. P(x) where P is an uninterpreted predicate
    let x = terms.mk_var("x", Sort::Int);
    let p_sym = Symbol::named("P");
    let p_of_x = terms.mk_app(p_sym, vec![x], Sort::Bool);

    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], p_of_x);

    // NOT(exists x. P(x)) should be collected as forall x. NOT(P(x))
    let not_exists = terms.mk_not(exists);

    let mut quantifiers = Vec::new();
    collect_quantifiers(&mut terms, not_exists, &mut quantifiers);

    assert_eq!(
        quantifiers.len(),
        1,
        "should collect exactly one quantifier"
    );

    // The collected quantifier should be a Forall with negated body
    match terms.get(quantifiers[0]) {
        TermData::Forall(vars, body, _triggers) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            // Body should be NOT(P(x)) — verify it's a negation
            match terms.get(*body) {
                TermData::Not(_) => {} // correct: body is negated
                other => {
                    panic!("expected Not(...) body in NNF-converted forall, got {other:?}",)
                }
            }
        }
        other => panic!("expected Forall from NNF conversion of NOT(exists), got {other:?}",),
    }
}

/// Verify NNF conversion also works for NOT(forall x. phi) → exists x. NOT(phi).
/// AC2 for #5612: verify stacker depth guards prevent stack overflow
/// on deeply nested terms (5000 levels of Not).
#[test]
fn test_depth_guard_5000_nested_not_no_overflow() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    // Build Not(Not(Not(...(x)...))) with 5000 levels
    let mut current = x;
    for _ in 0..5000 {
        current = terms.mk_not(current);
    }

    // All 5 guarded functions should handle this without stack overflow
    assert!(!contains_quantifier(&terms, current));

    let index = TermIndex::new(&terms, &[current]);
    assert!(index.by_symbol.is_empty());
}

#[test]
fn test_ematching_ignores_unasserted_ground_terms() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".into());

    let p_sym = Symbol::named("P");
    let q_sym = Symbol::named("Q");
    let r_sym = Symbol::named("R");

    let x = terms.mk_var("x", u.clone());
    let p_x = terms.mk_app(p_sym.clone(), vec![x], Sort::Bool);
    let q_x = terms.mk_app(q_sym, vec![x], Sort::Bool);
    let body = terms.mk_implies(p_x, q_x);
    let quant =
        terms.mk_forall_with_triggers(vec![("x".to_string(), u.clone())], body, vec![vec![p_x]]);

    let a = terms.mk_var("a", u);
    let _inactive_p_a = terms.mk_app(p_sym, vec![a], Sort::Bool);
    let asserted = terms.mk_app(r_sym, vec![a], Sort::Bool);

    let assertions = vec![quant, asserted];
    let result = perform_ematching(&mut terms, &assertions);

    assert!(
        result.instantiations.is_empty(),
        "unasserted ground terms must not trigger E-matching"
    );
}

#[test]
fn test_collect_quantifiers_nnf_negated_forall() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let p_sym = Symbol::named("P");
    let p_of_x = terms.mk_app(p_sym, vec![x], Sort::Bool);

    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_of_x);
    let not_forall = terms.mk_not(forall);

    let mut quantifiers = Vec::new();
    collect_quantifiers(&mut terms, not_forall, &mut quantifiers);

    assert_eq!(quantifiers.len(), 1);

    match terms.get(quantifiers[0]) {
        TermData::Exists(vars, body, _triggers) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            match terms.get(*body) {
                TermData::Not(_) => {}
                other => {
                    panic!("expected Not(...) body in NNF-converted exists, got {other:?}",)
                }
            }
        }
        other => panic!("expected Exists from NNF conversion of NOT(forall), got {other:?}",),
    }
}

/// Test that the repeated-variable binding save/restore works correctly.
///
/// Pattern: f(x, x) — both args must bind to the same variable.
/// Ground: f(a, b) where a != b — direct match fails after binding x=a.
/// With equivalence classes where a == b, the fallback should succeed.
/// Without equivalence, the match must fail (and binding state must be clean).
#[test]
fn test_repeated_variable_binding_restore_on_failure() {
    let mut terms = TermStore::new();

    let f_sym = Symbol::named("f");

    // Create ground terms: a and b (distinct constants)
    let a = terms.mk_int(BigInt::from(1));
    let b = terms.mk_int(BigInt::from(2));

    // f(a, b)
    let f_a_b = terms.mk_app(f_sym.clone(), vec![a, b], Sort::Int);

    // f(a, a) should match f(x, x)
    let f_a_a = terms.mk_app(f_sym.clone(), vec![a, a], Sort::Int);

    // Pattern: f(x, x) — variable 0 appears in both positions
    let pattern = EMatchPattern {
        symbol: f_sym,
        args: vec![EMatchArg::Var(0), EMatchArg::Var(0)],
    };

    // Without equivalence classes: f(x,x) should NOT match f(a,b) since a != b
    let result = match_pattern(&terms, &pattern, f_a_b, 1, None);
    assert!(
        result.is_none(),
        "f(x,x) should not match f(a,b) without equivalence classes"
    );
    let result = match_pattern(&terms, &pattern, f_a_a, 1, None);
    assert!(result.is_some(), "f(x,x) should match f(a,a)");
    assert_eq!(result.unwrap()[0], a);
}

/// Test that repeated-variable binding restoration is critical for equivalence
/// class fallback correctness.
///
/// This test specifically exercises the bug that the save/restore fix prevents:
/// Pattern f(x, x) matched against f(a, b) where a != b. The direct match fails
/// after binding x=a (dirty state). The equivalence class fallback tries f(c, c)
/// where c != a. Without binding restoration, the stale x=a binding causes the
/// f(c, c) match to fail because c != a. With restoration, the binding is clean
/// and f(c, c) matches correctly with x=c.
#[test]
fn test_repeated_variable_binding_with_equivalence_class_fallback() {
    let mut terms = TermStore::new();

    let f_sym = Symbol::named("f");
    let a = terms.mk_int(BigInt::from(1));
    let b = terms.mk_int(BigInt::from(2));
    let c = terms.mk_int(BigInt::from(3));

    // f(a, b) — the match target (a != b, so direct match of f(x,x) fails)
    let f_a_b = terms.mk_app(f_sym.clone(), vec![a, b], Sort::Int);

    // f(c, c) — an equivalent term where both args are the same (c != a, c != b)
    // This is the term the fallback should find and match successfully.
    let f_c_c = terms.mk_app(f_sym.clone(), vec![c, c], Sort::Int);

    // Pattern: f(x, x)
    let pattern = EMatchPattern {
        symbol: f_sym,
        args: vec![EMatchArg::Var(0), EMatchArg::Var(0)],
    };

    // Build equivalence classes: f(a,b) == f(c,c)
    let eq_assertion = terms.mk_eq(f_a_b, f_c_c);
    let assertions = vec![eq_assertion];
    let eq_classes = EqualityClasses::from_assertions(&terms, &assertions);

    // With equivalence: f(x,x) against f(a,b) should:
    //   1. Try direct match: f(x,x) vs f(a,b) → binds x=a, then fails (a != b)
    //   2. Restore binding to clean state (the fix being tested)
    //   3. Try equivalence class member f(c,c) → binds x=c, succeeds (c == c)
    //
    // Without the save/restore fix, step 3 would fail because x is still bound
    // to a from the dirty state, and a != c.
    let result = match_pattern(&terms, &pattern, f_a_b, 1, Some(&eq_classes));
    assert!(
        result.is_some(),
        "f(x,x) should match f(a,b) via equivalence class containing f(c,c) — \
         this fails without binding-state restoration after direct match failure"
    );
    assert_eq!(result.unwrap()[0], c);
}

/// Test Phase B1b: EUF model-derived equivalence classes augment E-matching.
///
/// Scenario: `forall x. P(f(g(x)))` with pattern `f(g(x))`.
/// Ground terms include `f(c)` but not `f(g(a))`.
/// EUF model says `g(a) = c` (congruence-implied equality).
/// Without B1b: no match (f(c) doesn't structurally match f(g(x))).
/// With B1b: `c` and `g(a)` are in the same equivalence class,
/// so `f(c)` matches `f(g(x))` with x=a.
#[test]
fn test_euf_model_augments_equality_classes() {
    let mut terms = TermStore::new();
    let s = Sort::Uninterpreted("S".into());

    // Declare symbols
    let f_sym = Symbol::named("f");
    let g_sym = Symbol::named("g");
    let p_sym = Symbol::named("P");

    // Declare constant a : S
    let a = terms.mk_var("a", s.clone());
    // Declare constant c : S
    let c = terms.mk_var("c", s.clone());

    // Build g(a) and f(c) as ground terms
    let g_a = terms.mk_app(g_sym.clone(), vec![a], s.clone());
    let f_c = terms.mk_app(f_sym.clone(), vec![c], s.clone());

    // Build pattern: forall x. P(f(g(x))) :pattern (f(g(x)))
    let x = terms.mk_var("x", s.clone());
    let g_x = terms.mk_app(g_sym, vec![x], s.clone());
    let f_g_x = terms.mk_app(f_sym, vec![g_x], s.clone());
    let p_f_g_x = terms.mk_app(p_sym.clone(), vec![f_g_x], Sort::Bool);
    let forall =
        terms.mk_forall_with_triggers(vec![("x".to_string(), s)], p_f_g_x, vec![vec![f_g_x]]);

    // Assert the quantifier and ground terms
    let p_f_c = terms.mk_app(p_sym, vec![f_c], Sort::Bool);
    let assertions = vec![forall, p_f_c];

    // Without EUF model: E-matching should NOT match f(c) against f(g(x))
    let result_without = perform_ematching(&mut terms, &assertions);
    assert!(
        result_without.instantiations.is_empty(),
        "Without EUF model, f(c) should not match f(g(x)) (no structural match)"
    );

    // Build EUF model that says g(a) = c (same equivalence class)
    let mut euf_model = EufModel::default();
    euf_model.term_values.insert(g_a, "elem_0".to_string());
    euf_model.term_values.insert(c, "elem_0".to_string());

    // With EUF model: E-matching SHOULD match f(c) against f(g(x)) via g(a)=c
    let result_with = perform_ematching_with_generations(
        &mut terms,
        &assertions,
        &EMatchingConfig::default(),
        GenerationTracker::new(),
        Some(&euf_model),
    );
    assert!(
        !result_with.instantiations.is_empty(),
        "With EUF model (g(a)=c), f(c) should match f(g(x)) with x=a"
    );
}

#[test]
fn test_pattern_covered_vars_single_var() {
    let pat = EMatchPattern {
        symbol: Symbol::named("P"),
        args: vec![EMatchArg::Var(0)],
    };
    let vars = pattern_covered_vars(&pat);
    assert_eq!(vars, HashSet::from([0]));
}

#[test]
fn test_pattern_covered_vars_nested() {
    let nested = EMatchPattern {
        symbol: Symbol::named("g"),
        args: vec![EMatchArg::Var(1)],
    };
    let pat = EMatchPattern {
        symbol: Symbol::named("f"),
        args: vec![EMatchArg::Var(0), EMatchArg::Nested(Box::new(nested))],
    };
    let vars = pattern_covered_vars(&pat);
    assert_eq!(vars, HashSet::from([0, 1]));
}

#[test]
fn test_auto_multi_trigger_synthesis_unit() {
    // forall (x y). P(x) /\ Q(y) — no single pattern covers both
    let mut terms = TermStore::new();
    let p_sym = Symbol::named("P");
    let q_sym = Symbol::named("Q");

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let p_x = terms.mk_app(p_sym, vec![x], Sort::Bool);
    let q_y = terms.mk_app(q_sym, vec![y], Sort::Bool);
    let body = terms.mk_and(vec![p_x, q_y]);
    let forall = terms.mk_forall(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );

    let groups = extract_patterns(&terms, forall);

    // Should have synthesized multi-trigger groups
    assert!(
        groups.iter().any(|g| g.patterns.len() >= 2),
        "Expected at least one multi-trigger group, got {:?} groups with sizes {:?}",
        groups.len(),
        groups.iter().map(|g| g.patterns.len()).collect::<Vec<_>>()
    );

    // The multi-trigger should cover both variables
    for group in &groups {
        if group.patterns.len() >= 2 {
            let mut all_vars: HashSet<usize> = HashSet::new();
            for pat in &group.patterns {
                all_vars.extend(pattern_covered_vars(pat));
            }
            assert_eq!(
                all_vars.len(),
                2,
                "Multi-trigger should cover both variables"
            );
        }
    }
}

/// Test for issue #5911: capture_avoiding_subst must detect when substitution
/// values contain free variables matching bound variable names, and alpha-rename
/// the bound variables to avoid capture.
///
/// Scenario: subst = {x -> sk_f(y)}, applied to (forall ((y Int)) (> (+ x y) 0))
/// Without the fix, the free y in sk_f(y) would be captured by forall's bound y.
/// With the fix, the inner y is alpha-renamed to a fresh name.
#[test]
fn test_issue_5911_capture_avoiding_subst_forall() {
    let mut terms = TermStore::new();

    // Outer universal variable y (free in the substitution value)
    let y_outer = terms.mk_var("y", Sort::Int);

    // Build substitution value: sk_f(y) -- a Skolem function applied to outer y
    let sk_f = Symbol::named("sk_f");
    let sk_f_y = terms.mk_app(sk_f, vec![y_outer], Sort::Int);

    // Substitution: {x -> sk_f(y)}
    let mut subst = HashMap::new();
    subst.insert("x".to_string(), sk_f_y);

    // Build inner quantifier body: (> (+ x y) 0)
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let plus_xy = terms.mk_add(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let gt = terms.mk_gt(plus_xy, zero);

    // Build inner forall: (forall ((y Int)) (> (+ x y) 0))
    let inner_forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], gt);

    // Apply substitution -- this should alpha-rename inner y to avoid capturing
    // the free y in sk_f(y)
    let result = subst_vars(&mut terms, inner_forall, &subst);

    // The result should be a forall with a DIFFERENT bound variable name
    if let TermData::Forall(vars, body, _) = terms.get(result).clone() {
        assert_ne!(
            vars[0].0, "y",
            "Bound variable must be alpha-renamed to avoid capture. Got: {}",
            vars[0].0
        );

        // The body should reference sk_f(y_outer) for x and the fresh var for the inner y
        // Verify the body contains the Skolem function
        fn contains_app(terms: &TermStore, term: TermId, sym_name: &str) -> bool {
            match terms.get(term) {
                TermData::App(sym, args) => {
                    sym.name() == sym_name || args.iter().any(|&a| contains_app(terms, a, sym_name))
                }
                TermData::Not(inner) => contains_app(terms, *inner, sym_name),
                _ => false,
            }
        }

        assert!(
            contains_app(&terms, body, "sk_f"),
            "Body should contain sk_f after substitution of x"
        );
    } else {
        panic!("Result should be a Forall, got: {:?}", terms.get(result));
    }
}

/// Test for issue #5911: exists quantifier case.
/// subst = {x -> f(y)}, applied to (exists ((y Int)) (= x y))
/// The bound y must be alpha-renamed since y appears free in f(y).
#[test]
fn test_issue_5911_capture_avoiding_subst_exists() {
    let mut terms = TermStore::new();

    let y_outer = terms.mk_var("y", Sort::Int);
    let f_sym = Symbol::named("f");
    let f_y = terms.mk_app(f_sym, vec![y_outer], Sort::Int);

    let mut subst = HashMap::new();
    subst.insert("x".to_string(), f_y);

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let inner_exists = terms.mk_exists(vec![("y".to_string(), Sort::Int)], eq);

    let result = subst_vars(&mut terms, inner_exists, &subst);

    if let TermData::Exists(vars, _, _) = terms.get(result).clone() {
        assert_ne!(
            vars[0].0, "y",
            "Bound variable in exists must be alpha-renamed"
        );
    } else {
        panic!("Result should be an Exists");
    }
}

/// Test for issue #5911: no alpha-rename needed when no conflict exists.
/// subst = {x -> 42}, applied to (forall ((y Int)) (= x y))
/// No free variable conflict, so y should remain unchanged.
#[test]
fn test_issue_5911_no_rename_when_no_conflict() {
    let mut terms = TermStore::new();

    let forty_two = terms.mk_int(BigInt::from(42));
    let mut subst = HashMap::new();
    subst.insert("x".to_string(), forty_two);

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let inner_forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], eq);
    let result = subst_vars(&mut terms, inner_forall, &subst);

    if let TermData::Forall(vars, _, _) = terms.get(result).clone() {
        assert_eq!(
            vars[0].0, "y",
            "Bound variable should NOT be renamed when no conflict"
        );
    } else {
        panic!("Result should be a Forall");
    }
}

/// Test for issue #5911: collect_free_var_names correctly respects binders.
#[test]
fn test_issue_5911_collect_free_var_names() {
    let mut terms = TermStore::new();

    // Build: f(x, y) where x and y are free variables
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let f_sym = Symbol::named("f");
    let f_xy = terms.mk_app(f_sym, vec![x, y], Sort::Int);

    let bound = HashSet::new();
    let mut free_vars = HashSet::new();
    collect_free_var_names(&terms, f_xy, &bound, &mut free_vars);
    assert!(free_vars.contains("x"));
    assert!(free_vars.contains("y"));
    assert_eq!(free_vars.len(), 2);

    // Build: (forall ((x Int)) (f x y)) -- x is bound, y is free
    let zero = terms.mk_int(BigInt::from(0));
    let gt = terms.mk_gt(f_xy, zero);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], gt);

    let mut free_vars2 = HashSet::new();
    collect_free_var_names(&terms, forall, &bound, &mut free_vars2);
    assert!(!free_vars2.contains("x"), "x should be bound by forall");
    assert!(free_vars2.contains("y"), "y should still be free");
}

/// Test for issue #5911: E-matching instantiation with shadowed variables.
///
/// Simulates: (forall ((x Int)) (forall ((y Int)) (> (+ x y) 0)))
/// E-matching binds x -> g(y) where y is a free variable in the binding.
/// instantiate_body calls subst_vars with {x -> g(y)} on the inner
/// (forall ((y Int)) (> (+ x y) 0)). The inner y must be alpha-renamed
/// to prevent the free y in g(y) from being captured.
#[test]
fn test_issue_5911_ematching_instantiation_shadowed_var() {
    let mut terms = TermStore::new();

    // Build the quantifier body: (forall ((y Int)) (> (+ x y) 0))
    let x = terms.mk_var("x", Sort::Int);
    let y_inner = terms.mk_var("y", Sort::Int);
    let plus_xy = terms.mk_add(vec![x, y_inner]);
    let zero = terms.mk_int(BigInt::from(0));
    let gt = terms.mk_gt(plus_xy, zero);
    let inner_forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], gt);

    // E-matching binding: x -> g(y) where y is a free variable
    let y_outer = terms.mk_var("y", Sort::Int);
    let g_sym = Symbol::named("g");
    let g_y = terms.mk_app(g_sym, vec![y_outer], Sort::Int);

    // instantiate_body applies {x -> g(y)} to the inner forall
    let result = instantiate_body(&mut terms, inner_forall, &["x".to_string()], &[g_y]);

    // The result should be a forall with a RENAMED bound variable
    // because y appears free in the binding term g(y)
    if let TermData::Forall(vars, body, _) = terms.get(result).clone() {
        assert_ne!(
            vars[0].0, "y",
            "E-matching instantiation must alpha-rename inner y to avoid capture by g(y)"
        );

        // The body should contain g(y) (referencing the OUTER y, not the renamed inner var)
        fn has_app(terms: &TermStore, term: TermId, name: &str) -> bool {
            match terms.get(term) {
                TermData::App(sym, args) => {
                    sym.name() == name || args.iter().any(|&a| has_app(terms, a, name))
                }
                TermData::Not(inner) => has_app(terms, *inner, name),
                _ => false,
            }
        }
        assert!(
            has_app(&terms, body, "g"),
            "Body should contain g(y) from E-matching binding"
        );
    } else {
        panic!("Result should be a Forall");
    }
}
