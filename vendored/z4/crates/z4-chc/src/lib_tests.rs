// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use std::collections::HashMap;

struct PanicOnInductiveTs {
    init_bounds_map: HashMap<String, generalize::InitBounds>,
}

impl PanicOnInductiveTs {
    fn new(init_bounds_map: HashMap<String, generalize::InitBounds>) -> Self {
        Self { init_bounds_map }
    }
}

impl generalize::TransitionSystemRef for PanicOnInductiveTs {
    fn check_inductive(&mut self, formula: &ChcExpr, level: u32) -> bool {
        panic!("unexpected inductiveness query at level {level}: {formula:?}");
    }

    fn check_inductive_with_core(
        &mut self,
        conjuncts: &[ChcExpr],
        level: u32,
    ) -> Option<Vec<ChcExpr>> {
        panic!("unexpected inductiveness+core query at level {level}: {conjuncts:?}");
    }

    fn init_bounds(&self) -> HashMap<String, generalize::InitBounds> {
        self.init_bounds_map.clone()
    }
}

#[test]
fn test_problem_construction() {
    // Test basic problem construction
    let mut problem = ChcProblem::new();

    // Declare Inv : Int -> Bool
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    assert_eq!(problem.predicates().len(), 1);

    // x = 0 => Inv(x)
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 10 => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 10 => false (query)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    assert_eq!(problem.clauses().len(), 3);
    assert_eq!(problem.queries().count(), 1);
    assert_eq!(problem.facts().count(), 1);
    assert_eq!(problem.transitions().count(), 1);
    assert!(problem.validate().is_ok());
}

fn build_deep_problem(depth: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let arg = ChcExpr::var(x);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(pred, vec![ChcExpr::int(0)]),
    ));

    let mut deep = ChcExpr::Int(0);
    for _ in 0..depth {
        deep = ChcExpr::add(arg.clone(), deep);
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![arg])], Some(deep)),
        ClauseHead::False,
    ));
    problem
}

#[test]
fn direct_engine_drop_deep_problem_small_stack_6847() {
    const DEPTH: usize = 20_000;
    // 8MB matches default production stack. The test verifies iterative Drop
    // (#6847) doesn't overflow — not that constructors are iterative.
    // PdrSolver::new() has recursive preprocessing (try_split_ors, eliminate_mod)
    // that needs >2MB for 20K-deep expressions. See #7415.
    const STACK_BYTES: usize = 8 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .name("direct-engine-drop-small-stack".to_string())
        .stack_size(STACK_BYTES)
        .spawn(|| {
            drop(PdrSolver::new(
                build_deep_problem(DEPTH),
                PdrConfig::default(),
            ));
            drop(BmcSolver::new(
                build_deep_problem(DEPTH),
                BmcConfig::default(),
            ));
            drop(KindSolver::new(
                build_deep_problem(DEPTH),
                KindConfig::default(),
            ));
            drop(PdkindSolver::new(
                build_deep_problem(DEPTH),
                PdkindConfig::default(),
            ));
            drop(tpa::TpaSolver::new(
                build_deep_problem(DEPTH),
                tpa::TpaConfig::default(),
            ));
        })
        .expect("small-stack regression thread should spawn");

    handle
        .join()
        .expect("direct engine drop should not overflow on deep ChcProblem");
}

#[test]
fn test_pdr_solver_terminates() {
    // Test that PDR solver terminates on a simple problem
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = PdrConfig {
        max_frames: 4,
        max_iterations: 20,
        max_obligations: 10_000,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);
    let result = solver.solve();

    // This small safety problem should be solved definitively.
    match result {
        PdrResult::Safe(_) => {
            // Expected: found invariant
        }
        PdrResult::Unknown | PdrResult::NotApplicable => panic!(
            "PDR returned Unknown/NotApplicable on a trivial safe problem.\n\
             This test is a canary for silent solver regressions."
        ),
        PdrResult::Unsafe(_) => {
            panic!("BUG: PDR returned Unsafe for a known-safe problem");
        }
    }
}

#[test]
fn test_constant_sum_overflow_init_sum_skips_inductiveness_check() {
    let g = generalize::ConstantSumGeneralizer::new();

    let mut bounds = HashMap::new();
    bounds.insert("x".to_string(), generalize::InitBounds::exact(i64::MAX));
    bounds.insert("y".to_string(), generalize::InitBounds::exact(1));
    let mut ts = PanicOnInductiveTs::new(bounds);

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x, ChcExpr::int(0)),
        ChcExpr::eq(y, ChcExpr::int(0)),
    );

    let result = generalize::LemmaGeneralizer::generalize(&g, &lemma, 1, &mut ts);
    assert_eq!(result, lemma);
}

#[test]
fn test_constant_sum_overflow_state_sum_skips_inductiveness_check() {
    let g = generalize::ConstantSumGeneralizer::new();

    let mut bounds = HashMap::new();
    bounds.insert("x".to_string(), generalize::InitBounds::exact(i64::MAX - 1));
    bounds.insert("y".to_string(), generalize::InitBounds::exact(0));
    let mut ts = PanicOnInductiveTs::new(bounds);

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x, ChcExpr::int(i64::MAX)),
        ChcExpr::eq(y, ChcExpr::int(1)),
    );

    let result = generalize::LemmaGeneralizer::generalize(&g, &lemma, 1, &mut ts);
    assert_eq!(result, lemma);
}

#[test]
fn test_propagate_constants_with_mod() {
    use std::sync::Arc;

    // Test: (= A 0) ∧ (not (= (mod A 2) 0))
    // After propagation: (= 0 0) ∧ (not (= (mod 0 2) 0))
    // After simplification: true ∧ (not (= 0 0)) = true ∧ false = false
    let a_var = ChcVar::new("A", ChcSort::Int);

    // (= A 0)
    let a_eq_0 = ChcExpr::eq(ChcExpr::Var(a_var.clone()), ChcExpr::Int(0));

    // (mod A 2)
    let mod_a_2 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Var(a_var)), Arc::new(ChcExpr::Int(2))],
    );

    // (= (mod A 2) 0)
    let mod_eq_0 = ChcExpr::eq(mod_a_2, ChcExpr::Int(0));

    // (not (= (mod A 2) 0))
    let not_mod_eq_0 = ChcExpr::not(mod_eq_0);

    // (and (= A 0) (not (= (mod A 2) 0)))
    let conjunction = ChcExpr::and(a_eq_0, not_mod_eq_0);

    let propagated = conjunction.propagate_constants();

    // Should simplify to false since 0 mod 2 = 0, so (= 0 0) is true,
    // (not true) is false, and (true ∧ false) is false
    assert_eq!(propagated, ChcExpr::Bool(false));
}

#[test]
fn test_simplify_mod_constants() {
    use std::sync::Arc;

    // Test (mod 7 3) should simplify to 1
    let mod_expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(7)), Arc::new(ChcExpr::Int(3))],
    );
    let simplified = mod_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Int(1));

    // Test (mod 6 3) should simplify to 0
    let mod_expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(6)), Arc::new(ChcExpr::Int(3))],
    );
    let simplified = mod_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Int(0));

    // Test (mod 0 2) should simplify to 0
    let mod_expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(0)), Arc::new(ChcExpr::Int(2))],
    );
    let simplified = mod_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Int(0));
}

#[test]
fn test_simplify_and_contradiction() {
    use std::sync::Arc;

    // Test P AND NOT P should simplify to false
    let x = ChcVar::new("x", ChcSort::Int);
    let eq = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Mod,
            vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(ChcExpr::Int(6))],
        ),
        ChcExpr::Int(0),
    );
    let not_eq = ChcExpr::not(eq.clone());

    // Direct contradiction: (P AND NOT P)
    let and_expr = ChcExpr::and(eq.clone(), not_eq.clone());
    let simplified = and_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Bool(false));

    // Nested contradiction: ((A AND P) AND NOT P)
    let a = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));
    let nested = ChcExpr::and(ChcExpr::and(a, eq), not_eq);
    let simplified = nested.simplify_constants();
    assert_eq!(simplified, ChcExpr::Bool(false));
}

#[test]
fn test_deep_expr_traversals_do_not_overflow() {
    // Deeply nested expressions can be created by malicious or accidental input. Traversals
    // should not stack overflow.
    let depth = 50_000;

    let mut expr = ChcExpr::Bool(true);
    for _ in 0..depth {
        expr = ChcExpr::not(expr);
    }

    // Exercise multiple traversals that historically used direct recursion.
    assert_eq!(expr.simplify_constants(), ChcExpr::Bool(true));
    assert_eq!(expr.normalize_negations(), ChcExpr::Bool(true));
    assert!(expr.vars().is_empty());
    assert_eq!(expr.substitute(&[]), expr);

    let eliminated = expr.eliminate_mod().eliminate_ite();
    assert_eq!(eliminated, expr);
}

/// #2389 #2495: Verify that deeply-nested expression trees do not overflow
/// the stack during variable collection (exercises maybe_grow_expr_stack).
///
/// Uses `ChcExpr::add` (not `ChcExpr::and`) because `and_all` flattens
/// nested And nodes into a single flat node, defeating the depth test.
/// Add/Sub/Mul/Implies constructors do NOT flatten, producing genuinely
/// deep trees.
///
/// Depth must stay under MAX_EXPR_RECURSION_DEPTH (500) so that
/// collect_vars_dedupe traverses the full tree. Previous depth of 10_000
/// caused SIGABRT: the depth guard truncated vars() to 500, the assertion
/// panicked, and recursive Arc drop during unwinding overflowed the stack.
#[test]
fn test_deep_add_tree_traversals_do_not_overflow() {
    let depth = 400;

    // Build a right-skewed Add tree: (+ x0 (+ x1 (+ x2 ... 0)))
    // Each add creates a 2-child node without flattening.
    let mut expr = ChcExpr::Int(0);
    for i in 0..depth {
        let var = ChcExpr::var(ChcVar::new(format!("x{i}"), ChcSort::Int));
        expr = ChcExpr::add(var, expr);
    }

    // vars() exercises maybe_grow_expr_stack in collect_vars_dedupe.
    let v = expr.vars();
    assert_eq!(v.len(), depth);

    // Leak to avoid recursive Drop overflow (#2495): the default Rust Drop
    // for deeply-nested Arc<ChcExpr> recurses through the tree.
    std::mem::forget(expr);
}
