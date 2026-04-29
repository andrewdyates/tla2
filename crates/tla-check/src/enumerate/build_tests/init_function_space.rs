// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_constructor_in_init() {
    use tla_core::ast::Expr;

    let src = r#"
---- MODULE Test ----
CONSTANT N
VARIABLE pc

ProcSet == 1..N

Init == pc = [p \in ProcSet |-> "b0"]
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);

    // Print the concrete syntax tree (Debug format)
    eprintln!("\n=== CST (debug) ===");
    eprintln!("{:#?}", tree);

    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    eprintln!("\nLower errors: {:?}", lower_result.errors);

    let module = lower_result.module.unwrap();

    eprintln!("\n=== All operators ===");
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            eprintln!(
                "Op '{}': body type = {:?}",
                def.name.node,
                std::mem::discriminant(&def.body.node)
            );
            // Match on the body to show more detail
            match &def.body.node {
                Expr::Ident(name, _) => eprintln!("  -> Ident({})", name),
                Expr::Eq(lhs, rhs) => {
                    eprintln!("  -> Eq(lhs={:?}, rhs={:?})", lhs.node, rhs.node);
                }
                other => eprintln!("  -> Other: {:?}", other),
            }
        }
    }

    let (_, mut ctx, vars) = setup_module(src);

    // Bind N = 3
    ctx.bind_mut("N", Value::int(3));

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    // The Init body should be Eq, not Ident
    match &init_def.body.node {
        Expr::Eq(_, _) => eprintln!("Init body is correctly an Eq"),
        Expr::Ident(name, _) => panic!("Init body is incorrectly Ident({})", name),
        other => panic!("Init body is unexpected: {:?}", other),
    }

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None);
    eprintln!("Branches: {:?}", branches);
    assert!(
        branches.is_some(),
        "Failed to extract constraints from Init with function constructor"
    );

    // Verify the constraint value is a function or sequence
    // (domain 1..N becomes a Seq with our semantics)
    let branches = branches.unwrap();
    assert_eq!(branches.len(), 1, "Expected one branch");
    let branch = &branches[0];
    assert_eq!(branch.len(), 1, "Expected one constraint");
    match &branch[0] {
        Constraint::Eq(name, value) => {
            assert_eq!(name.as_ref() as &str, "pc");
            // Domain 1..N creates a Seq (functions with domain 1..n are sequences in TLA+)
            assert!(
                matches!(value, Value::Func(_) | Value::IntFunc(_) | Value::Seq(_)),
                "Expected function or sequence value, got {:?}",
                value
            );
        }
        other => panic!("Expected Eq constraint, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_function_space_membership() {
    // Test grid \in [Pos -> BOOLEAN] pattern
    // Use explicit set enum to avoid operator lookup
    let src = r#"
---- MODULE Test ----
VARIABLE grid
Init == grid \in [{<<1, 1>>, <<1, 2>>} -> {TRUE, FALSE}]
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    eprintln!("=== CST ===");
    eprintln!("{:#?}", tree);

    let lower_result = lower(FileId(0), &tree);
    eprintln!("Lower errors: {:?}", lower_result.errors);

    let module = lower_result.module.unwrap();
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            eprintln!("Op '{}' body: {:?}", def.name.node, def.body.node);
        }
    }

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut vars = Vec::new();
    for unit in &module.units {
        if let tla_core::ast::Unit::Variable(var_names) = &unit.node {
            for var in var_names {
                let name = Arc::from(var.node.as_str());
                ctx.register_var(Arc::clone(&name));
                vars.push(name);
            }
        }
    }

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    eprintln!("Init body (in test): {:?}", init_def.body.node);

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None);
    eprintln!("Branches: {:?}", branches);

    assert!(
        branches.is_some(),
        "Should extract constraints from function space membership"
    );

    let branches = branches.unwrap();
    // {<<1,1>>, <<1,2>>} has 2 elements, {TRUE, FALSE} has 2 elements
    // So [... -> ...] has 2^2 = 4 functions
    // After streaming init change (cd2a89896), Enumerable domains need a
    // context to materialize. Pass the ctx we already built above.
    let states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .unwrap()
        .unwrap();
    assert_eq!(states.len(), 4, "Expected 4 initial states (2^2 functions)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_function_space_with_operator_ref() {
    // Test grid \in [Pos -> BOOLEAN] where Pos is an operator
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE grid

Pos == {<<1, 1>>, <<1, 2>>}
Init == grid \in [Pos -> BOOLEAN]
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    eprintln!("=== CST with Pos ===");
    eprintln!("{:#?}", tree);

    let lower_result = lower(FileId(0), &tree);
    eprintln!("Lower errors: {:?}", lower_result.errors);

    let module = lower_result.module.unwrap();
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            eprintln!("Op '{}' body: {:?}", def.name.node, def.body.node);
        }
    }

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut vars = Vec::new();
    for unit in &module.units {
        if let tla_core::ast::Unit::Variable(var_names) = &unit.node {
            for var in var_names {
                let name = Arc::from(var.node.as_str());
                ctx.register_var(Arc::clone(&name));
                vars.push(name);
            }
        }
    }

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    eprintln!("Init body with Pos: {:?}", init_def.body.node);

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None);
    eprintln!("Branches with Pos: {:?}", branches);

    assert!(
        branches.is_some(),
        "Should extract constraints from function space membership with operator reference"
    );

    let branches = branches.unwrap();
    // After streaming init change (cd2a89896), Enumerable domains need a
    // context to materialize. Pass the ctx we already built above.
    let states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .unwrap()
        .unwrap();
    assert_eq!(states.len(), 4, "Expected 4 initial states (2^2 functions)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deferred_in_constraint_with_setpred_domain() {
    // Regression for SetPred centralization: deferred In constraints whose
    // domain references an already-bound variable must enumerate lazy SetPred
    // values via eval_iter_set_for_init.
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
VARIABLE x, y
Init ==
    /\ x \in {1, 2}
    /\ y \in {s \in SUBSET {1, 2} : Cardinality(s) = x}
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Init" => Some(def),
            _ => None,
        })
        .expect("invariant: Init operator should exist");

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None)
        .expect("Init constraints should extract for deferred SetPred membership");
    let states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .expect("enumeration should not fail")
        .expect("small finite domain should use in-memory state enumeration");

    assert_eq!(
        states.len(),
        3,
        "expected x=1 with two singleton y values, and x=2 with one pair y value"
    );

    let xy_pairs: Vec<(i64, Value)> = states
        .iter()
        .map(|s| {
            let x = s
                .get("x")
                .and_then(tla_value::Value::as_i64)
                .expect("x should be bound to integer");
            let y = s.get("y").expect("y should be bound").clone();
            (x, y)
        })
        .collect();

    assert!(xy_pairs.contains(&(1, Value::set([Value::int(1)]))));
    assert!(xy_pairs.contains(&(1, Value::set([Value::int(2)]))));
    assert!(xy_pairs.contains(&(2, Value::set([Value::int(1), Value::int(2)]))));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_exists_two_bounds_setpred_domains() {
    // Regression for SetPred centralization: multi-bound existential extraction
    // must enumerate both SetPred domains correctly in init constraints.
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
VARIABLE a, b
Init ==
    \E x \in {s \in SUBSET {1, 2, 3} : Cardinality(s) = 1},
      y \in {t \in SUBSET {10, 20} : Cardinality(t) = 1}:
        /\ a = x
        /\ b = y
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Init" => Some(def),
            _ => None,
        })
        .expect("invariant: Init operator should exist");

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None)
        .expect("Init constraints should extract for two-bound SetPred existential");
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .expect("enumeration should not fail")
        .expect("small finite domain should use in-memory state enumeration");

    assert_eq!(
        states.len(),
        6,
        "expected 3 singleton choices for a crossed with 2 singleton choices for b"
    );

    let ab_pairs: Vec<(Value, Value)> = states
        .iter()
        .map(|s| {
            let a = s.get("a").expect("a should be bound").clone();
            let b = s.get("b").expect("b should be bound").clone();
            (a, b)
        })
        .collect();

    for a in [
        Value::set([Value::int(1)]),
        Value::set([Value::int(2)]),
        Value::set([Value::int(3)]),
    ] {
        for b in [Value::set([Value::int(10)]), Value::set([Value::int(20)])] {
            assert!(
                ab_pairs.contains(&(a.clone(), b.clone())),
                "missing expected pair (a={a:?}, b={b:?})"
            );
        }
    }
}

/// Regression test for #2575: RECURSIVE operators in Init must not cause infinite
/// inlining during constraint extraction. The self-recursive operator should be
/// treated as a Filter constraint, allowing other domain constraints to be
/// extracted normally.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_recursive_operator_in_init_becomes_filter_2575() {
    let src = r#"
---- MODULE Test ----
EXTENDS Naturals

RECURSIVE RecPred(_)
RecPred(n) ==
    IF n = 0 THEN TRUE
    ELSE RecPred(n - 1)

VARIABLE x
Init == x \in {0, 1, 2} /\ RecPred(x)
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = find_operator(&module, "Init");

    // This must complete without hanging — before #2575 fix, extract_init_constraints
    // would infinitely inline RecPred's body because it references itself.
    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None)
        .expect("constraint extraction should succeed for RECURSIVE operator in Init");

    // Should have exactly one branch (single conjunction)
    assert_eq!(branches.len(), 1, "expected single constraint branch");

    // The branch should contain domain constraint for x and a Filter for RecPred(x)
    let branch = &branches[0];
    let has_domain_for_x = branch
        .iter()
        .any(|c| matches!(c, Constraint::In(name, _) if name == "x"));
    let has_filter = branch.iter().any(|c| matches!(c, Constraint::Filter(_)));

    assert!(
        has_domain_for_x,
        "x \\in {{0, 1, 2}} should extract a domain constraint even with RECURSIVE operator"
    );
    assert!(
        has_filter,
        "RecPred(x) should become a Filter constraint (not inlined infinitely)"
    );
}
