// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_simple_equality_constraints() {
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 1
====
"#;
    let (module, ctx, vars) = setup_module(src);

    // Find Init definition
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

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    assert_eq!(branches.len(), 1);
    assert_eq!(branches[0].len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_init_constraints_preserves_filter_order_with_print_1004() {
    // Regression for #1004: constraint extraction must preserve conjunct order so
    // side-effecting TLC operators like Print are evaluated in TLC order.
    //
    // In particular, Print after a runtime error (like applying a model value as a function)
    // must not be evaluated.
    let src = r#"
---- MODULE Test ----
EXTENDS TLC
VARIABLE x
CONSTANT A

Req == [mask |-> A]

Init == /\ x = 1
        /\ Print("Should report error for applying model value to arg", TRUE)
        /\ Req.mask[1] = 1
        /\ Print("Should never get this far", TRUE)
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                (def.name.node == "Init").then_some(def)
            } else {
                None
            }
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    assert_eq!(branches.len(), 1);
    let branch = &branches[0];
    assert_eq!(branch.len(), 4);

    match &branch[0] {
        Constraint::Eq(name, value) => {
            assert_eq!(name.as_str(), "x");
            assert_eq!(value, &Value::int(1));
        }
        other => panic!("expected Eq constraint, got {other:?}"),
    }

    match &branch[1] {
        Constraint::Filter(expr) => match &expr.node {
            tla_core::ast::Expr::Apply(op, args) => {
                assert!(matches!(&op.node, tla_core::ast::Expr::Ident(n, _) if n == "Print"));
                assert!(matches!(
                    &args[0].node,
                    tla_core::ast::Expr::String(s) if s == "Should report error for applying model value to arg"
                ));
            }
            other => panic!("expected Print Apply filter, got {other:?}"),
        },
        other => panic!("expected Filter constraint, got {other:?}"),
    }

    match &branch[2] {
        Constraint::Filter(expr) => match &expr.node {
            tla_core::ast::Expr::Eq(lhs, _rhs) => {
                assert!(matches!(&lhs.node, tla_core::ast::Expr::FuncApply(_, _)));
            }
            other => panic!("expected Eq(FuncApply(..), ..) filter, got {other:?}"),
        },
        other => panic!("expected Filter constraint, got {other:?}"),
    }

    match &branch[3] {
        Constraint::Filter(expr) => match &expr.node {
            tla_core::ast::Expr::Apply(op, args) => {
                assert!(matches!(&op.node, tla_core::ast::Expr::Ident(n, _) if n == "Print"));
                assert!(matches!(
                    &args[0].node,
                    tla_core::ast::Expr::String(s) if s == "Should never get this far"
                ));
            }
            other => panic!("expected Print Apply filter, got {other:?}"),
        },
        other => panic!("expected Filter constraint, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_init_constraints_resolves_replaced_zero_arg_candidate() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == TypeOK /\ x > 0
TypeOK == x \in {99}
MCTypeOK == x \in {0, 1, 2}
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    ctx.add_op_replacement("TypeOK".to_string(), "MCTypeOK".to_string());

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                (def.name.node == "Init").then_some(def)
            } else {
                None
            }
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None)
        .expect("replacement-routed init should remain extractable");
    let states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .unwrap()
        .expect("replacement-routed init extraction should enumerate states");

    let mut xs: Vec<Value> = states
        .into_iter()
        .map(|state| {
            state
                .get("x")
                .cloned()
                .expect("enumerated state should bind x")
        })
        .collect();
    xs.sort();
    assert_eq!(xs, vec![Value::int(1), Value::int(2)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_constraints_to_bulk_enforces_filter_with_deferred_var() {
    // Regression: bulk enumeration must enforce Constraint::Filter semantics even when
    // the filter depends on deferred variables (bound after immediate enumeration).
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x, y

Init == /\ x = 1
        /\ y = x + 1
        /\ y > 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

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

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();

    let vars_len = ctx.var_registry().len();
    let mut storage = crate::arena::BulkStateStorage::new(vars_len, 4);
    let count =
        enumerate_constraints_to_bulk(&mut ctx, &vars, &branches, &mut storage, |_values, _ctx| {
            Ok(true)
        })
        .unwrap()
        .expect("expected streaming constraint enumeration");

    assert_eq!(count, 1);
    assert_eq!(storage.len(), 1);
    assert_eq!(storage.get_state(0u32), &[Value::int(1), Value::int(2)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_constraints_to_bulk_skips_branch_with_empty_deferred_domain() {
    let src = r#"
---- MODULE Test ----
VARIABLE x, y

Init == /\ x = 1
        /\ y \in IF x = 2 THEN {3} ELSE {}
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

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

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    assert_eq!(branches.len(), 1);
    assert_eq!(branches[0].len(), 2);
    assert!(
        matches!(&branches[0][0], Constraint::Eq(name, value) if name == "x" && value == &Value::int(1))
    );
    assert!(matches!(
        &branches[0][1],
        Constraint::DeferredIn(name, _) if name == "y"
    ));

    let states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .unwrap()
        .unwrap();
    assert!(states.is_empty());

    let vars_len = ctx.var_registry().len();
    let mut storage = crate::arena::BulkStateStorage::new(vars_len, 4);
    let count =
        enumerate_constraints_to_bulk(&mut ctx, &vars, &branches, &mut storage, |_values, _ctx| {
            Ok(true)
        })
        .unwrap()
        .expect("expected streaming constraint enumeration");

    assert_eq!(count, 0);
    assert_eq!(storage.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_constraints_to_bulk_empty_immediate_domain_produces_zero_states() {
    // Regression test for #1720: when an immediate variable has an empty domain,
    // the bulk path must produce zero states for that branch (not skip the variable
    // and proceed with an unconstrained cross-product).
    let src = r#"
---- MODULE Test ----
VARIABLE x, y

Init == \/ (x \in {} /\ y = 1)
        \/ (x = 2 /\ y = 3)
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let init_def = find_operator(&module, "Init");

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    // Two branches: one with empty domain for x, one with concrete values.
    assert!(branches.len() >= 1);

    // Non-bulk path: should produce exactly 1 state from the second branch
    let states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .unwrap()
        .unwrap();
    assert_eq!(
        states.len(),
        1,
        "non-bulk: only the (x=2, y=3) branch should produce states"
    );
    assert_eq!(states[0].get("x").unwrap(), &Value::int(2));
    assert_eq!(states[0].get("y").unwrap(), &Value::int(3));

    // Bulk path: must match non-bulk — exactly 1 state
    let vars_len = ctx.var_registry().len();
    let mut storage = crate::arena::BulkStateStorage::new(vars_len, 4);
    let count =
        enumerate_constraints_to_bulk(&mut ctx, &vars, &branches, &mut storage, |_values, _ctx| {
            Ok(true)
        })
        .unwrap()
        .expect("expected streaming constraint enumeration");

    assert_eq!(
        count, 1,
        "bulk: empty immediate domain branch must produce 0 states"
    );
    assert_eq!(storage.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_init_constraints_preserves_lazy_filtered_record_domain_3228() {
    let src = r#"
---- MODULE Test ----
EXTENDS Naturals
VARIABLE can

Can == [black : 0..2, white : 0..2]
Init == can \in {c \in Can : c.black + c.white \in 1..2}
====
"#;
    let (module, ctx, vars) = setup_module(src);
    let init_def = find_operator(&module, "Init");

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None)
        .expect("CoffeeCan-shaped init should extract constraints");

    assert_eq!(branches.len(), 1);
    assert_eq!(branches[0].len(), 1);
    match &branches[0][0] {
        Constraint::In(name, InitDomain::Enumerable(_)) => {
            assert_eq!(name, "can");
        }
        other => panic!("expected lazy enumerable init domain, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_init_constraints_defers_state_dependent_setpred_domain() {
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
    let init_def = find_operator(&module, "Init");

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None)
        .expect("state-dependent SetPred init should still extract");

    assert_eq!(branches.len(), 1);
    assert_eq!(branches[0].len(), 2);
    assert!(matches!(&branches[0][0], Constraint::In(name, _) if name == "x"));
    assert!(
        matches!(&branches[0][1], Constraint::DeferredIn(name, _) if name == "y"),
        "expected y domain to defer until x is bound, got {:?}",
        branches[0][1]
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_init_constraints_resolves_replaced_ident_and_apply_operators() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Init == TypeOK /\ Match(1)
TypeOK == x \in {99}
MCTypeOK == x \in {1, 2}
Match(v) == x = 99 /\ x = v
MCMatch(v) == x = v
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let init_def = find_operator(&module, "Init");

    let mut config = crate::Config::default();
    config.constants.insert(
        "TypeOK".to_string(),
        crate::ConstantValue::Replacement("MCTypeOK".to_string()),
    );
    config.constants.insert(
        "Match".to_string(),
        crate::ConstantValue::Replacement("MCMatch".to_string()),
    );
    crate::bind_constants_from_config(&mut ctx, &config)
        .expect("operator replacements should bind into init extraction ctx");

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None)
        .expect("replacement-routed init should still extract");
    let states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .expect("replacement-routed init enumeration should not error")
        .expect("replacement-routed init enumeration should stay on extracted path");

    assert_eq!(
        states.len(),
        1,
        "both zero-arg and applied init operators must honor config replacements"
    );
    assert_eq!(
        states[0].get("x"),
        Some(&Value::int(1)),
        "replacement-routed init extraction should enumerate the MCTypeOK/MCMatch state"
    );
}
