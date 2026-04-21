// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_core::ast::{Expr, Unit};
use tla_core::name_intern::NameId;
use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_action_subscripts_expand_to_unchanged_sugar() {
    let source = r"
---- MODULE Main ----
Sub == [Next]_vars
Angle == <<Next>>_vars
SubMod == [M!Next]_M!vars
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");

    let mut saw_sub = false;
    let mut saw_angle = false;
    let mut saw_sub_mod = false;

    for unit in &module.units {
        let Unit::Operator(def) = &unit.node else {
            continue;
        };

        match def.name.node.as_str() {
            "Sub" => {
                let Expr::Or(action, unchanged) = &def.body.node else {
                    panic!("expected Sub body to be Or, got: {:?}", def.body.node);
                };
                let Expr::Ident(name, NameId::INVALID) = &action.node else {
                    panic!("expected Sub action to be Ident, got: {:?}", action.node);
                };
                assert_eq!(name, "Next");
                let Expr::Unchanged(sub) = &unchanged.node else {
                    panic!(
                        "expected Sub rhs to be Unchanged, got: {:?}",
                        unchanged.node
                    );
                };
                let Expr::Ident(v, NameId::INVALID) = &sub.node else {
                    panic!(
                        "expected Sub UNCHANGED arg to be Ident, got: {:?}",
                        sub.node
                    );
                };
                assert_eq!(v, "vars");
                saw_sub = true;
            }
            "Angle" => {
                let Expr::And(action, not_unchanged) = &def.body.node else {
                    panic!("expected Angle body to be And, got: {:?}", def.body.node);
                };
                let Expr::Ident(name, NameId::INVALID) = &action.node else {
                    panic!("expected Angle action to be Ident, got: {:?}", action.node);
                };
                assert_eq!(name, "Next");
                let Expr::Not(inner) = &not_unchanged.node else {
                    panic!(
                        "expected Angle rhs to be Not, got: {:?}",
                        not_unchanged.node
                    );
                };
                let Expr::Unchanged(sub) = &inner.node else {
                    panic!(
                        "expected Angle rhs inner to be Unchanged, got: {:?}",
                        inner.node
                    );
                };
                let Expr::Ident(v, NameId::INVALID) = &sub.node else {
                    panic!(
                        "expected Angle UNCHANGED arg to be Ident, got: {:?}",
                        sub.node
                    );
                };
                assert_eq!(v, "vars");
                saw_angle = true;
            }
            "SubMod" => {
                let Expr::Or(action, unchanged) = &def.body.node else {
                    panic!("expected SubMod body to be Or, got: {:?}", def.body.node);
                };
                let Expr::ModuleRef(m, op, args) = &action.node else {
                    panic!(
                        "expected SubMod action to be ModuleRef, got: {:?}",
                        action.node
                    );
                };
                assert_eq!(m.name(), "M");
                assert_eq!(op, "Next");
                assert!(args.is_empty());
                let Expr::Unchanged(sub) = &unchanged.node else {
                    panic!(
                        "expected SubMod rhs to be Unchanged, got: {:?}",
                        unchanged.node
                    );
                };
                let Expr::ModuleRef(m2, op2, args2) = &sub.node else {
                    panic!(
                        "expected SubMod UNCHANGED arg to be ModuleRef, got: {:?}",
                        sub.node
                    );
                };
                assert_eq!(m2.name(), "M");
                assert_eq!(op2, "vars");
                assert!(args2.is_empty());
                saw_sub_mod = true;
            }
            _ => {}
        }
    }

    assert!(saw_sub, "did not find operator Sub");
    assert!(saw_angle, "did not find operator Angle");
    assert!(saw_sub_mod, "did not find operator SubMod");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn top_level_action_subscript_bodies_keep_real_syntax_provenance() {
    let source = r"
---- MODULE Main ----
RealBox == [Next]_vars
ExpandedBox == Next \/ UNCHANGED vars
RealAngle == <<Next>>_vars
ExpandedAngle == Next /\ ~UNCHANGED vars
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");

    let real_box = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "RealBox" => Some(def),
            _ => None,
        })
        .expect("did not find operator RealBox");
    let expanded_box = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "ExpandedBox" => Some(def),
            _ => None,
        })
        .expect("did not find operator ExpandedBox");
    let real_angle = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "RealAngle" => Some(def),
            _ => None,
        })
        .expect("did not find operator RealAngle");
    let expanded_angle = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "ExpandedAngle" => Some(def),
            _ => None,
        })
        .expect("did not find operator ExpandedAngle");

    assert!(
        module.action_subscript_spans.contains(&real_box.body.span),
        "top-level [A]_v body span must preserve real syntax provenance"
    );
    assert!(
        !module
            .action_subscript_spans
            .contains(&expanded_box.body.span),
        "explicit box expansion must not be mistaken for real [A]_v syntax"
    );
    assert!(
        module
            .action_subscript_spans
            .contains(&real_angle.body.span),
        "top-level <<A>>_v body span must preserve real syntax provenance"
    );
    assert!(
        !module
            .action_subscript_spans
            .contains(&expanded_angle.body.span),
        "explicit angle expansion must not be mistaken for real <<A>>_v syntax"
    );
}

/// Regression test for #465: identifier-style subscripts like `_vars` must be
/// consumed as part of `[A]_vars` even when nested under temporal operators.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn parse_always_action_with_identifier_subscript() {
    let source = r"
---- MODULE Main ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let spec = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "Spec" => Some(def),
            _ => None,
        })
        .expect("did not find operator Spec");

    // Spec body should be: Init /\ [][Next \/ UNCHANGED vars]
    // The And's RHS should be an Always containing Or(Next, Unchanged(vars))
    let Expr::And(_, always) = &spec.body.node else {
        panic!("expected Spec body to be And, got: {:?}", spec.body.node);
    };

    let Expr::Always(inner) = &always.node else {
        panic!("expected Spec rhs to be Always, got: {:?}", always.node);
    };

    let Expr::Or(action, unchanged) = &inner.node else {
        panic!("expected [] operand to be Or, got: {:?}", inner.node);
    };
    assert!(
        module.action_subscript_spans.contains(&inner.span),
        "real [A]_v syntax must preserve action-subscript provenance"
    );

    let Expr::Ident(action_name, NameId::INVALID) = &action.node else {
        panic!("expected action to be Ident, got: {:?}", action.node);
    };
    assert_eq!(action_name, "Next");

    let Expr::Unchanged(vars_expr) = &unchanged.node else {
        panic!("expected rhs to be Unchanged, got: {:?}", unchanged.node);
    };
    let Expr::Ident(v, NameId::INVALID) = &vars_expr.node else {
        panic!(
            "expected UNCHANGED arg to be Ident, got: {:?}",
            vars_expr.node
        );
    };
    assert_eq!(v, "vars");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn action_subscript_provenance_distinguishes_real_subscript_from_expansion() {
    let source = r"
---- MODULE Main ----
VARIABLE x
vars == <<x>>
Next == x' = x + 1
Real == [][Next]_vars
Expanded == [](Next \/ UNCHANGED vars)
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let real = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "Real" => Some(def),
            _ => None,
        })
        .expect("did not find operator Real");
    let expanded = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "Expanded" => Some(def),
            _ => None,
        })
        .expect("did not find operator Expanded");

    let Expr::Always(real_inner) = &real.body.node else {
        panic!("expected Real body to be Always, got: {:?}", real.body.node);
    };
    let Expr::Always(expanded_inner) = &expanded.body.node else {
        panic!(
            "expected Expanded body to be Always, got: {:?}",
            expanded.body.node
        );
    };

    assert!(
        module.action_subscript_spans.contains(&real_inner.span),
        "real [A]_v syntax must be recorded"
    );
    assert!(
        !module.action_subscript_spans.contains(&expanded_inner.span),
        "explicit expansion must not be mistaken for [A]_v syntax"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn action_angle_subscript_provenance_distinguishes_real_subscript_from_expansion() {
    let source = r"
---- MODULE Main ----
VARIABLE x
vars == <<x>>
Next == x' = x + 1
RealAngle == []<<Next>>_vars
ExpandedAngle == [](Next /\ ~UNCHANGED vars)
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let real = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "RealAngle" => Some(def),
            _ => None,
        })
        .expect("did not find operator RealAngle");
    let expanded = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node.as_str() == "ExpandedAngle" => Some(def),
            _ => None,
        })
        .expect("did not find operator ExpandedAngle");

    let Expr::Always(real_inner) = &real.body.node else {
        panic!(
            "expected RealAngle body to be Always, got: {:?}",
            real.body.node
        );
    };
    let Expr::Always(expanded_inner) = &expanded.body.node else {
        panic!(
            "expected ExpandedAngle body to be Always, got: {:?}",
            expanded.body.node
        );
    };

    assert!(
        module.action_subscript_spans.contains(&real_inner.span),
        "real <<A>>_v syntax must be recorded"
    );
    assert!(
        !module.action_subscript_spans.contains(&expanded_inner.span),
        "explicit expansion must not be mistaken for <<A>>_v syntax"
    );
}

/// Regression test for #451: underscore-prefixed identifiers should NOT be parsed
/// as action subscripts unless they follow `]` or `>>` (action bracket closers).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn underscore_prefixed_identifiers_are_not_action_subscripts_after_arbitrary_expressions() {
    // Apalache-style `LET __Dom == { ... } __Rng == { ... }` where the parser
    // previously misinterpreted `__Rng` as a postfix action subscript on the preceding set.
    let source = r"
---- MODULE Main ----
SetAsFun(__S) ==
    LET __Dom == { __x : <<__x, __y>> \in __S }
        __Rng == { __y : <<__x, __y>> \in __S }
    IN __Dom
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
}
