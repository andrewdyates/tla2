// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use tla_core::ast::OpParam;
use tla_core::{Span, Spanned};

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned {
        node,
        span: Span::default(),
    }
}

fn make_op_def(name: &str, body: Expr) -> OperatorDef {
    OperatorDef {
        name: spanned(name.to_string()),
        params: vec![],
        body: spanned(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

fn make_op_def_with_params(name: &str, params: Vec<&str>, body: Expr) -> OperatorDef {
    OperatorDef {
        name: spanned(name.to_string()),
        params: params
            .into_iter()
            .map(|p| OpParam {
                name: spanned(p.to_string()),
                arity: 0,
            })
            .collect(),
        body: spanned(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

// --- expr_references_trace (bare, non-alias) ---

#[test]
fn test_bare_trace_ident_detected() {
    assert!(expr_references_trace(&Expr::Ident(
        "Trace".to_string(),
        tla_core::name_intern::NameId::INVALID
    )));
}

#[test]
fn test_non_trace_ident_not_detected() {
    assert!(!expr_references_trace(&Expr::Ident(
        "Foo".to_string(),
        tla_core::name_intern::NameId::INVALID
    )));
}

#[test]
fn test_tlcext_trace_module_ref_detected() {
    let expr = Expr::ModuleRef(
        ModuleTarget::Named("TLCExt".to_string()),
        "Trace".to_string(),
        vec![],
    );
    assert!(expr_references_trace(&expr));
}

#[test]
fn test_non_tlcext_module_ref_not_detected() {
    let expr = Expr::ModuleRef(
        ModuleTarget::Named("Other".to_string()),
        "Trace".to_string(),
        vec![],
    );
    assert!(!expr_references_trace(&expr));
}

// --- alias-aware detection ---

#[test]
fn test_alias_trace_detected_with_aliases() {
    let aliases: HashSet<String> = ["MyTLCExt".to_string()].into_iter().collect();
    let expr = Expr::ModuleRef(
        ModuleTarget::Named("MyTLCExt".to_string()),
        "Trace".to_string(),
        vec![],
    );
    assert!(expr_references_trace_with_aliases(&expr, &aliases));
}

#[test]
fn test_alias_non_trace_op_not_detected() {
    let aliases: HashSet<String> = ["MyTLCExt".to_string()].into_iter().collect();
    let expr = Expr::ModuleRef(
        ModuleTarget::Named("MyTLCExt".to_string()),
        "AssertEq".to_string(),
        vec![],
    );
    assert!(!expr_references_trace_with_aliases(&expr, &aliases));
}

// --- collect_trace_module_aliases ---

#[test]
fn test_collect_aliases_finds_instance_tlcext() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert(
        "TE".to_string(),
        make_op_def("TE", Expr::InstanceExpr("TLCExt".to_string(), vec![])),
    );
    op_defs.insert(
        "OtherInv".to_string(),
        make_op_def("OtherInv", Expr::Bool(true)),
    );
    let aliases = collect_trace_module_aliases(&op_defs);
    assert_eq!(aliases, ["TE".to_string()].into_iter().collect());
}

#[test]
fn test_collect_aliases_ignores_parameterized_instance() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    // Operator with params (e.g., `Alias(x) == INSTANCE TLCExt WITH ...`) is not a bare alias
    op_defs.insert(
        "ParamAlias".to_string(),
        make_op_def_with_params(
            "ParamAlias",
            vec!["x"],
            Expr::InstanceExpr("TLCExt".to_string(), vec![]),
        ),
    );
    let aliases = collect_trace_module_aliases(&op_defs);
    assert!(aliases.is_empty());
}

#[test]
fn test_collect_aliases_ignores_non_tlcext_instance() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert(
        "Chan".to_string(),
        make_op_def("Chan", Expr::InstanceExpr("Channel".to_string(), vec![])),
    );
    let aliases = collect_trace_module_aliases(&op_defs);
    assert!(aliases.is_empty());
}

// --- compute_uses_trace ---

fn make_config(
    invariants: Vec<&str>,
    constraints: Vec<&str>,
    action_constraints: Vec<&str>,
) -> Config {
    Config {
        invariants: invariants.into_iter().map(String::from).collect(),
        constraints: constraints.into_iter().map(String::from).collect(),
        action_constraints: action_constraints.into_iter().map(String::from).collect(),
        ..Config::default()
    }
}

#[test]
fn test_compute_uses_trace_invariant_with_bare_trace() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert(
        "Inv".to_string(),
        make_op_def(
            "Inv",
            Expr::Ident("Trace".to_string(), tla_core::name_intern::NameId::INVALID),
        ),
    );
    let config = make_config(vec!["Inv"], vec![], vec![]);
    assert!(compute_uses_trace(&config, &op_defs).unwrap());
}

#[test]
fn test_compute_uses_trace_no_trace_refs() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert("Inv".to_string(), make_op_def("Inv", Expr::Bool(true)));
    let config = make_config(vec!["Inv"], vec![], vec![]);
    assert!(!compute_uses_trace(&config, &op_defs).unwrap());
}

#[test]
fn test_compute_uses_trace_constraint_with_trace() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert("Inv".to_string(), make_op_def("Inv", Expr::Bool(true)));
    op_defs.insert(
        "MyConstraint".to_string(),
        make_op_def(
            "MyConstraint",
            Expr::Ident("Trace".to_string(), tla_core::name_intern::NameId::INVALID),
        ),
    );
    let config = make_config(vec!["Inv"], vec!["MyConstraint"], vec![]);
    assert!(compute_uses_trace(&config, &op_defs).unwrap());
}

#[test]
fn test_compute_uses_trace_action_constraint_with_trace() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert("Inv".to_string(), make_op_def("Inv", Expr::Bool(true)));
    op_defs.insert(
        "AC".to_string(),
        make_op_def(
            "AC",
            Expr::Ident("Trace".to_string(), tla_core::name_intern::NameId::INVALID),
        ),
    );
    let config = make_config(vec!["Inv"], vec![], vec!["AC"]);
    assert!(compute_uses_trace(&config, &op_defs).unwrap());
}

#[test]
fn test_compute_uses_trace_alias_form_detected() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    // TE == INSTANCE TLCExt
    op_defs.insert(
        "TE".to_string(),
        make_op_def("TE", Expr::InstanceExpr("TLCExt".to_string(), vec![])),
    );
    // Inv uses TE!Trace
    op_defs.insert(
        "Inv".to_string(),
        make_op_def(
            "Inv",
            Expr::ModuleRef(
                ModuleTarget::Named("TE".to_string()),
                "Trace".to_string(),
                vec![],
            ),
        ),
    );
    let config = make_config(vec!["Inv"], vec![], vec![]);
    assert!(compute_uses_trace(&config, &op_defs).unwrap());
}

#[test]
fn test_compute_uses_trace_alias_in_quantifier_bound_domain() {
    // Regression: bound_var_references_trace must propagate trace_aliases.
    // Without alias propagation, \A i \in 1..Len(TE!Trace) would NOT be
    // detected when TE is an alias for TLCExt.
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    // TE == INSTANCE TLCExt
    op_defs.insert(
        "TE".to_string(),
        make_op_def("TE", Expr::InstanceExpr("TLCExt".to_string(), vec![])),
    );
    // Inv == \A i \in {TE!Trace} : TRUE
    // The bound domain references TE!Trace (alias form)
    let te_trace = Expr::ModuleRef(
        ModuleTarget::Named("TE".to_string()),
        "Trace".to_string(),
        vec![],
    );
    let domain = Expr::SetEnum(vec![spanned(te_trace)]);
    let bound = tla_core::ast::BoundVar {
        name: spanned("i".to_string()),
        domain: Some(Box::new(spanned(domain))),
        pattern: None,
    };
    let inv_body = Expr::Forall(vec![bound], Box::new(spanned(Expr::Bool(true))));
    op_defs.insert("Inv".to_string(), make_op_def("Inv", inv_body));

    let config = make_config(vec!["Inv"], vec![], vec![]);
    assert!(
        compute_uses_trace(&config, &op_defs).unwrap(),
        "alias-form Trace in quantifier bound domain must be detected"
    );
}

#[test]
fn test_compute_uses_trace_missing_invariant_fails_loud() {
    let op_defs: HashMap<String, OperatorDef> = HashMap::new();
    let config = make_config(vec!["NonExistent"], vec![], vec![]);
    let result = compute_uses_trace(&config, &op_defs);
    assert!(result.is_err());
}

#[test]
fn test_compute_uses_trace_missing_constraint_fails_loud() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert("Inv".to_string(), make_op_def("Inv", Expr::Bool(true)));
    let config = make_config(vec!["Inv"], vec!["Missing"], vec![]);
    let result = compute_uses_trace(&config, &op_defs);
    assert!(result.is_err());
}

#[test]
fn test_compute_uses_trace_missing_action_constraint_fails_loud() {
    let mut op_defs: HashMap<String, OperatorDef> = HashMap::new();
    op_defs.insert("Inv".to_string(), make_op_def("Inv", Expr::Bool(true)));
    let config = make_config(vec!["Inv"], vec![], vec!["Missing"]);
    let result = compute_uses_trace(&config, &op_defs);
    assert!(result.is_err());
}

#[test]
fn test_compute_uses_trace_sequential_and_parallel_agree() {
    // Both HashMap and FxHashMap should work identically
    let mut std_ops: HashMap<String, OperatorDef> = HashMap::new();
    std_ops.insert(
        "Inv".to_string(),
        make_op_def(
            "Inv",
            Expr::ModuleRef(
                ModuleTarget::Named("TLCExt".to_string()),
                "Trace".to_string(),
                vec![],
            ),
        ),
    );

    let mut fx_ops: rustc_hash::FxHashMap<String, OperatorDef> = rustc_hash::FxHashMap::default();
    fx_ops.insert(
        "Inv".to_string(),
        make_op_def(
            "Inv",
            Expr::ModuleRef(
                ModuleTarget::Named("TLCExt".to_string()),
                "Trace".to_string(),
                vec![],
            ),
        ),
    );

    let config = make_config(vec!["Inv"], vec![], vec![]);
    let std_result = compute_uses_trace(&config, &std_ops).unwrap();
    let fx_result = compute_uses_trace(&config, &fx_ops).unwrap();
    assert_eq!(std_result, fx_result);
    assert!(std_result);
}
