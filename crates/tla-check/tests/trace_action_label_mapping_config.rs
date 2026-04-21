// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use tla_check::{
    ActionLabelInstanceError, ActionLabelMappingConfig, EvalCtx, JsonValue, OperatorRef,
    TraceActionLabelMappingError,
};
use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn parses_actions_section_and_binds_params_in_formal_order() {
    let cfg = r#"
[spec]
module = "MySpec"

[[actions]]
label = "ClientStep"
operator = "ClientStep"
params = ["client", "req_id"]
param_encoding = "tla-json"
allow_stutter = true

[[actions]]
label = "DefaultStutter"
operator = "DefaultStutter"
"#;

    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();

    assert_eq!(cfg.spec_module.as_deref(), Some("MySpec"));

    let mapping = cfg.mapping("ClientStep").unwrap();
    assert_eq!(
        mapping.operator,
        OperatorRef::Unqualified {
            name: "ClientStep".to_string()
        }
    );
    assert!(mapping.allow_stutter);

    let mapping = cfg.mapping("DefaultStutter").unwrap();
    assert_eq!(
        mapping.operator,
        OperatorRef::Unqualified {
            name: "DefaultStutter".to_string()
        }
    );
    assert!(!mapping.allow_stutter);

    let mut params: HashMap<String, JsonValue> = HashMap::new();
    params.insert("req_id".to_string(), JsonValue::Int(42));
    params.insert("client".to_string(), JsonValue::Int(1));

    let bound = cfg.bind_params("ClientStep", &params).unwrap();
    assert_eq!(bound.len(), 2);
    assert_eq!(bound[0].0, "client");
    match &bound[0].1 {
        JsonValue::Int(v) => assert_eq!(*v, 1),
        other => panic!("expected client=int(1), got: {other:?}"),
    }
    assert_eq!(bound[1].0, "req_id");
    match &bound[1].1 {
        JsonValue::Int(v) => assert_eq!(*v, 42),
        other => panic!("expected req_id=int(42), got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bind_params_rejects_unknown_label() {
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), "").unwrap();
    let params: HashMap<String, JsonValue> = HashMap::new();
    assert!(matches!(
        cfg.bind_params("NoSuchLabel", &params),
        Err(ActionLabelInstanceError::UnknownLabel { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bind_params_requires_exact_param_set() {
    let cfg = r#"
[[actions]]
label = "A"
operator = "A"
params = ["x", "y"]
"#;
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();

    // Missing "y"
    let mut params: HashMap<String, JsonValue> = HashMap::new();
    params.insert("x".to_string(), JsonValue::Int(1));
    assert!(matches!(
        cfg.bind_params("A", &params),
        Err(ActionLabelInstanceError::ParamMismatch { .. })
    ));

    // Extra "z"
    params.insert("y".to_string(), JsonValue::Int(2));
    params.insert("z".to_string(), JsonValue::Int(3));
    assert!(matches!(
        cfg.bind_params("A", &params),
        Err(ActionLabelInstanceError::ParamMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn validate_for_spec_rejects_module_mismatch() {
    let cfg = r#"
[spec]
module = "Foo"
"#;
    let ctx = EvalCtx::new();
    assert!(matches!(
        ActionLabelMappingConfig::from_toml_str_for_spec("<test>".to_string(), cfg, "Bar", &ctx),
        Err(TraceActionLabelMappingError::ModuleMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn from_toml_str_rejects_non_reference_operator_expr() {
    let cfg = r#"
[[actions]]
label = "A"
operator = "1 + 2"
"#;
    assert!(matches!(
        ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg),
        Err(TraceActionLabelMappingError::InvalidOperatorRef { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn validate_for_spec_rejects_unknown_operator() {
    let src = r#"---- MODULE MySpec ----
Foo == TRUE
===="#;
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    let module = lowered.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let cfg = r#"
[spec]
module = "MySpec"

[[actions]]
label = "L"
operator = "NoSuchOp"
"#;
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();
    assert!(matches!(
        cfg.validate_for_spec("MySpec", &ctx),
        Err(TraceActionLabelMappingError::UnknownOperator { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn validate_for_spec_rejects_operator_arity_mismatch() {
    let src = r#"---- MODULE MySpec ----
Op(x, y) == TRUE
===="#;
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    let module = lowered.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let cfg = r#"
[spec]
module = "MySpec"

[[actions]]
label = "L"
operator = "Op"
params = ["x"]
"#;
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();
    assert!(matches!(
        cfg.validate_for_spec("MySpec", &ctx),
        Err(TraceActionLabelMappingError::OperatorArityMismatch {
            expected: 2,
            got: 1,
            ..
        })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn validate_for_spec_accepts_instance_qualified_operator_ref() {
    let main_src = r#"---- MODULE MySpec ----
Inst == INSTANCE Inner
===="#;
    let inner_src = r#"---- MODULE Inner ----
Step(x) == x = 1
===="#;

    let main_tree = parse_to_syntax_tree(main_src);
    let main_lowered = lower(FileId(0), &main_tree);
    let main_module = main_lowered.module.unwrap();

    let inner_tree = parse_to_syntax_tree(inner_src);
    let inner_lowered = lower(FileId(1), &inner_tree);
    let inner_module = inner_lowered.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&main_module);
    ctx.load_instance_module(inner_module.name.node.clone(), &inner_module);

    let cfg = r#"
[spec]
module = "MySpec"

[[actions]]
label = "L"
operator = "Inst!Step"
params = ["x"]
"#;
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();
    cfg.validate_for_spec("MySpec", &ctx).unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn validate_for_spec_rejects_module_qualified_operator_ref_without_instance() {
    let main_src = r#"---- MODULE MySpec ----
===="#;
    let inner_src = r#"---- MODULE Inner ----
Step(x) == x = 1
===="#;

    let main_tree = parse_to_syntax_tree(main_src);
    let main_lowered = lower(FileId(0), &main_tree);
    let main_module = main_lowered.module.unwrap();

    let inner_tree = parse_to_syntax_tree(inner_src);
    let inner_lowered = lower(FileId(1), &inner_tree);
    let inner_module = inner_lowered.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&main_module);
    ctx.load_instance_module(inner_module.name.node.clone(), &inner_module);

    let cfg = r#"
[spec]
module = "MySpec"

[[actions]]
label = "L"
operator = "Inner!Step"
params = ["x"]
"#;
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();
    assert!(matches!(
        cfg.validate_for_spec("MySpec", &ctx),
        Err(TraceActionLabelMappingError::UnknownOperator { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn validate_for_spec_rejects_operator_param_name_mismatch() {
    let src = r#"---- MODULE MySpec ----
Op(x) == TRUE
===="#;
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    let module = lowered.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let cfg = r#"
[spec]
module = "MySpec"

[[actions]]
label = "L"
operator = "Op"
params = ["y"]
"#;
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();
    assert!(matches!(
        cfg.validate_for_spec("MySpec", &ctx),
        Err(TraceActionLabelMappingError::OperatorParamNameMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn validate_for_spec_rejects_higher_order_operator() {
    let src = r#"---- MODULE MySpec ----
Op(F(_), x) == TRUE
===="#;
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    let module = lowered.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let cfg = r#"
[spec]
module = "MySpec"

[[actions]]
label = "L"
operator = "Op"
params = ["F", "x"]
"#;
    let cfg = ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg).unwrap();
    assert!(matches!(
        cfg.validate_for_spec("MySpec", &ctx),
        Err(TraceActionLabelMappingError::UnsupportedHigherOrderOperator { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn from_toml_str_rejects_duplicate_labels() {
    let cfg = r#"
[[actions]]
label = "A"
operator = "A"

[[actions]]
label = "A"
operator = "B"
"#;
    assert!(matches!(
        ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg),
        Err(TraceActionLabelMappingError::DuplicateLabel { label }) if label == "A"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn from_toml_str_rejects_duplicate_param_names() {
    let cfg = r#"
[[actions]]
label = "A"
operator = "A"
params = ["x", "x"]
"#;
    assert!(matches!(
        ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg),
        Err(TraceActionLabelMappingError::DuplicateParamName { label, param })
            if label == "A" && param == "x"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn from_toml_str_rejects_reference_with_args() {
    let cfg = r#"
[[actions]]
label = "A"
operator = "Foo(1)"
"#;
    assert!(matches!(
        ActionLabelMappingConfig::from_toml_str("<test>".to_string(), cfg),
        Err(TraceActionLabelMappingError::InvalidOperatorRef { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn from_toml_str_reports_invalid_toml() {
    assert!(matches!(
        ActionLabelMappingConfig::from_toml_str("<test>".to_string(), "this is not toml"),
        Err(TraceActionLabelMappingError::ParseToml { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn from_path_reports_io_errors() {
    let missing_path =
        Path::new("definitely-not-a-real-file-2d76db49-4e47-4f8e-a23b-49dc20f504c8.toml");
    assert!(matches!(
        ActionLabelMappingConfig::from_path(missing_path),
        Err(TraceActionLabelMappingError::ReadConfig { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn from_path_round_trips_valid_toml() {
    let toml = r#"
[spec]
module = "MySpec"

[[actions]]
label = "A"
operator = "A"
params = ["x"]
"#;

    let mut f = tempfile::NamedTempFile::new().unwrap();
    f.write_all(toml.as_bytes()).unwrap();

    let cfg = ActionLabelMappingConfig::from_path(f.path()).unwrap();
    assert_eq!(cfg.spec_module.as_deref(), Some("MySpec"));
    assert_eq!(
        cfg.mapping("A").unwrap().operator,
        OperatorRef::Unqualified {
            name: "A".to_string()
        }
    );
}
