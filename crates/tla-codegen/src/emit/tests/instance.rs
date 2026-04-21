// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{generate_rust_with_context, CodeGenContext, CodeGenOptions};
use std::path::Path;
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader, SyntaxNode};

fn lower_main_module(source: &str) -> (tla_core::ast::Module, SyntaxNode) {
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);
    assert!(
        result.errors.is_empty(),
        "lower errors: {:?}",
        result.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
    (result.module.expect("main module"), tree)
}

fn generate_with_loader_context(source: &str) -> String {
    try_generate_with_loader_context(source).expect("generate rust")
}

fn try_generate_with_loader_context(source: &str) -> Result<String, String> {
    let (module, tree) = lower_main_module(source);
    let spec_path = Path::new("/tmp/tla2-codegen-instance-inline.tla");

    let mut loader = ModuleLoader::new(spec_path);
    loader.seed_from_syntax_tree(&tree, spec_path);
    loader.load_extends(&module).expect("load extends");
    loader.load_instances(&module).expect("load instances");

    let context = CodeGenContext {
        modules: loader.modules_for_model_checking(&module),
    };
    generate_rust_with_context(&module, &context, &CodeGenOptions::default())
        .map_err(|e| e.to_string())
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn expands_named_instance_module_refs() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
Init == I!Init
Next == I!Next
InvNonNegative == I!InvNonNegative
====

---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
InvNonNegative == x >= 0
====
"#,
    );

    assert!(rust.contains("fn check_inv_non_negative"));
    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
    assert!(!rust.contains("I!"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn imports_init_next_and_invariant_from_standalone_instance() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner
====

---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
InvNonNegative == x >= 0
====
"#,
    );

    assert!(rust.contains("fn init(&self) -> Vec<Self::State>"));
    assert!(rust.contains("fn next(&self, state: &Self::State) -> Vec<Self::State>"));
    assert!(rust.contains("\"InvNonNegative\""), "{rust}");
    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn imports_init_next_and_invariant_from_standalone_instance_with_substitutions() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner WITH limit <- 5
InvLocal == x >= 0
====

---- MODULE Inner ----
CONSTANT limit
Init == x = limit
Next == x' = x + 1
InvBounded == x >= limit
====
"#,
    );

    assert!(
        rust.contains("fn init(&self) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(
        rust.contains("fn next(&self, state: &Self::State) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(rust.contains("\"InvBounded\""), "{rust}");
    assert!(rust.contains("x: 5_i64"), "{rust}");
    assert!(rust.contains("(state.x >= 5_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn standalone_instance_skips_temporal_invariants_when_importing_top_level_ops() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner
====

---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
TypeInvariant == x >= 0
LoopInvariant == [][x' = x]_x
====
"#,
    );

    assert!(
        rust.contains("fn init(&self) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(
        rust.contains("fn next(&self, state: &Self::State) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(rust.contains("\"TypeInvariant\""), "{rust}");
    assert!(!rust.contains("\"LoopInvariant\""), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn standalone_instance_skips_invariants_that_expand_to_temporal_helpers() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner
====

---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
TypeInvariant == LoopInvariantAlias
LoopInvariantAlias == [][x' = x]_x
====
"#,
    );

    assert!(
        rust.contains("fn init(&self) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(
        rust.contains("fn next(&self, state: &Self::State) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(!rust.contains("\"TypeInvariant\""), "{rust}");
    assert!(!rust.contains("\"LoopInvariantAlias\""), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn resolves_helper_lookup_through_instanced_module_extends_scope() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
InvOk == I!InvOk
====

---- MODULE Inner ----
EXTENDS Helpers
InvOk == Helper(x)
====

---- MODULE Helpers ----
Helper(v) == v >= 0
====
"#,
    );

    assert!(rust.contains("fn check_inv_ok"));
    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn expands_parameterized_instance_targets() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I(n) == INSTANCE Inner WITH limit <- n
InvBounded == I(5)!InvBounded
====

---- MODULE Inner ----
InvBounded == x <= limit
====
"#,
    );

    assert!(rust.contains("fn check_inv_bounded"));
    assert!(rust.contains("(state.x <= 5_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn expands_chained_instance_targets() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Mid
InvChained == I!J!InvBounded
====

---- MODULE Mid ----
J == INSTANCE Inner
====

---- MODULE Inner ----
InvBounded == x <= 10
====
"#,
    );

    assert!(rust.contains("fn check_inv_chained"));
    assert!(rust.contains("(state.x <= 10_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn instanced_helper_lookup_prefers_extends_over_standalone_instance_imports() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
InvPick == I!InvPick
====

---- MODULE Inner ----
EXTENDS HelperExt
INSTANCE HelperInst
InvPick == ChooseMe(x)
====

---- MODULE HelperExt ----
ChooseMe(v) == v >= 0
====

---- MODULE HelperInst ----
ChooseMe(v) == v <= -1
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
    assert!(!rust.contains("(state.x <= -1_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn standalone_imported_top_level_ops_prefer_extends_over_nested_instance_imports() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner
====

---- MODULE Inner ----
EXTENDS ExtSpec
INSTANCE InstSpec
====

---- MODULE ExtSpec ----
Init == x = 0
Next == x' = x + 1
InvPick == x >= 0
====

---- MODULE InstSpec ----
Init == x = 99
Next == x' = x - 1
InvPick == x <= -1
====
"#,
    );

    assert!(rust.contains("x: 0_i64"), "{rust}");
    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
    assert!(!rust.contains("99_i64"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn exported_ops_can_still_use_local_helpers_inside_their_module() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
InvPublic == I!InvPublic
====

---- MODULE Inner ----
LOCAL Hidden(v) == v >= 0
InvPublic == Hidden(x)
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn local_helpers_do_not_leak_through_named_instances() {
    let err = try_generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
InvPublic == I!InvPublic
InvLeak == I!Hidden
====

---- MODULE Inner ----
LOCAL Hidden == x >= 0
InvPublic == Hidden
====
"#,
    )
    .expect_err("non-exported local helper should fail codegen");

    assert!(
        err.contains("module reference (M!Op)"),
        "expected unresolved local export failure, got: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn local_instance_operators_do_not_leak_through_extends() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
InvPublic == I!InvPublic
====

---- MODULE Inner ----
EXTENDS Mid
InvPublic == Public(x)
====

---- MODULE Mid ----
LOCAL INSTANCE LocalHelpers
Public(v) == Hidden(v)
====

---- MODULE LocalHelpers ----
Hidden(v) == v >= 0
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn caller_let_helpers_do_not_leak_into_instanced_module_bodies() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
Init == x = 0
Next == x' = x
Inv == LET Helper(v) == v <= -1 IN I!Inv
====

---- MODULE Inner ----
Helper(v) == v >= 0
Inv == Helper(x)
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
    assert!(!rust.contains("(state.x <= -1_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn instance_substitutions_use_the_declaring_module_scope() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
Init == x = 0
Next == x' = x
Inv == I!Inv
====

---- MODULE Inner ----
Helper(v) == v >= 0
J == INSTANCE Other WITH q <- Helper(x)
Inv == J!Op
====

---- MODULE Other ----
Op == q
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn local_instance_operators_materialize_with_helpers_in_caller_scope() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

Init == x = 0
Next == x' = x
Inv ==
    LET Helper(v) == v >= 0
        J == INSTANCE Inner WITH limit <- Helper(x)
    IN J!Inv
====

---- MODULE Inner ----
Inv == limit
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn parameterized_instance_operator_params_shadow_zero_arg_helpers() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

Arg == x <= -1
I(Arg) == INSTANCE Inner WITH limit <- Arg
Init == x = 0
Next == x' = x
Inv == I(x >= 0)!Inv
====

---- MODULE Inner ----
Inv == limit
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
    assert!(!rust.contains("(state.x <= -1_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn local_parameterized_instance_params_shadow_zero_arg_helpers() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

Init == x = 0
Next == x' = x
Inv ==
    LET Arg == x <= -1
        J(Arg) == INSTANCE Inner WITH limit <- Arg
    IN J(x >= 0)!Inv
====

---- MODULE Inner ----
Inv == limit
====
"#,
    );

    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
    assert!(!rust.contains("(state.x <= -1_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn instance_with_variable_substitution_maps_state_vars() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE myCount

INSTANCE Counter WITH count <- myCount
====

---- MODULE Counter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
InvNonNeg == count >= 0
====
"#,
    );

    assert!(
        rust.contains("fn init(&self) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(
        rust.contains("fn next(&self, state: &Self::State) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(rust.contains("\"InvNonNeg\""), "{rust}");
    // The substitution count <- myCount means all references to 'count'
    // in the inner module should become 'my_count' in generated Rust
    assert!(rust.contains("my_count"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn named_instance_with_variable_substitution() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE myCount

I == INSTANCE Counter WITH count <- myCount
Init == I!Init
Next == I!Next
InvOk == I!InvNonNeg
====

---- MODULE Counter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
InvNonNeg == count >= 0
====
"#,
    );

    assert!(rust.contains("fn check_inv_ok"), "{rust}");
    assert!(rust.contains("my_count"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn instance_with_constant_and_variable_substitution() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner WITH limit <- 10
InvLocal == x >= 0
====

---- MODULE Inner ----
CONSTANT limit
Init == x = limit
Next == x' = x + 1
InvBounded == x >= limit /\ x >= 0
====
"#,
    );

    assert!(
        rust.contains("fn init(&self) -> Vec<Self::State>"),
        "{rust}"
    );
    assert!(rust.contains("x: 10_i64"), "{rust}");
    assert!(rust.contains("(state.x >= 10_i64)"), "{rust}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn instance_with_multiple_substitutions() {
    let rust = generate_with_loader_context(
        r#"
---- MODULE Main ----
VARIABLE x

I(lo, hi) == INSTANCE Bounds WITH low <- lo, high <- hi
InvOk == I(0, 10)!InRange
====

---- MODULE Bounds ----
InRange == x >= low /\ x <= high
====
"#,
    );

    assert!(rust.contains("fn check_inv_ok"), "{rust}");
    assert!(rust.contains("(state.x >= 0_i64)"), "{rust}");
    assert!(rust.contains("(state.x <= 10_i64)"), "{rust}");
}
