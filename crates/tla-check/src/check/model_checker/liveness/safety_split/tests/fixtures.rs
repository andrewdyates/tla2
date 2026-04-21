// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn dummy(e: Expr) -> Spanned<Expr> {
    Spanned::dummy(e)
}

pub(super) fn boxed(e: Expr) -> Box<Spanned<Expr>> {
    Box::new(dummy(e))
}

pub(super) fn inner_named_instance_module() -> tla_core::ast::Module {
    parse_module(
        r#"
---- MODULE InnerNamedInstance ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Spec == Init /\ [][Next]_vars
Bad == []((Next) \/ UNCHANGED vars)
Raw == []Next
===="#,
        FileId(1),
    )
}

pub(super) fn outer_named_instance_module() -> tla_core::ast::Module {
    parse_module(
        r#"
---- MODULE OuterNamedInstance ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
I == INSTANCE InnerNamedInstance
Refines == I!Spec
Expanded == I!Bad
RawRefines == I!Raw
===="#,
        FileId(0),
    )
}

pub(super) fn outer_named_instance_init_split_module() -> tla_core::ast::Module {
    parse_module(
        r#"
---- MODULE OuterNamedInstanceInitSplit ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
InitLeft == x = 0
InitRight == x \in 0..2
I == INSTANCE InnerNamedInstance WITH Init <- (InitLeft /\ InitRight)
Refines == I!Spec
===="#,
        FileId(2),
    )
}

pub(super) fn operator_body<'a>(
    module: &'a tla_core::ast::Module,
    name: &str,
) -> &'a Spanned<Expr> {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == name => Some(&def.body),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator {name} not found"))
}

pub(super) fn named_instance_config(prop: &str) -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec![prop.to_string()],
        check_deadlock: false,
        ..Default::default()
    }
}
