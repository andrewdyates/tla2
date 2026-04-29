// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Collection- and quantifier-heavy parity canaries.

use super::*;

const STRUCTURED_MODULE: &str = "\
---- MODULE Structured ----
TupleLit == <<1, 2 + 1>>
RecordLit == [a |-> 1, b |-> <<2, 3>>]
RecordAccess == [a |-> 1, b |-> <<2, 3>>].b
SetEnumLit == {1, 2, 3}
SetUnion == {1, 2} \\cup {2, 3}
SetIntersect == {1, 2, 3} \\cap {2, 3, 4}
SetMinus == {1, 2, 3} \\ {2}
RangeLit == 2..4
TimesLit == {1, 2} \\X {3}
====";

#[test]
fn test_tir_parity_structured_values() {
    let module = parse_module(STRUCTURED_MODULE);
    for name in [
        "TupleLit",
        "RecordLit",
        "RecordAccess",
        "SetEnumLit",
        "SetUnion",
        "SetIntersect",
        "SetMinus",
        "RangeLit",
        "TimesLit",
    ] {
        assert_parity(&module, name);
    }
}

const QUANTIFIER_MODULE: &str = "\
---- MODULE TirQuantifiers ----
ForallTrue == \\A x \\in {TRUE, FALSE}: x = TRUE \\/ x = FALSE
ForallFalse == \\A x \\in {1, 2, 3}: x > 1
ExistsTrue == \\E x \\in {1, 2, 3}: x > 2
ExistsFalse == \\E x \\in {1, 2, 3}: x > 5
ChooseOp == CHOOSE x \\in {1, 2, 3}: x > 1
ForallMulti == \\A x \\in {1, 2}, y \\in {3, 4}: x + y > 0
ExistsMulti == \\E x \\in {1, 2}, y \\in {3, 4}: x + y = 5
====";

#[test]
fn test_tir_parity_quantifiers() {
    let module = parse_module(QUANTIFIER_MODULE);
    for name in &[
        "ForallTrue",
        "ForallFalse",
        "ExistsTrue",
        "ExistsFalse",
        "ChooseOp",
        "ForallMulti",
        "ExistsMulti",
    ] {
        assert_parity(&module, name);
    }
}

const MEMBERSHIP_MODULE: &str = "\
---- MODULE TirMembership ----
InTrue == 2 \\in {1, 2, 3}
InFalse == 5 \\in {1, 2, 3}
SubseteqTrue == {1, 2} \\subseteq {1, 2, 3}
SubseteqFalse == {1, 4} \\subseteq {1, 2, 3}
====";

#[test]
fn test_tir_parity_membership() {
    let module = parse_module(MEMBERSHIP_MODULE);
    for name in &["InTrue", "InFalse", "SubseteqTrue", "SubseteqFalse"] {
        assert_parity(&module, name);
    }
}

const SET_COMPREHENSION_MODULE: &str = "\
---- MODULE TirSetComprehension ----
FilterOp == {x \\in {1, 2, 3, 4, 5}: x > 3}
BuilderOp == {x + 1 : x \\in {1, 2, 3}}
BuilderMulti == {x + y : x \\in {1, 2}, y \\in {10, 20}}
====";

#[test]
fn test_tir_parity_set_comprehension() {
    let module = parse_module(SET_COMPREHENSION_MODULE);
    for name in &["FilterOp", "BuilderOp", "BuilderMulti"] {
        assert_parity(&module, name);
    }
}

const POWERSET_MODULE: &str = "\
---- MODULE TirPowerset ----
PowerOp == SUBSET {1, 2}
BigUnionOp == UNION {{1, 2}, {2, 3}}
RecordSetOp == [a: {1, 2}, b: {TRUE, FALSE}]
====";

#[test]
fn test_tir_parity_powerset_union_recordset() {
    let module = parse_module(POWERSET_MODULE);
    for name in &["PowerOp", "BigUnionOp", "RecordSetOp"] {
        assert_parity(&module, name);
    }
}
