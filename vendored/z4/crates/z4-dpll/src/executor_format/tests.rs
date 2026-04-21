// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use z4_core::term::Symbol;

#[test]
fn format_sort_handles_core_sorts_and_quoting() {
    assert_eq!(format_sort(&Sort::Bool), "Bool");
    assert_eq!(format_sort(&Sort::RegLan), "RegLan");
    assert_eq!(format_sort(&Sort::bitvec(8)), "(_ BitVec 8)");
    assert_eq!(
        format_sort(&Sort::array(Sort::Int, Sort::Bool)),
        "(Array Int Bool)"
    );
    assert_eq!(
        format_sort(&Sort::Uninterpreted("let".to_string())),
        "|let|"
    );
}

#[test]
fn format_symbol_quotes_reserved_words_and_formats_indices() {
    assert_eq!(format_symbol(&Symbol::named("x")), "x");
    assert_eq!(format_symbol(&Symbol::named("let")), "|let|");
    assert_eq!(
        format_symbol(&Symbol::indexed("extract", vec![7, 4])),
        "(_ extract 7 4)"
    );
}

#[test]
fn format_rational_prints_integer_and_fractional_values() {
    assert_eq!(
        format_rational(&BigRational::from_integer(BigInt::from(5))),
        "5.0"
    );
    assert_eq!(
        format_rational(&BigRational::from_integer(BigInt::from(-5))),
        "(- 5.0)"
    );
    assert_eq!(
        format_rational(&BigRational::new(BigInt::from(3), BigInt::from(2))),
        "(/ 3 2)"
    );
    assert_eq!(
        format_rational(&BigRational::new(BigInt::from(-3), BigInt::from(2))),
        "(- (/ 3 2))"
    );
}

#[test]
fn format_bigint_uses_unary_minus_form() {
    assert_eq!(format_bigint(&BigInt::from(0)), "0");
    assert_eq!(format_bigint(&BigInt::from(7)), "7");
    assert_eq!(format_bigint(&BigInt::from(-7)), "(- 7)");
}

#[test]
fn format_bitvec_masks_and_pads() {
    // Width 4: divisible by 4, uses hex
    assert_eq!(format_bitvec(&BigInt::from(3), 4), "#x3");
    // Width 8: divisible by 4, uses hex
    assert_eq!(format_bitvec(&BigInt::from(0xA_u32), 8), "#x0a");
    assert_eq!(format_bitvec(&BigInt::from(-1), 8), "#xff");
    // Width 1: not divisible by 4, uses binary (#1793)
    assert_eq!(format_bitvec(&BigInt::from(0), 1), "#b0");
    assert_eq!(format_bitvec(&BigInt::from(1), 1), "#b1");
    // Width 49: not divisible by 4, uses binary (#1793)
    assert_eq!(
        format_bitvec(&BigInt::from(1), 49),
        "#b0000000000000000000000000000000000000000000000001"
    );
    // Width 64: boundary case, divisible by 4, uses hex (#1793)
    assert_eq!(format_bitvec(&BigInt::from(1), 64), "#x0000000000000001");
    // Width 65: > 64, not divisible by 4, uses indexed format (#1793)
    assert_eq!(format_bitvec(&BigInt::from(1), 65), "(_ bv1 65)");
    // Width 68: > 64, divisible by 4, still uses hex (#1793)
    assert_eq!(format_bitvec(&BigInt::from(1), 68), "#x00000000000000001");
}

#[test]
fn format_model_atom_quotes_uninterpreted_values() {
    // Non-uninterpreted sorts return value as-is
    assert_eq!(format_model_atom(&Sort::Int, "42"), "42");
    assert_eq!(format_model_atom(&Sort::Bool, "true"), "true");
    assert_eq!(format_model_atom(&Sort::Real, "3.14"), "3.14");
    assert_eq!(format_model_atom(&Sort::bitvec(8), "#xff"), "#xff");

    // Uninterpreted sorts quote via quote_symbol - @ and ! are valid symbol chars
    // so @U!0 doesn't need quoting
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "@U!0"),
        "@U!0"
    );
    assert_eq!(
        format_model_atom(
            &Sort::Datatype(z4_core::DatatypeSort::new("Pair", vec![])),
            "@Pair!1"
        ),
        "@Pair!1"
    );

    // Simple identifiers don't need quoting
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "elem0"),
        "elem0"
    );

    // Values with spaces or reserved words need quoting
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "foo bar"),
        "|foo bar|"
    );
    // Reserved word 'true' needs quoting (even as uninterpreted value)
    assert_eq!(
        format_model_atom(&Sort::Uninterpreted("U".to_string()), "true"),
        "|true|"
    );
}

#[test]
fn format_default_value_produces_smt_lib_defaults() {
    assert_eq!(format_default_value(&Sort::Bool), "false");
    assert_eq!(format_default_value(&Sort::Int), "0");
    assert_eq!(format_default_value(&Sort::Real), "0.0");
    assert_eq!(format_default_value(&Sort::String), "\"\"");
    assert_eq!(format_default_value(&Sort::RegLan), "re.none");
    // width%4==0 uses hex (#1793)
    assert_eq!(format_default_value(&Sort::bitvec(8)), "#x00");
    assert_eq!(format_default_value(&Sort::bitvec(4)), "#x0");
    assert_eq!(format_default_value(&Sort::bitvec(16)), "#x0000");
    // width%4!=0 uses binary (#1793)
    assert_eq!(format_default_value(&Sort::bitvec(1)), "#b0");
    assert_eq!(format_default_value(&Sort::bitvec(7)), "#b0000000");
    assert_eq!(
        format_default_value(&Sort::FloatingPoint(8, 24)),
        "(_ +zero 8 24)"
    );
    // @U!0 uses valid symbol chars, no quoting needed
    assert_eq!(
        format_default_value(&Sort::Uninterpreted("U".to_string())),
        "@U!0"
    );
    assert_eq!(
        format_default_value(&Sort::Datatype(z4_core::DatatypeSort::new("List", vec![]))),
        "@List!0"
    );
    // Nested array sort
    assert_eq!(
        format_default_value(&Sort::array(Sort::Int, Sort::Bool)),
        "((as const (Array Int Bool)) false)"
    );
}

#[test]
fn format_value_handles_bool_and_defaults() {
    let terms = TermStore::new();

    // Bool values
    assert_eq!(format_value(&Sort::Bool, Some(true), &terms), "true");
    assert_eq!(format_value(&Sort::Bool, Some(false), &terms), "false");
    assert_eq!(format_value(&Sort::Bool, None, &terms), "false"); // Default

    // Other sorts return default values (value param ignored for non-Bool)
    assert_eq!(format_value(&Sort::Int, None, &terms), "0");
    assert_eq!(format_value(&Sort::Real, None, &terms), "0.0");
    assert_eq!(format_value(&Sort::String, None, &terms), "\"\"");
    assert_eq!(format_value(&Sort::RegLan, None, &terms), "re.none");
    assert_eq!(format_value(&Sort::bitvec(8), None, &terms), "#x00");
    // @T!0 uses valid symbol chars, no quoting needed
    assert_eq!(
        format_value(&Sort::Uninterpreted("T".to_string()), None, &terms),
        "@T!0"
    );
    assert_eq!(
        format_value(&Sort::array(Sort::Int, Sort::Bool), None, &terms),
        "((as const (Array Int Bool)) false)"
    );
}
