// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-compatible error message formatting helpers.
//!
//! These functions are used by the `#[error(...)]` attributes on `EvalError`
//! variants. They are private implementation detail — the public surface is
//! the `EvalError` enum in the parent module.

/// TLC-compatible single-argument error message formatting (EC.TLC_MODULE_ONE_ARGUMENT_ERROR = 2283).
/// Matches TLC's "The argument of <op> should be a <type>, but instead it is:\n<value>".
pub(super) fn _format_one_argument_error(
    op: &str,
    expected_type: &str,
    value_display: &str,
) -> String {
    let article = if expected_type.starts_with(|c: char| "aeiouAEIOU".contains(c)) {
        "an"
    } else {
        "a"
    };
    format!(
        "The argument of {op} should be {article} {expected_type}, but instead it is:\n{value_display}"
    )
}

/// TLC-compatible argument error message formatting (EC.TLC_MODULE_ARGUMENT_ERROR).
/// Matches TLC's "The <pos> argument of <op> should be a/an <type>, but instead it is:\n<value>".
pub(super) fn _format_argument_error(
    position: &str,
    op: &str,
    expected_type: &str,
    value_display: &str,
) -> String {
    let article = if expected_type.starts_with(|c: char| "aeiouAEIOU".contains(c)) {
        "an"
    } else {
        "a"
    };
    format!(
        "The {position} argument of {op} should be {article} {expected_type}, but instead it is:\n{value_display}"
    )
}

/// TLC-compatible "no such field" message formatting (RecordValue.java:488).
/// With record_display: "Attempted to access nonexistent field '<field>' of record\n<record>"
/// Without: "Record has no field: <field>"
pub(super) fn _format_no_such_field(field: &str, record_display: &Option<String>) -> String {
    match record_display {
        Some(r) => format!("Attempted to access nonexistent field '{field}' of record\n{r}"),
        None => format!("Record has no field: {field}"),
    }
}

/// TLC-compatible "index out of bounds" message formatting (TupleValue.java:144).
/// With value_display: "Attempted to access index <N> of tuple\n<tuple>\nwhich is out of bounds."
/// Without: "Sequence index out of bounds: <index> not in 1..<len>"
pub(super) fn _format_index_out_of_bounds(
    index: &i64,
    len: &usize,
    value_display: &Option<String>,
) -> String {
    match value_display {
        Some(v) => {
            format!("Attempted to access index {index} of tuple\n{v}\nwhich is out of bounds.")
        }
        None => format!("Sequence index out of bounds: {index} not in 1..{len}"),
    }
}

/// TLC-compatible "not in domain" message formatting.
/// With func_display: "Attempted to apply function:\n<func>\nto argument <arg>, which is not in the domain of the function."
/// Without: "Attempted to apply function to argument <arg>, which is not in the domain of the function."
pub(super) fn _format_not_in_domain(arg: &str, func_display: &Option<String>) -> String {
    match func_display {
        Some(f) => format!(
            "Attempted to apply function:\n{f}\nto argument {arg}, which is not in the domain of the function."
        ),
        None => format!(
            "Attempted to apply function to argument {arg}, which is not in the domain of the function."
        ),
    }
}
