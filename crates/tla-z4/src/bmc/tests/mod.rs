// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

mod choose;
mod compound_e2e;
mod div_mod_basics;
mod div_mod_linearization;
mod errors;
mod execution;
mod expr_forms;
mod func_encoding;
mod incremental;
mod nested_powerset;
mod operators;
mod powerset_encoding;
mod quantifiers;
mod record_tuple_e2e;
mod seq_encoding;
mod set_encoding;
mod var_accumulation;
