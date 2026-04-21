// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::ast::{BoundPattern, Expr, Unit};
use crate::lower::lower;
use crate::span::FileId;
use crate::syntax::parse_to_syntax_tree;
use num_bigint::BigInt;

mod except_and_spans;
mod expr_and_collections;
mod module_and_operator_defs;
mod module_ref_target_prime;
mod parser_edge_cases;
mod prime_metadata;
mod quantifiers_and_choose;
mod recursive_and_local_defs;
