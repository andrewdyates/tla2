// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod algebra;
mod membership;

pub(crate) use algebra::value_subseteq;
pub(crate) use algebra::{eval_big_union, eval_intersect, eval_set_minus, eval_subseteq};
pub use membership::set_contains_with_ctx;
pub(crate) use membership::{eval_in, eval_not_in};
