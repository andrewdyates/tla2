// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-lowering AST analysis: prime detection and guard-prime dependency computation.

mod contains_prime;
mod fixed_point;
mod guards_depend_on_prime;
mod primed_params;

pub use contains_prime::compute_contains_prime;
pub use guards_depend_on_prime::compute_guards_depend_on_prime;
pub use primed_params::{compute_has_primed_param, operator_has_primed_param};
