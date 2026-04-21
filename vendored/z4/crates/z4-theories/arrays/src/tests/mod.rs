// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::assert_conflict_soundness;
use z4_core::Sort;

mod core_solver;
mod store_chain;
mod verification;

fn make_array_sort() -> Sort {
    Sort::array(Sort::Int, Sort::Int)
}
