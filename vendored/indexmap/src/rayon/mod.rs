#![cfg_attr(docsrs, doc(cfg(feature = "rayon")))]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0


use rayon::prelude::*;

use alloc::collections::LinkedList;
use alloc::vec::Vec;

pub mod map;
pub mod set;

// This form of intermediate collection is also how Rayon collects `HashMap`.
// Note that the order will also be preserved!
fn collect<I: IntoParallelIterator>(iter: I) -> LinkedList<Vec<I::Item>> {
    iter.into_par_iter().collect_vec_list()
}
