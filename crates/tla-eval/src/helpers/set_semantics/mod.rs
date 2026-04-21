// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set equality semantics and SetPred-aware iteration.
//!
//! Split from monolithic `set_semantics.rs` as part of #3463.

mod equality;
pub(crate) mod funcset_partition;
mod iteration;

pub use self::equality::values_equal;
pub use self::iteration::{
    eval_iter_set, eval_iter_set_tlc_normalized, eval_iter_set_tlc_normalized_inline,
    materialize_setpred_to_vec,
};
// Part of #3978: Streaming SetPred iteration for quantifier short-circuit.
pub(crate) use self::iteration::{count_setpred_streaming, try_stream_setpred, SetPredStreamIter};
