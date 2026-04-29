// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod fixpoint;
mod prefire;
mod structural;

#[cfg(test)]
pub(crate) use fixpoint::reduce_iterative;
#[cfg(test)]
pub(crate) use fixpoint::reduce_iterative_structural;
#[cfg(test)]
pub(crate) use fixpoint::reduce_iterative_structural_deadlock_safe_with_protected;
#[cfg(test)]
pub(crate) use fixpoint::reduce_iterative_structural_with_protected;
#[cfg(test)]
pub(crate) use fixpoint::reduce_iterative_temporal_projection_candidate;
pub(crate) use fixpoint::{
    reduce_iterative_structural_one_safe, reduce_iterative_structural_query_with_protected,
    reduce_iterative_structural_with_mode, reduce_query_guarded,
};
#[cfg(test)]
pub(crate) use prefire::apply_query_guarded_prefire;
#[cfg(test)]
pub(crate) use structural::reduce;
