// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! UpperBounds examination.
//!
//! For each property in `UpperBounds.xml`, computes the maximum sum of
//! tokens across the specified places over all reachable markings.
//!
//! MCC output: `FORMULA <id> <bound> TECHNIQUES EXPLICIT`
//! where `<bound>` is the maximum token sum observed, or
//! `CANNOT_COMPUTE` if exploration was incomplete.
//!
//! Multiple properties are tracked simultaneously during a single BFS pass.

mod model;
mod observer;
mod pipeline;

#[cfg(test)]
pub(crate) use pipeline::check_upper_bounds_properties;
pub(crate) use pipeline::check_upper_bounds_properties_with_aliases;

#[cfg(test)]
mod tests;
