// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Non-property examination verdict and output helpers.

#[path = "examination_non_property/mod.rs"]
mod split;

pub(crate) use self::split::{
    deadlock_verdict, liveness_verdict, one_safe_verdict, quasi_liveness_verdict,
    stable_marking_verdict, state_space_stats,
};
