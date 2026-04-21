// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// Adapted from https://github.com/Alexhuszagh/rust-lexical.

//! Precalculated large powers for limbs.

#[cfg(fast_arithmetic = "32")]
pub(crate) use super::large_powers32::*;

#[cfg(fast_arithmetic = "64")]
pub(crate) use super::large_powers64::*;
