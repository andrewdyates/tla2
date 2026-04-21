#![deprecated(note = "Only for internal testing. Do not use")]
// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)] // We need to allow ourselves the stuff we deprecate here.
//! Some strategies for internal testing.
//!
//! # Warning
//!
//! They come with no guarantees of correctness, stability, performance or anything at all. *DO NOT
//! USE*.

use super::hybrid::{Config, HybridStrategy};

/// Config for no fast slots.
#[derive(Clone, Copy, Default)]
pub struct NoFastSlots;

impl Config for NoFastSlots {
    const USE_FAST: bool = false;
}

/// A strategy that fills the slots with some crap to make sure we test the fallbacks too.
#[deprecated(note = "Only for internal testing. Do not use")]
pub type FillFastSlots = HybridStrategy<NoFastSlots>;
