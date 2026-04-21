#![allow(clippy::module_inception)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0


#[allow(clippy::redundant_static_lifetimes)]
#[rustfmt::skip]
mod tables;

pub(crate) use self::tables::*;
