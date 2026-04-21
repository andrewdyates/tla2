// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source directory: `arch/`
//!
//! <https://github.com/kraj/musl/tree/master/arch>

pub(crate) mod generic;

#[cfg(target_arch = "mips")]
pub(crate) mod mips;
#[cfg(target_arch = "mips64")]
pub(crate) mod mips64;
