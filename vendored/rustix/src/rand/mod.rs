// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random-related operations.

#[cfg(linux_kernel)]
mod getrandom;

#[cfg(linux_kernel)]
pub use getrandom::{getrandom, GetRandomFlags};
