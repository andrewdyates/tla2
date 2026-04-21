// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Apple interfaces.
//!
//! The Xcode SDK includes interfaces that are split across a couple of different libraries. Most
//! of these are available at <https://github.com/apple-oss-distributions>.

/// Entrypoint for Apple headers, usually found as part of the Xcode SDK.
///
/// <https://github.com/apple-oss-distributions/Libc/tree/main/include>
mod libc {
}

mod libpthread;
mod xnu;

pub(crate) use libc::*;
pub(crate) use libpthread::pthread_;
pub(crate) use pthread_::pthread;
pub(crate) use xnu::*;
