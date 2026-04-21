// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Directory: `sys/`
//!
//! <https://github.com/apple-oss-distributions/xnu/tree/main/bsd/sys>

pub(crate) mod signal;

/// Directory: `sys/_types`
///
/// https://github.com/apple-oss-distributions/xnu/tree/main/bsd/sys/_types
pub(crate) mod _types {
    pub(crate) mod _ucontext;
}

// Bit of a hack since the directories get merged and we can't have >1 sys module.
pub(crate) use crate::new::apple::libpthread::sys::*;
