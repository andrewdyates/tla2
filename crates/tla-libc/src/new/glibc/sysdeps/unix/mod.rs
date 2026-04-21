// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Source directory: `sysdeps/unix/`
//!
//! <https://github.com/bminor/glibc/tree/master/sysdeps/unix>

#[cfg(target_os = "linux")]
pub(crate) mod linux;
