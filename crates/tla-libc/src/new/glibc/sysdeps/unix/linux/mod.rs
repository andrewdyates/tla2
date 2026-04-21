// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Source directory: `sysdeps/unix/sysv/linux` (the `sysv` is flattened).
//!
//! <https://github.com/bminor/glibc/tree/master/sysdeps/unix/sysv/linux>

/// Directory: `net/`
///
/// Source directory: `sysdeps/unix/sysv/linux/net`
pub(crate) mod net {
    pub(crate) mod route;
}
