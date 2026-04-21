// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GNU libc.
//!
//! * Headers: <https://sourceware.org/git/?p=glibc.git> (official)
//! * Headers: <https://github.com/bminor/glibc> (mirror)
//!
//! This module structure is modeled after glibc's source tree. Its build system selects headers
//! from different locations based on the platform, which we mimic here with reexports.

/// Source directory: `posix/`
///
/// <https://github.com/bminor/glibc/tree/master/posix>
mod posix {
}

/// Source directory: `sysdeps/`
///
/// <https://github.com/bminor/glibc/tree/master/sysdeps>
mod sysdeps {
    // FIXME(pthread): eventually all platforms should use this module
}

pub(crate) use posix::*;
// FIXME(pthread): eventually all platforms should use this module
#[cfg(target_os = "linux")]
pub(crate) use sysdeps::nptl::*;
#[cfg(target_os = "linux")]
pub(crate) use sysdeps::unix::linux::*;
