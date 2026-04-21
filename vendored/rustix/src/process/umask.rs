// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Umask support.

#[cfg(feature = "fs")]
use crate::backend;
#[cfg(feature = "fs")]
use crate::fs::Mode;

/// `umask(mask)`—Set the process file creation mask.
///
/// # References
///  - [POSIX]
///  - [Linux]
///
/// [POSIX]: https://pubs.opengroup.org/onlinepubs/9799919799/functions/umask.html
/// [Linux]: https://man7.org/linux/man-pages/man2/umask.2.html
#[cfg(feature = "fs")]
#[cfg_attr(docsrs, doc(cfg(feature = "fs")))]
#[inline]
pub fn umask(mask: Mode) -> Mode {
    backend::process::syscalls::umask(mask)
}
