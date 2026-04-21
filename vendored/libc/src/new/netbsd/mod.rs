// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NetBSD libc.
//!
//! * Headers: <https://github.com/NetBSD/src/tree/trunk/include>
//! * Sys headers: <https://github.com/NetBSD/src/tree/trunk/sys/sys>
//! * Manual pages: <https://man.netbsd.org/>

pub(crate) mod net {
}

pub(crate) mod sys;
pub(crate) mod unistd;
pub(crate) mod utmp_;
pub(crate) mod utmpx_;
