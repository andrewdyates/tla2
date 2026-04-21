// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Directory: `sys/`
//!
//! https://github.com/NetBSD/src/tree/trunk/sys/sys

pub(crate) mod file;
pub(crate) mod ipc;
pub(crate) mod socket;
pub(crate) mod statvfs;
pub(crate) mod time;
pub(crate) mod timex;
pub(crate) mod types;
