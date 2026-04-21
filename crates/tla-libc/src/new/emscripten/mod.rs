// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Emscripten libc.
//!
//! * Headers: <https://github.com/emscripten-core/emscripten/tree/main/system/lib/libc>

pub(crate) mod pthread;
pub(crate) mod sched;
pub(crate) mod unistd;
