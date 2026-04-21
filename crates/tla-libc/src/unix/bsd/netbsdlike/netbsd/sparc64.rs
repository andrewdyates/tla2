// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::prelude::*;

pub type __cpu_simple_lock_nv_t = c_uchar;

// should be pub(crate), but that requires Rust 1.18.0
#[doc(hidden)]
pub const _ALIGNBYTES: usize = 0xf;
