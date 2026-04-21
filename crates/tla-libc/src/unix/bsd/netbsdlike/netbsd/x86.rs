// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::prelude::*;

pub type __cpu_simple_lock_nv_t = c_uchar;

pub(crate) const _ALIGNBYTES: usize = size_of::<c_int>() - 1;
