// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::prelude::*;

pub(crate) const _ALIGNBYTES: usize = size_of::<c_double>() - 1;

pub const _MAX_PAGE_SHIFT: u32 = 12;
