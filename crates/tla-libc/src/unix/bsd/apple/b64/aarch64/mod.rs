// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::prelude::*;

pub type boolean_t = c_int;

s! {
    pub struct malloc_zone_t {
        __private: [crate::uintptr_t; 18], // FIXME(macos): needs arm64 auth pointers support
    }
}

s_no_extra_traits! {
    pub struct max_align_t {
        priv_: f64,
    }
}
