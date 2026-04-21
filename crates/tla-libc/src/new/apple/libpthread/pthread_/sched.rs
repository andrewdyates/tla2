// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

pub use crate::new::pthread_::pthread_impl::*;
use crate::prelude::*;

s! {
    pub struct sched_param {
        pub sched_priority: c_int,
        __opaque: [c_char; 4],
    }
}
