// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Header: `sys/time.h`
//!
//! <https://github.com/NetBSD/src/blob/trunk/sys/sys/time.h>

s! {
    pub struct itimerspec {
        pub it_interval: crate::timespec,
        pub it_value: crate::timespec,
    }
}

pub const CLOCK_VIRTUAL: crate::clockid_t = 1;
pub const CLOCK_PROF: crate::clockid_t = 2;
pub const CLOCK_THREAD_CPUTIME_ID: crate::clockid_t = 0x20000000;
pub const CLOCK_PROCESS_CPUTIME_ID: crate::clockid_t = 0x40000000;
