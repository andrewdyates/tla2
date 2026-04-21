// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! linux_raw syscalls for PIDs
//!
//! # Safety
//!
//! See the `rustix::backend` module documentation for details.
#![allow(unsafe_code, clippy::undocumented_unsafe_blocks)]

use crate::backend::conv::ret_usize_infallible;
use crate::pid::{Pid, RawPid};

#[inline]
#[must_use]
pub(crate) fn getpid() -> Pid {
    unsafe {
        let pid = ret_usize_infallible(syscall_readonly!(__NR_getpid)) as RawPid;
        Pid::from_raw_unchecked(pid)
    }
}
