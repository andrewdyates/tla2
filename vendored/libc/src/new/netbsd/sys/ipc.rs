// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Header: `sys/ipc.h`
//!
//! <https://github.com/NetBSD/src/blob/trunk/sys/sys/ipc.h>

use crate::prelude::*;

s! {
    pub struct ipc_perm {
        pub uid: crate::uid_t,
        pub gid: crate::gid_t,
        pub cuid: crate::uid_t,
        pub cgid: crate::gid_t,
        pub mode: crate::mode_t,
        pub _seq: c_ushort,
        pub _key: crate::key_t,
    }
}
