// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(crate) mod addr;
pub(crate) mod ext;
#[cfg(not(any(
    windows,
    target_os = "espidf",
    target_os = "horizon",
    target_os = "vita"
)))]
pub(crate) mod msghdr;
#[cfg(linux_kernel)]
pub(crate) mod netdevice;
pub(crate) mod read_sockaddr;
pub(crate) mod send_recv;
pub(crate) mod sockopt;
pub(crate) mod syscalls;
pub(crate) mod write_sockaddr;
