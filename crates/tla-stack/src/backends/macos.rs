// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

pub unsafe fn guess_os_stack_limit() -> Option<usize> {
    Some(
        libc::pthread_get_stackaddr_np(libc::pthread_self()) as usize
            - libc::pthread_get_stacksize_np(libc::pthread_self()) as usize,
    )
}
