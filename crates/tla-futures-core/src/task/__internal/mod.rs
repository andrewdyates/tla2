// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg_attr(
    target_os = "none",
    cfg(any(target_has_atomic = "ptr", feature = "portable-atomic"))
)]
mod atomic_waker;
#[cfg_attr(
    target_os = "none",
    cfg(any(target_has_atomic = "ptr", feature = "portable-atomic"))
)]
pub use self::atomic_waker::AtomicWaker;
