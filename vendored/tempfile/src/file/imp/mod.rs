// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg_attr(any(unix, target_os = "redox", target_os = "wasi"), path = "unix.rs")]
#[cfg_attr(windows, path = "windows.rs")]
#[cfg_attr(
    not(any(unix, target_os = "redox", target_os = "wasi", windows)),
    path = "other.rs"
)]

pub use self::platform::*;
