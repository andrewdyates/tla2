// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(any(unix, target_os = "wasi"))]
pub mod fd;
#[cfg(windows)]
pub mod windows;
