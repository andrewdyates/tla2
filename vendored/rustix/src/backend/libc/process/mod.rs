// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(not(windows))]
pub(crate) mod syscalls;
pub(crate) mod types;
#[cfg(not(any(target_os = "espidf", target_os = "vita", target_os = "wasi")))]
pub(crate) mod wait;
