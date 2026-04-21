// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Directory: `mach/`
//!
//! <https://github.com/apple-oss-distributions/xnu/tree/main/osfmk/mach>

/// Directory: `mach/arm`
#[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
pub(crate) mod arm {
}

/// Directory: `mach/i386`
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub(crate) mod i386 {
}

/// Directory: `mach/machine`
pub(crate) mod machine {
}
