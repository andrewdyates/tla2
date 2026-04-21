// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::backend::c;

/// `sysinfo`
#[cfg(linux_kernel)]
pub type Sysinfo = c::sysinfo;

#[cfg(not(target_os = "wasi"))]
pub(crate) type RawUname = c::utsname;
