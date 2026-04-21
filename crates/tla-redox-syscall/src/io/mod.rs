// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the MIT License (see LICENSE).
//
// Verbatim fork of upstream redox_syscall 0.5.18
// (https://gitlab.redox-os.org/redox-os/syscall). Original code:
// Copyright (c) 2017 Redox OS Developers, MIT License.

//! I/O functions

pub use self::{io::*, mmio::*};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use self::pio::*;

mod io;
mod mmio;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod pio;
