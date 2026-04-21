// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! FreeBSD libc.
//!
//! * Headers: <https://github.com/freebsd/freebsd-src/blob/main/sys/riscv/include/ucontext.h>
//! * Symbol map: <https://github.com/freebsd/freebsd-src/blob/main/lib/libc/gen/Symbol.map>

pub(crate) mod sys;
pub(crate) mod unistd;
