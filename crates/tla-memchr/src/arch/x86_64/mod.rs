// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/*!
Vector algorithms for the `x86_64` target.
*/

pub mod avx2;
pub mod sse2;

pub(crate) mod memchr;
