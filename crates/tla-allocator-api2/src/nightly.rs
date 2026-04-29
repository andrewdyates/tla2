// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(not(feature = "alloc"))]
pub use core::alloc;

#[cfg(feature = "alloc")]
pub use alloc_crate::{alloc, boxed, collections, vec};
