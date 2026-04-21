// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "rayon")]
pub(crate) mod rayon;
#[cfg(feature = "serde")]
mod serde;
