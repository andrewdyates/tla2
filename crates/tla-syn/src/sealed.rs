// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "parsing")]
pub(crate) mod lookahead {
    pub trait Sealed: Copy {}
}
