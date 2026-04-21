// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "parsing")]
pub(crate) mod lookahead {
    pub trait Sealed: Copy {}
}
