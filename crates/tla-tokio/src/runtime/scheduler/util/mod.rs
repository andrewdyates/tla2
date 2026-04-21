// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(all(tokio_unstable, feature = "time", feature = "rt-multi-thread"))]
pub(in crate::runtime) mod time_alt;
