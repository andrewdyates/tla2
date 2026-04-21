#![allow(unused_macros)]
// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0


macro_rules! log {
    ($($tt:tt)*) => {
        #[cfg(feature = "logging")]
        {
            $($tt)*
        }
    }
}

macro_rules! debug {
    ($($tt:tt)*) => { log!(log::debug!($($tt)*)) }
}

macro_rules! trace {
    ($($tt:tt)*) => { log!(log::trace!($($tt)*)) }
}
