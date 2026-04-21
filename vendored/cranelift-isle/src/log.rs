// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Debug logging from the ISLE compiler itself.

/// Log a compiler-internal message for debugging purposes.
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log {
    ($($msg:tt)*) => {
        ::log::trace!($($msg)*)
    };
}

/// Log a compiler-internal message for debugging purposes.
#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log {
    ($($msg:tt)*) => {};
}
