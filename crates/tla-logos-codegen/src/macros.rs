// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "debug")]
macro_rules! debug {
    ($($arg:tt)*) => {
        eprint!("[{}:{}:{}] ", file!(), line!(), column!());
        eprintln!($($arg)*)
    }
}

#[cfg(not(feature = "debug"))]
macro_rules! debug {
    ($($arg:tt)*) => {};
}
