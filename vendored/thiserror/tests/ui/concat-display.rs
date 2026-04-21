// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

macro_rules! error_type {
    ($name:ident, $what:expr) => {
        // Use #[error("invalid {}", $what)] instead.

        #[derive(Error, Debug)]
        #[error(concat!("invalid ", $what))]
        pub struct $name;
    };
}

error_type!(Error, "foo");

fn main() {}
