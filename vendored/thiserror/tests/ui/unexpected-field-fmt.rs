// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    What {
        #[error("...")]
        io: std::io::Error,
    },
}

fn main() {}
