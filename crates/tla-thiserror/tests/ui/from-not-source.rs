// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
pub struct Error {
    #[source]
    source: std::io::Error,
    #[from]
    other: anyhow::Error,
}

fn main() {}
