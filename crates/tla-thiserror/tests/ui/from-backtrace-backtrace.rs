// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// https://github.com/dtolnay/thiserror/issues/163

use std::backtrace::Backtrace;
use thiserror::Error;

#[derive(Error, Debug)]
#[error("...")]
pub struct Error(
    #[from]
    #[backtrace]
    std::io::Error,
    Backtrace,
);

fn main() {}
