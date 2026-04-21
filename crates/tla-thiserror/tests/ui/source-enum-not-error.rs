// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Debug)]
pub struct NotError;

#[derive(Error, Debug)]
#[error("...")]
pub enum ErrorEnum {
    Broken { source: NotError },
}

fn main() {}
