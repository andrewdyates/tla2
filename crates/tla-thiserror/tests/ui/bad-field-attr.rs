// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
#[error(transparent)]
pub struct Error(#[error(transparent)] std::io::Error);

fn main() {}
