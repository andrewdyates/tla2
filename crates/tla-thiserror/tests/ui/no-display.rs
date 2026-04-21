// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Debug)]
struct NoDisplay;

#[derive(Error, Debug)]
#[error("thread: {thread}")]
pub struct Error {
    thread: NoDisplay,
}

#[derive(Error, Debug)]
#[error("thread: {thread:o}")]
pub struct ErrorOctal {
    thread: NoDisplay,
}

fn main() {}
