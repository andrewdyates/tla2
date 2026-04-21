// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error)]
pub union U {
    msg: &'static str,
    num: usize,
}

fn main() {}
