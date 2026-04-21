// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
pub enum ErrorEnum {
    Confusing {
        #[source]
        a: std::io::Error,
        #[source]
        b: anyhow::Error,
    },
}

fn main() {}
