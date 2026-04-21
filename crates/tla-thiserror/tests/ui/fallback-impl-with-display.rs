// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use core::fmt::{self, Display};
use thiserror::Error;

#[derive(Error, Debug)]
#[error]
pub struct MyError;

impl Display for MyError {
    fn fmt(&self, _formatter: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

fn main() {}
