// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
#[error(fmt = core::fmt::Octal::fmt)]
pub struct Error(i32);

fn main() {}
