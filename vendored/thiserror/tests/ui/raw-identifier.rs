// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
#[error("error: {r#fn}")]
pub struct Error {
    r#fn: &'static str,
}

fn main() {
    let r#fn = "...";
    let _ = format!("error: {r#fn}");
}
