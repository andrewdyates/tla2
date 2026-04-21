// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
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
