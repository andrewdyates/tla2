// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
#[error("invalid rdo_lookahead_frames {0} (expected < {})", i32::MAX)]
pub struct Error(u32);

fn main() {}
