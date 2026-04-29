// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

mod color_tag;
mod types;
mod util;

pub use color_tag::color_tag;
pub use types::{Error, ErrorDetail};
use types::{Input, Parser, Result};
