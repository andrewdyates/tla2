// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::fs::asyncify;

use std::io;
use std::path::{Path, PathBuf};

/// Reads a symbolic link, returning the file that the link points to.
///
/// This is an async version of [`std::fs::read_link`].
pub async fn read_link(path: impl AsRef<Path>) -> io::Result<PathBuf> {
    let path = path.as_ref().to_owned();
    asyncify(move || std::fs::read_link(path)).await
}
