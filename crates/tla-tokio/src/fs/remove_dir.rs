// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::fs::asyncify;

use std::io;
use std::path::Path;

/// Removes an existing, empty directory.
///
/// This is an async version of [`std::fs::remove_dir`].
pub async fn remove_dir(path: impl AsRef<Path>) -> io::Result<()> {
    let path = path.as_ref().to_owned();
    asyncify(move || std::fs::remove_dir(path)).await
}
