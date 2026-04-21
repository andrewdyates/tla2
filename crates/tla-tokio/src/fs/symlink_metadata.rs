// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::fs::asyncify;

use std::fs::Metadata;
use std::io;
use std::path::Path;

/// Queries the file system metadata for a path.
///
/// This is an async version of [`std::fs::symlink_metadata`][std]
///
/// [std]: fn@std::fs::symlink_metadata
pub async fn symlink_metadata(path: impl AsRef<Path>) -> io::Result<Metadata> {
    let path = path.as_ref().to_owned();
    asyncify(|| std::fs::symlink_metadata(path)).await
}
