// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::fs::asyncify;

use std::io;
use std::path::Path;

/// Returns `Ok(true)` if the path points at an existing entity.
///
/// This function will traverse symbolic links to query information about the
/// destination file. In case of broken symbolic links this will return `Ok(false)`.
///
/// This is the async equivalent of [`std::path::Path::try_exists`][std].
///
/// [std]: fn@std::path::Path::try_exists
///
/// # Examples
///
/// ```no_run
/// use tokio::fs;
///
/// # async fn dox() -> std::io::Result<()> {
/// fs::try_exists("foo.txt").await?;
/// # Ok(())
/// # }
/// ```
pub async fn try_exists(path: impl AsRef<Path>) -> io::Result<bool> {
    let path = path.as_ref().to_owned();
    asyncify(move || path.try_exists()).await
}
