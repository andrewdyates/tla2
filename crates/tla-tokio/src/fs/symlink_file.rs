// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::fs::asyncify;

use std::io;
use std::path::Path;

/// Creates a new file symbolic link on the filesystem.
///
/// The `link` path will be a file symbolic link pointing to the `original`
/// path.
///
/// This is an async version of [`std::os::windows::fs::symlink_file`][std]
///
/// [std]: https://doc.rust-lang.org/std/os/windows/fs/fn.symlink_file.html
pub async fn symlink_file(original: impl AsRef<Path>, link: impl AsRef<Path>) -> io::Result<()> {
    let original = original.as_ref().to_owned();
    let link = link.as_ref().to_owned();

    asyncify(move || std::os::windows::fs::symlink_file(original, link)).await
}
