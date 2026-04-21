// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::fs::asyncify;

use std::fs::Permissions;
use std::io;
use std::path::Path;

/// Changes the permissions found on a file or a directory.
///
/// This is an async version of [`std::fs::set_permissions`][std]
///
/// [std]: fn@std::fs::set_permissions
pub async fn set_permissions(path: impl AsRef<Path>, perm: Permissions) -> io::Result<()> {
    let path = path.as_ref().to_owned();
    asyncify(|| std::fs::set_permissions(path, perm)).await
}
