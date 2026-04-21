// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/// A lock (mutex) yielding generic data.
pub(crate) trait Lock<T> {
    type Handle: AsMut<T>;

    fn lock(self) -> Self::Handle;
}
