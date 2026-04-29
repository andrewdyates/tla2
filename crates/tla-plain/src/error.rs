// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Error {
    TooShort,
    BadAlignment,
}
