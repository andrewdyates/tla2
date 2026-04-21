// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use super::AtomicU64;
use crate::loom::sync::Mutex;

pub(crate) type StaticAtomicU64 = AtomicU64;

impl AtomicU64 {
    pub(crate) const fn new(val: u64) -> Self {
        Self {
            inner: Mutex::const_new(val),
        }
    }
}
