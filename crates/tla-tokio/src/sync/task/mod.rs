// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Thread-safe task notification primitives.

mod atomic_waker;
pub(crate) use self::atomic_waker::AtomicWaker;
