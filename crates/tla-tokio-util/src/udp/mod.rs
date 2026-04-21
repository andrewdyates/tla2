#![cfg(not(loom))]
// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0


//! UDP framing

mod frame;
pub use frame::UdpFramed;
