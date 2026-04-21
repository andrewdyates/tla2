// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// Don't test on custom wasm32-unknown-unknown
#![cfg(not(all(
    target_arch = "wasm32",
    target_os = "unknown",
    feature = "custom",
    not(feature = "js")
)))]

// Use the normal getrandom implementation on this architecture.
use getrandom::getrandom as getrandom_impl;
mod common;
