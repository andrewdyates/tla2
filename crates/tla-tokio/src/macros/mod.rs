#![cfg_attr(not(feature = "full"), allow(unused_macros))]
// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[macro_use]
mod cfg;

#[macro_use]
mod loom;

#[macro_use]
mod pin;

#[macro_use]
mod thread_local;

#[macro_use]
mod addr_of;

cfg_trace! {
    #[macro_use]
    mod trace;
}

cfg_macros! {
    #[macro_use]
    mod select;

    #[macro_use]
    mod join;

    #[macro_use]
    mod try_join;
}

// Includes re-exports needed to implement macros
#[doc(hidden)]
pub mod support;
