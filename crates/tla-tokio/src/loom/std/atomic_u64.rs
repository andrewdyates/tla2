// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Implementation of an atomic `u64` cell. On 64 bit platforms, this is a
//! re-export of `AtomicU64`. On 32 bit platforms, this is implemented using a
//! `Mutex`.

// `AtomicU64` can only be used on targets with `target_has_atomic` is 64 or greater.
// Once `cfg_target_has_atomic` feature is stable, we can replace it with
// `#[cfg(target_has_atomic = "64")]`.
// Refs: https://github.com/rust-lang/rust/tree/master/src/librustc_target
cfg_has_atomic_u64! {
    #[path = "atomic_u64_native.rs"]
    mod imp;
}

cfg_not_has_atomic_u64! {
    #[path = "atomic_u64_as_mutex.rs"]
    mod imp;
}

pub(crate) use imp::AtomicU64;
