// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/// Marker for types that are `Sync` but not `Send`
#[allow(dead_code)]
pub(crate) struct SyncNotSend(#[allow(dead_code)] *mut ());

unsafe impl Sync for SyncNotSend {}

cfg_rt! {
    pub(crate) struct NotSendOrSync(#[allow(dead_code)] *mut ());
}
