// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

pub(super) struct TraceStatus {}

impl TraceStatus {
    pub(super) fn new(_: usize) -> Self {
        Self {}
    }

    pub(super) fn trace_requested(&self) -> bool {
        false
    }
}
