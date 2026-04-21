// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use super::{Core, Handle};

impl Handle {
    pub(super) fn trace_core(&self, core: Box<Core>) -> Box<Core> {
        core
    }
}
