// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use super::Inject;

impl<T: 'static> Inject<T> {
    pub(crate) fn len(&self) -> usize {
        self.shared.len()
    }
}
