// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::future::Future;

pub(crate) trait InstrumentedFuture: Future {
    fn id(&self) -> Option<tracing::Id>;
}

impl<F: Future> InstrumentedFuture for tracing::instrument::Instrumented<F> {
    fn id(&self) -> Option<tracing::Id> {
        self.span().id()
    }
}
