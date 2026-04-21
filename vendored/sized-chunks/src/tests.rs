// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicUsize, Ordering};

pub(crate) struct DropTest<'a> {
    counter: &'a AtomicUsize,
}

impl<'a> DropTest<'a> {
    pub(crate) fn new(counter: &'a AtomicUsize) -> Self {
        counter.fetch_add(1, Ordering::Relaxed);
        DropTest { counter }
    }
}

impl<'a> Drop for DropTest<'a> {
    fn drop(&mut self) {
        self.counter.fetch_sub(1, Ordering::Relaxed);
    }
}
