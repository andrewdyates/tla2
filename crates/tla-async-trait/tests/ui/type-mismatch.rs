// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use async_trait::async_trait;

#[async_trait]
trait Interface {
    async fn f(&self);
    async fn g(&self) -> ();
}

struct Thing;

#[async_trait]
impl Interface for Thing {
    async fn f(&self) {
        0
    }
    async fn g(&self) {
        0
    }
}

fn main() {}
