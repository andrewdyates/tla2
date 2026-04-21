// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use async_trait::async_trait;

#[async_trait]
trait Trait {
    async fn f(&self);
}

struct Thing;

#[async_trait]
impl Trait for Thing {
    async fn f(&self);
}

fn main() {}
