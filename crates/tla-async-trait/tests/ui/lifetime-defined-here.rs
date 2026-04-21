// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use async_trait::async_trait;

#[async_trait]
trait Foo {
    async fn bar(&self, x: &str, y: &'_ str) -> &'static str;
}

struct S(String);

#[async_trait]
impl Foo for S {
    async fn bar(&self, x: &str, y: &'_ str) -> &'static str {
        if false {
            &self.0
        } else if false {
            x
        } else {
            y
        }
    }
}

fn main() {}
