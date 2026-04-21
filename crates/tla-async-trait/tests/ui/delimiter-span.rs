#![allow(unused_macro_rules)]
// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0


use async_trait::async_trait;

macro_rules! picky {
    ($(t:tt)*) => {};
}

#[async_trait]
trait Trait {
    async fn method();
}

struct Struct;

#[async_trait]
impl Trait for Struct {
    async fn method() {
        picky!({ 123, self });
        picky!({ 123 });
    }
}

fn main() {}
