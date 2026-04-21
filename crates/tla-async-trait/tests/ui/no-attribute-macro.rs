// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

pub trait Trait {
    async fn method(&self);
}

pub struct Struct;

impl Trait for Struct {
    async fn method(&self) {}
}

fn main() {
    let _: &dyn Trait;
}
