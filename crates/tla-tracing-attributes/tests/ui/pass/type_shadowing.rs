// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! This program is a regression test for [#3306], where shadowing
//! caused compilation failure in certain cases due to the original
//! function body not getting its own scope.
//!
//! [#3306]: https://github.com/tokio-rs/tracing/issues/3306
type Foo = ();
enum Bar {
    Foo,
}

#[tracing::instrument]
fn this_is_fine() -> Foo {
    // glob import imports Bar::Foo, shadowing Foo
    use Bar::*;
}

fn main() {}
