#![allow(unreachable_code)]
// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0


#[tracing::instrument]
async fn unit() {
    ""
}

#[tracing::instrument]
async fn simple_mismatch() -> String {
    ""
}

#[tracing::instrument]
async fn opaque_unsatisfied() -> impl std::fmt::Display {
    ("",)
}

struct Wrapper<T>(T);

#[tracing::instrument]
async fn mismatch_with_opaque() -> Wrapper<impl std::fmt::Display> {
    ""
}

#[tracing::instrument]
async fn early_return_unit() {
    if true {
        return "";
    }
}

#[tracing::instrument]
async fn early_return() -> String {
    if true {
        return "";
    }
    String::new()
}

#[tracing::instrument]
async fn extra_semicolon() -> i32 {
    1;
}

fn main() {}
