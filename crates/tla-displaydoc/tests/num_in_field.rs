// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/// {foo1} {foo2}
#[derive(displaydoc::Display)]
pub struct Test {
    foo1: String,
    foo2: String,
}

fn assert_display<T: std::fmt::Display>(input: T, expected: &'static str) {
    let out = format!("{}", input);
    assert_eq!(expected, out);
}

#[test]
fn does_it_print() {
    assert_display(
        Test {
            foo1: "hi".into(),
            foo2: "hello".into(),
        },
        "hi hello",
    );
}
