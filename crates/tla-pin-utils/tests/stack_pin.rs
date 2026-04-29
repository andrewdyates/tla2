#![forbid(unsafe_code)] // pin_mut! is completely safe.
                        // Copyright 2026 Dropbox, Inc.
                        // Author: Andrew Yates <ayates@dropbox.com>
                        // Licensed under the Apache License, Version 2.0

use core::pin::Pin;
use pin_utils::pin_mut;

#[test]
fn stack_pin() {
    struct Foo {}
    let foo = Foo {};
    pin_mut!(foo);
    let _: Pin<&mut Foo> = foo;

    let bar = Foo {};
    let baz = Foo {};
    pin_mut!(bar, baz,);
    let _: Pin<&mut Foo> = bar;
    let _: Pin<&mut Foo> = baz;
}
