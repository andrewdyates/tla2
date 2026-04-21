// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[macro_use]
extern crate lazy_static;

mod outer {
    pub mod inner {
        lazy_static! {
            pub(in outer) static ref FOO: () = ();
        }
    }
}

fn main() {
    assert_eq!(*outer::inner::FOO, ());
}
