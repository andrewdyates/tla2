// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// SPDX-License-Identifier: Apache-2.0 OR MIT

use pin_project_lite::pin_project;

pin_project! {
    struct Struct1 {} //~ ERROR no rules expected the token `}`
}

pin_project! {
    struct Struct2(); //~ ERROR no rules expected the token `(`
}

pin_project! {
    struct Struct3; //~ ERROR no rules expected the token `;`
}

pin_project! {
    enum Enum { //~ ERROR no rules expected the token `enum`
        A(u8)
    }
}

pin_project! {
    union Union { //~ ERROR no rules expected the token `union`
        x: u8,
    }
}

fn main() {}
