// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use quote::quote_spanned;

fn main() {
    let span = "";
    let x = 0i32;
    quote_spanned!(span=> #x);
}
