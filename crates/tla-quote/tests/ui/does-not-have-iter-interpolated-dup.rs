// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use quote::quote;

fn main() {
    let nonrep = "";

    // Without some protection against repetitions with no iterator somewhere
    // inside, this would loop infinitely.
    quote!(#(#nonrep #nonrep)*);
}
