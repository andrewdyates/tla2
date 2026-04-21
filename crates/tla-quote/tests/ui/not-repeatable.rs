// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use quote::quote;

struct Ipv4Addr;

fn main() {
    let ip = Ipv4Addr;
    let _ = quote! { #(#ip)* };
}
