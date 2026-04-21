// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use quote::quote;
use std::net::Ipv4Addr;

fn main() {
    let ip = Ipv4Addr::LOCALHOST;
    let _ = quote! { #ip };
}
