// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use quote::quote;
use std::net::Ipv4Addr;

fn main() {
    let ip = Ipv4Addr::LOCALHOST;
    let _ = quote! { #ip };
}
