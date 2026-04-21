// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::common_macro::schema_imports::*;
use core::net::IpAddr;

#[test]
fn ip_addr_schema() {
    let actual_name = IpAddr::declaration();
    assert_eq!("IpAddr", actual_name);
    let mut defs = Default::default();
    IpAddr::add_definitions_recursively(&mut defs);
    insta::assert_snapshot!(format!("{:#?}", defs));
}
