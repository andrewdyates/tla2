// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::env;

fn main() {
    let target = env::var("TARGET").unwrap();
    let mut cfg = cc::Build::new();
    if target.contains("windows") {
        cfg.define("WINDOWS", None);
        cfg.file("src/arch/windows.c");
        cfg.include("src/arch").compile("libstacker.a");
    } else {
        return;
    }
}
