// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

extern crate autocfg;

fn main() {
    // Normally, cargo will set `OUT_DIR` for build scripts.
    let ac = autocfg::AutoCfg::with_dir("target").unwrap();
    for i in 0..100 {
        ac.emit_rustc_version(1, i);
    }
}
