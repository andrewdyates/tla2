// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

extern crate autocfg;

use std::env;

mod support;

/// Tests that autocfg uses the RUSTFLAGS or CARGO_ENCODED_RUSTFLAGS
/// environment variables when running rustc.
#[test]
fn test_with_sysroot() {
    let out = support::out_dir();
    let probe_rlib = support::build_probe_rlib(out.as_ref());
    let probe_extern = format!("--extern=autocfg_probe={}", probe_rlib.display());

    // If we have encoded rustflags, they take precedence, even if empty.
    env::set_var("CARGO_ENCODED_RUSTFLAGS", "");
    env::set_var("RUSTFLAGS", &probe_extern);
    let ac = autocfg::AutoCfg::with_dir(out.as_ref()).unwrap();
    assert!(ac.probe_sysroot_crate("std"));
    assert!(!ac.probe_sysroot_crate("autocfg_probe"));

    // Now try again with useful encoded args.
    env::set_var("CARGO_ENCODED_RUSTFLAGS", &probe_extern);
    let ac = autocfg::AutoCfg::with_dir(out.as_ref()).unwrap();
    assert!(ac.probe_sysroot_crate("autocfg_probe"));

    // Try the old-style RUSTFLAGS, ensuring HOST != TARGET.
    env::remove_var("CARGO_ENCODED_RUSTFLAGS");
    env::set_var("HOST", "lol");
    env::set_var("RUSTFLAGS", &probe_extern);
    let ac = autocfg::AutoCfg::with_dir(out.as_ref()).unwrap();
    assert!(ac.probe_sysroot_crate("autocfg_probe"));
}
