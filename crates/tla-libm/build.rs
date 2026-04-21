// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// TLA2 fork of libm 0.2.11 build.rs.
// Upstream build.rs enables cfg(assert_no_panic) when OPT_LEVEL != 0,
// which activates `#[cfg_attr(all(test, assert_no_panic), no_panic::no_panic)]`
// attributes in math modules. The `no-panic` crate was an upstream dev-dep
// used to assert panic-freedom in release builds; the TLA2 fork drops it
// to maintain the zero-runtime-dep posture, so we must NOT enable the cfg.

use std::env;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(assert_no_panic)");
    println!("cargo:rustc-check-cfg=cfg(feature, values(\"unstable\"))");
    println!("cargo:rustc-check-cfg=cfg(feature, values(\"checked\"))");
    // Silence unused warning from the upstream pattern while preserving
    // the env read so the build script remains a drop-in replacement
    // if upstream gains new cfg gates.
    let _ = env::var("OPT_LEVEL");
    // Intentionally NOT emitting `cargo:rustc-cfg=assert_no_panic`;
    // the `no-panic` dev-dep is dropped in this fork. The math modules
    // retain their `#[cfg_attr(all(test, assert_no_panic), ...)]` lines
    // upstream-verbatim — the cfg is simply never set, so those attrs
    // compile out cleanly.
}
