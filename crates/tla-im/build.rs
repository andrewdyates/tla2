// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// tla-im: Fork of im 15.1 into the tla2 workspace (Part of #4250).
// Threadsafe detection matches upstream im (the threadsafe variant),
// keyed off CARGO_PKG_NAME == "tla-im".

use std::env;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if let Some(channel) = version_check::Channel::read() {
        if channel.supports_features() {
            println!("cargo:rustc-cfg=has_specialisation");
        }
    }
    // Declare custom cfg keys so the `unexpected_cfgs` lint is quiet.
    println!("cargo:rustc-check-cfg=cfg(has_specialisation)");
    println!("cargo:rustc-check-cfg=cfg(threadsafe)");

    let pkgname = env::var("CARGO_PKG_NAME").expect("Cargo didn't set the CARGO_PKG_NAME env var!");
    let test_rc = env::var("IM_TEST_RC").is_ok();
    match pkgname.as_str() {
        // Original name preserved; tla-im is the fork entry point.
        "im" | "tla-im" => {
            if !test_rc {
                println!("cargo:rustc-cfg=threadsafe");
            }
        }
        "im-rc" => {}
        _ => panic!("unexpected package name!"),
    }
}
