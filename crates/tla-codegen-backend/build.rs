// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build script for tla-codegen-backend.
//!
//! When the `host-arch` feature is enabled (default), detects the target
//! architecture and emits the corresponding ISA feature cfg (`arm64` or `x86`).
//! This mirrors the upstream cranelift-codegen build.rs behavior but without
//! the cranelift-codegen-meta dependency — we map architectures directly.
//! See: #4206

fn main() {
    // Only emit host ISA cfg when the `host-arch` feature is active and no
    // explicit architecture feature (`all-arch`, `x86`, `arm64`) was selected.
    let host_arch = std::env::var("CARGO_FEATURE_HOST_ARCH").is_ok();
    let all_arch = std::env::var("CARGO_FEATURE_ALL_ARCH").is_ok();
    let explicit_x86 = std::env::var("CARGO_FEATURE_X86").is_ok();
    let explicit_arm64 = std::env::var("CARGO_FEATURE_ARM64").is_ok();

    if host_arch && !all_arch && !explicit_x86 && !explicit_arm64 {
        let target = std::env::var("TARGET").expect("TARGET env var not set by Cargo");
        let arch = target.split('-').next().expect("TARGET has no architecture component");
        let isa = match arch {
            "aarch64" => "arm64",
            "x86_64" => "x86",
            _ => {
                eprintln!(
                    "cargo:warning=tla-codegen-backend: unsupported host architecture '{}', \
                     no ISA feature enabled",
                    arch
                );
                return;
            }
        };
        println!("cargo:rustc-cfg=feature=\"{isa}\"");
    }
}
