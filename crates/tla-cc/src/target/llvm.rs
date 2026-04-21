// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;

use super::{generated, TargetInfo};

impl TargetInfo<'_> {
    /// The LLVM/Clang target triple.
    ///
    /// See <https://clang.llvm.org/docs/CrossCompilation.html#target-triple>.
    ///
    /// Rust and Clang don't really agree on target naming, so we first try to
    /// find the matching trible based on `rustc`'s output, but if no such
    /// triple exists, we attempt to construct the triple from scratch.
    ///
    /// NOTE: You should never need to match on this explicitly, use the
    /// fields on [`TargetInfo`] instead.
    pub(crate) fn llvm_target(
        &self,
        rustc_target: &str,
        version: Option<&str>,
    ) -> Cow<'static, str> {
        if rustc_target == "armv7-apple-ios" {
            // FIXME(madsmtm): Unnecessary once we bump MSRV to Rust 1.74
            return Cow::Borrowed("armv7-apple-ios");
        } else if self.os == "uefi" {
            // Override the UEFI LLVM targets.
            //
            // The rustc mappings (as of 1.82) for the UEFI targets are:
            // * i686-unknown-uefi -> i686-unknown-windows-gnu
            // * x86_64-unknown-uefi -> x86_64-unknown-windows
            // * aarch64-unknown-uefi -> aarch64-unknown-windows
            //
            // However, in cc-rs all the UEFI targets use
            // -windows-gnu. This has been the case since 2021 [1].
            // * i686-unknown-uefi -> i686-unknown-windows-gnu
            // * x86_64-unknown-uefi -> x86_64-unknown-windows-gnu
            // * aarch64-unknown-uefi -> aarch64-unknown-windows-gnu
            //
            // For now, override the UEFI mapping to keep the behavior
            // of cc-rs unchanged.
            //
            // TODO: as discussed in [2], it may be possible to switch
            // to new UEFI targets added to clang, and regardless it
            // would be good to have consistency between rustc and
            // cc-rs.
            //
            // [1]: https://github.com/rust-lang/cc-rs/pull/623
            // [2]: https://github.com/rust-lang/cc-rs/pull/1264
            return Cow::Owned(format!("{}-unknown-windows-gnu", self.full_arch));
        }

        // If no version is requested, let's take the triple directly from
        // `rustc` (the logic below is not yet good enough for most targets).
        //
        // FIXME(madsmtm): This should ideally be removed.
        if version.is_none() {
            if let Ok(index) = generated::LLVM_TARGETS
                .binary_search_by_key(&rustc_target, |(rustc_target, _)| rustc_target)
            {
                let (_, llvm_target) = &generated::LLVM_TARGETS[index];
                return Cow::Borrowed(llvm_target);
            }
        }

        // Otherwise, attempt to construct the triple from the target info.

        let arch = match self.full_arch {
            riscv32 if riscv32.starts_with("riscv32") => "riscv32",
            riscv64 if riscv64.starts_with("riscv64") => "riscv64",
            "aarch64" if self.vendor == "apple" => "arm64",
            "armv7" if self.vendor == "sony" => "thumbv7a", // FIXME
            arch => arch,
        };
        let vendor = match self.vendor {
            "kmc" | "nintendo" => "unknown",
            "unknown" if self.os == "android" => "linux",
            "uwp" => "pc",
            "espressif" => "",
            _ if self.arch == "msp430" => "",
            vendor => vendor,
        };
        let os = match self.os {
            "macos" => "macosx",
            "visionos" => "xros",
            "uefi" => "windows",
            "solid_asp3" | "horizon" | "teeos" | "nuttx" | "espidf" => "none",
            "nto" => "unknown",    // FIXME
            "trusty" => "unknown", // FIXME
            os => os,
        };
        let version = version.unwrap_or("");
        let env = match self.env {
            "newlib" | "nto70" | "nto71" | "nto71_iosock" | "p1" | "p2" | "relibc" | "sgx"
            | "uclibc" => "",
            "sim" => "simulator",
            env => env,
        };
        let abi = match self.abi {
            "llvm" | "softfloat" | "uwp" | "vec-extabi" => "",
            "ilp32" => "_ilp32",
            "abi64" => "",
            "elfv1" | "elfv2" => "",
            abi => abi,
        };
        Cow::Owned(match (vendor, env, abi) {
            ("", "", "") => format!("{arch}-{os}{version}"),
            ("", env, abi) => format!("{arch}-{os}{version}-{env}{abi}"),
            (vendor, "", "") => format!("{arch}-{vendor}-{os}{version}"),
            (vendor, env, abi) => format!("{arch}-{vendor}-{os}{version}-{env}{abi}"),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::TargetInfo;

    #[test]
    fn test_old_ios_target() {
        assert_eq!(
            TargetInfo {
                full_arch: "armv7",
                arch: "armv7",
                vendor: "apple",
                os: "ios",
                env: "",
                abi: "",
            }
            .llvm_target("armv7-apple-ios", None),
            "armv7-apple-ios"
        );
    }

    #[test]
    fn basic_llvm_triple_guessing() {
        assert_eq!(
            TargetInfo {
                full_arch: "aarch64",
                arch: "aarch64",
                vendor: "unknown",
                os: "linux",
                env: "",
                abi: "",
            }
            .llvm_target("invalid", None),
            "aarch64-unknown-linux"
        );
        assert_eq!(
            TargetInfo {
                full_arch: "x86_64",
                arch: "x86_64",
                vendor: "unknown",
                os: "linux",
                env: "gnu",
                abi: "",
            }
            .llvm_target("invalid", None),
            "x86_64-unknown-linux-gnu"
        );
        assert_eq!(
            TargetInfo {
                full_arch: "x86_64",
                arch: "x86_64",
                vendor: "unknown",
                os: "linux",
                env: "gnu",
                abi: "eabi",
            }
            .llvm_target("invalid", None),
            "x86_64-unknown-linux-gnueabi"
        );
        assert_eq!(
            TargetInfo {
                full_arch: "x86_64",
                arch: "x86_64",
                vendor: "apple",
                os: "macos",
                env: "",
                abi: "",
            }
            .llvm_target("invalid", None),
            "x86_64-apple-macosx"
        );
    }

    #[test]
    fn llvm_version() {
        assert_eq!(
            TargetInfo {
                full_arch: "aarch64",
                arch: "aarch64",
                vendor: "apple",
                os: "ios",
                env: "sim",
                abi: "",
            }
            .llvm_target("aarch64-apple-ios-sim", Some("14.0")),
            "arm64-apple-ios14.0-simulator"
        );
        assert_eq!(
            TargetInfo {
                full_arch: "aarch64",
                arch: "aarch64",
                vendor: "apple",
                os: "visionos",
                env: "",
                abi: "",
            }
            .llvm_target("aarch64-apple-visionos", Some("2.0")),
            "arm64-apple-xros2.0"
        );
        assert_eq!(
            TargetInfo {
                full_arch: "aarch64",
                arch: "aarch64",
                vendor: "apple",
                os: "ios",
                env: "",
                abi: "macabi",
            }
            .llvm_target("aarch64-apple-ios-macabi", Some("13.1")),
            "arm64-apple-ios13.1-macabi"
        );
    }

    #[test]
    fn uefi() {
        assert_eq!(
            TargetInfo {
                full_arch: "i686",
                arch: "x86",
                vendor: "unknown",
                os: "uefi",
                env: "",
                abi: "",
            }
            .llvm_target("i686-unknown-uefi", None),
            "i686-unknown-windows-gnu"
        );
        assert_eq!(
            TargetInfo {
                full_arch: "x86_64",
                arch: "x86_64",
                vendor: "unknown",
                os: "uefi",
                env: "",
                abi: "",
            }
            .llvm_target("x86_64-unknown-uefi", None),
            "x86_64-unknown-windows-gnu"
        );
        assert_eq!(
            TargetInfo {
                full_arch: "aarch64",
                arch: "aarch64",
                vendor: "unknown",
                os: "uefi",
                env: "",
                abi: "",
            }
            .llvm_target("aarch64-unknown-uefi", None),
            "aarch64-unknown-windows-gnu"
        );
    }

    // NOTE: Upstream had an `llvm_for_all_rustc_targets` nightly-only test
    // that was skipped via a skip-annotation. Per tla2 rule, the test was
    // removed on fork. It relied on -Zunstable-options and was never wired
    // into CI upstream.
}
