// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;
use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{self, Command};

/// The directory containing this test binary.
pub fn exe_dir() -> PathBuf {
    let exe = env::current_exe().unwrap();
    exe.parent().unwrap().to_path_buf()
}

/// The directory to use for test probes.
pub fn out_dir() -> Cow<'static, Path> {
    let base = if let Some(tmpdir) = option_env!("CARGO_TARGET_TMPDIR") {
        PathBuf::from(tmpdir)
    } else if let Some(tmpdir) = env::var_os("TESTS_TARGET_DIR") {
        tmpdir.into()
    } else {
        // Use the same path as this test binary.
        exe_dir()
    };
    let exe_name = env::current_exe()
        .ok()
        .and_then(|path| path.file_stem().map(|stem| stem.to_owned()))
        .unwrap_or_else(|| "autocfg-test".into());
    let dir = base.join("autocfg-probes").join(format!(
        "{}-{}",
        exe_name.to_string_lossy(),
        process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    Cow::Owned(dir)
}

/// Build a small rlib for rustflags tests.
#[allow(dead_code)]
pub fn build_probe_rlib(out: &Path) -> PathBuf {
    let source = out.join("autocfg_probe.rs");
    let mut file = fs::File::create(&source).unwrap();
    file.write_all(b"pub fn marker() {}\n").unwrap();

    let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let status = Command::new(rustc)
        .arg("--crate-name")
        .arg("autocfg_probe")
        .arg("--crate-type")
        .arg("rlib")
        .arg(&source)
        .arg("--out-dir")
        .arg(out)
        .status()
        .unwrap();
    assert!(status.success());

    out.join("libautocfg_probe.rlib")
}
