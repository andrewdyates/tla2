// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::process::Command;

mod common;
use common::TempDir;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_liveness_error_location_attributes_instanced_module() {
    let dir = TempDir::new("tla2-liveness-location-instance-module");

    let main = dir.path.join("Main.tla");
    let inst = dir.path.join("InstMod.tla");
    let cfg = dir.path.join("Main.cfg");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
INSTANCE InstMod

VARIABLE x
vars == <<x>>

Init == x = 0
Next == x' = x

Prop == BadProp
====
"#,
    );

    common::write_file(
        &inst,
        br#"
---- MODULE InstMod ----
\* Unbounded quantifier over temporal body triggers EC 2213 (cannot handle temporal formula).
BadProp == \E y : <>TRUE
====
"#,
    );

    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n",
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args([
            "check",
            main.to_str().expect("utf-8 main path"),
            "--config",
            cfg.to_str().expect("utf-8 cfg path"),
            "--no-deadlock",
            "--workers",
            "1",
        ])
        .output()
        .expect("run tla2 check");

    assert!(
        !out.status.success(),
        "expected failure\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("TLC cannot handle the temporal formula"),
        "stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("of module InstMod"),
        "expected liveness error location to attribute InstMod\nstderr:\n{stderr}"
    );
}
