// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use std::time::Duration;

use common::TempDir;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn alias_instance_var_registry_uses_extends_only_variable_registry_for_named_instance_modules() {
    let dir = TempDir::new("tla2-alias-instance-var-registry");
    let main = dir.path.join("Main.tla");
    let inner = dir.path.join("Inner.tla");
    let cfg = dir.path.join("Main.cfg");

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
EXTENDS Integers

VARIABLES x, derived
====
"#,
    );

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
EXTENDS Integers

VARIABLE data

x == data[1]
derived == data[2]

\* Named INSTANCE is present to load Inner into the checker dependency set.
I == INSTANCE Inner

Init == data = <<0, 0>>
Next == data' = <<data[1] + 1, data[1] + 1>>
TooLarge == x < 3
Alias == [x |-> x, derived |-> derived]
====
"#,
    );

    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nINVARIANT TooLarge\nALIAS Alias\nCHECK_DEADLOCK FALSE\n",
    );

    let (code, stdout, stderr) = common::run_tla_parsed_with_timeout(
        &[
            "check",
            main.to_str().expect("utf-8 spec path"),
            "--config",
            cfg.to_str().expect("utf-8 cfg path"),
            "--workers",
            "1",
            "--no-deadlock",
        ],
        Duration::from_secs(90),
    );

    assert_ne!(
        code, 0,
        "expected invariant violation, not success\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("Error: Invariant TooLarge is violated."),
        "expected invariant violation output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("State::to_values") && !stderr.contains("panicked"),
        "ALIAS path must not panic on INSTANCE variables\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("/\\ x = 3"),
        "expected aliased trace field x in counterexample trace\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("/\\ derived = 3"),
        "expected aliased trace field derived in counterexample trace\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("data = <<"),
        "expected aliased trace output, not raw state variable output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
