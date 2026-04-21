// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_check::CheckResult;
use tla_check::Config;

mod common;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_module_preserves_quantifier_bindings_in_enabled_eval() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessEnabledQuantifierBindings ----

VARIABLE x
Clients == {1, 2}

Init == x = 0
Next == UNCHANGED x

Act(c) ==
    /\ x = c
    /\ x' = x

Prop == \A c \in Clients : WF_x(Act(c))

====
"#;

    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1);
        }
        CheckResult::Error { error, .. } => {
            let msg = format!("{error}");
            assert!(
                !msg.contains("Undefined variable"),
                "expected liveness check without undefined variable, got: {msg}"
            );
            panic!("expected Success, got Error: {msg}");
        }
        other => panic!("expected Success, got: {other:?}"),
    }
}
