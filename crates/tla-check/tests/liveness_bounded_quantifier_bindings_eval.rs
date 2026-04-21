// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_check::CheckResult;
use tla_check::Config;

mod common;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_module_applies_quantifier_bindings_during_liveness_eval() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessBoundedQuantifierBindingsApplied ----

VARIABLE x
Init == x = 0
Next == x' = x

\* Forces temporal-level bounded-quantifier expansion, producing leaf predicates
\* that must be evaluated under the enumerated bindings for y. Uses a state
\* variable (x) so the predicate is not constant-foldable and avoids the
\* tautology checker (which rejects <>(TRUE) from constant y = 2).
Prop == \E y \in {0, 1} : <>(x = y)

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
        other => panic!("expected Success, got: {other:?}"),
    }
}
