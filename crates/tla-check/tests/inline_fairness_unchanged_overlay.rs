// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #3100: WF fairness overlays with UNCHANGED conjuncts
//! should stay on the compiled inline path instead of falling back to AST eval.

use tla_check::Config;
use tla_check::{resolve_spec_from_config, CheckResult};
use tla_core::{lower, parse_to_syntax_tree, FileId};

mod common;

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn inline_fairness_unchanged_overlay_stays_compiled() {
    let _skip_liveness = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");
    let _profile = common::EnvVarGuard::set("TLA2_LIVENESS_PROFILE", Some("1"));

    let src = r#"
---- MODULE InlineFairnessUnchanged ----
EXTENDS Integers

VARIABLES x, y
vars == <<x, y>>

Init == /\ x = 0 /\ y = 0
AdvanceX == /\ x < 1 /\ x' = x + 1 /\ UNCHANGED y
AdvanceY == /\ y < 1 /\ y' = y + 1 /\ UNCHANGED x
Next == AdvanceX \/ AdvanceY

Done == x = 1 /\ y = 1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Terminated == <>Done

====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result
        .module
        .expect("module lowering should produce a root module");

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved =
        resolve_spec_from_config(&spec_config, &tree).expect("spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Terminated".to_string()],
        ..Default::default()
    };
    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "expected the two-bit progress lattice to contain exactly 4 states"
            );
        }
        other => panic!(
            "expected liveness success for fairness spec with UNCHANGED conjuncts, got {other:?}"
        ),
    }
}
