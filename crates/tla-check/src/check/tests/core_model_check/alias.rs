// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ==================== ALIAS trace evaluation (#3012) ====================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alias_transforms_trace_states() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec with an ALIAS operator that adds a computed field.
    let src = r#"
---- MODULE AliasTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TooLarge == x < 3
Alias == [x |-> x, doubled |-> x + x]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TooLarge".to_string()],
        alias: Some("Alias".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation { trace, .. } => {
            assert_eq!(trace.len(), 4); // x=0,1,2,3

            // Create an EvalCtx to apply the alias.
            let mut ctx = EvalCtx::new();
            ctx.load_module(&module);
            // Register state variables in the VarRegistry (required for bind_state_array).
            ctx.register_vars(["x".to_string()]);
            bind_constants_from_config(&mut ctx, &config).unwrap();

            let aliased = trace.apply_alias(&mut ctx, "Alias");
            assert_eq!(aliased.len(), 4);

            // Each aliased state should have "x" and "doubled" fields.
            let s0 = &aliased.states[0];
            assert_eq!(s0.get("x"), Some(&Value::int(0)));
            assert_eq!(s0.get("doubled"), Some(&Value::int(0)));

            let s3 = &aliased.states[3];
            assert_eq!(s3.get("x"), Some(&Value::int(3)));
            assert_eq!(s3.get("doubled"), Some(&Value::int(6)));
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alias_non_record_keeps_original_state() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // ALIAS that returns a non-record (integer) — should keep original state.
    let src = r#"
---- MODULE AliasNonRecord ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TooLarge == x < 2
BadAlias == x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TooLarge".to_string()],
        alias: Some("BadAlias".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation { trace, .. } => {
            let mut ctx = EvalCtx::new();
            ctx.load_module(&module);
            ctx.register_vars(["x".to_string()]);
            bind_constants_from_config(&mut ctx, &config).unwrap();

            let aliased = trace.apply_alias(&mut ctx, "BadAlias");
            // Non-record ALIAS: states should be unchanged.
            assert_eq!(aliased.len(), trace.len());
            for (orig, alias_state) in trace.states.iter().zip(aliased.states.iter()) {
                assert_eq!(orig.get("x"), alias_state.get("x"));
            }
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}
