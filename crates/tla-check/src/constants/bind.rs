// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constant binding for model checking
//!
//! Binds parsed constant values from TLC config files into the
//! evaluation context, including model value registration.

use crate::config::{Config, ConstantValue};
use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::value::{SetBuilder, Value};
use rustc_hash::FxHashSet;

use super::parse::parse_constant_value;

/// Bind constants from config to the evaluation context
///
/// # Arguments
/// * `ctx` - The evaluation context to bind constants into
/// * `config` - The parsed TLC config
///
/// # Returns
/// * `Ok(())` - All constants bound successfully
/// * `Err(CheckError)` - Error binding a constant
pub fn bind_constants_from_config(ctx: &mut EvalCtx, config: &Config) -> Result<(), EvalError> {
    let names: Vec<&String> = if !config.constants_order.is_empty() {
        let mut out = Vec::with_capacity(config.constants.len());
        let mut seen: FxHashSet<&str> =
            FxHashSet::with_capacity_and_hasher(config.constants.len(), Default::default());

        // Primary order: file order as recorded by the config parser.
        for name in &config.constants_order {
            if config.constants.contains_key(name) {
                out.push(name);
                seen.insert(name.as_str());
            }
        }

        // Deterministic fallback for any constants inserted programmatically (or added by tools)
        // that didn't populate `constants_order`.
        let mut rest: Vec<&String> = config
            .constants
            .keys()
            .filter(|k| !seen.contains(k.as_str()))
            .collect();
        rest.sort();
        out.extend(rest);
        out
    } else {
        // Deterministic fallback: lexical order.
        let mut out: Vec<&String> = config.constants.keys().collect();
        out.sort();
        out
    };

    for name in names {
        let const_val = &config.constants[name];
        let value = match const_val {
            ConstantValue::Value(value_str) => {
                parse_constant_value(value_str).map_err(|e| EvalError::Internal {
                    message: format!("Error parsing CONSTANT {}: {}", name, e),
                    span: None,
                })?
            }
            ConstantValue::ModelValue => {
                // A standalone model value - use the constant name as the model value name
                Value::try_model_value(name.as_str())?
            }
            ConstantValue::ModelValueSet(values) => {
                // Set of model values - bind each individual model value to the context
                let mut set = SetBuilder::new();
                for v in values {
                    let mv = Value::try_model_value(v.as_str())?;
                    // Bind each model value so it can be referenced in the spec
                    ctx.bind_mut(v.clone(), mv.clone());
                    set.insert(mv);
                }
                set.build_value()
            }
            ConstantValue::Replacement(op_name) => {
                if is_syntactic_operator_replacement_name(name) {
                    return Err(EvalError::Internal {
                        message: format!(
                            "config replacement of syntactic operator {name} is unsupported: \
                             SUBSET, UNION, and DOMAIN are parsed as language forms, not named operators"
                        ),
                        span: None,
                    });
                }
                // Operator replacement: when evaluating `name`, use `op_name` instead
                // This is used for things like `Seq <- BoundedSeq` in config files
                ctx.add_op_replacement(name.clone(), op_name.clone());
                // Skip the value binding below - this is an operator replacement, not a value
                continue;
            }
        };

        // Also bind individual model values found in parsed set literals
        // This ensures that when a spec references "m2", it resolves to the same
        // model value that's in the set {m1, m2, m3}
        bind_model_values_from_value(ctx, &value);

        // Mark this constant as config-provided so lookups prioritize env over operator defs.
        // This is essential for cases like `Done == CHOOSE v : v \notin Reg` with
        // `Done = Done` in config - we want the model value @Done, not the CHOOSE.
        ctx.add_config_constant(name.clone());

        // Bind the constant value in the evaluation context
        ctx.bind_mut(name.clone(), value);
    }

    // Module-scoped assignments can introduce model values (e.g., `X = [M] a` or `{a, b}`).
    // TLC treats these identifiers as model values, so we must bind them globally so that
    // rewritten operator bodies can evaluate them.
    //
    // Iterate deterministically to keep model-value registration stable across runs.
    let mut module_names: Vec<&String> = config.module_assignments.keys().collect();
    module_names.sort();
    for module_name in module_names {
        let Some(assigns) = config.module_assignments.get(module_name) else {
            continue;
        };
        let mut lhs_names: Vec<&String> = assigns.keys().collect();
        lhs_names.sort();
        for lhs in lhs_names {
            let value_str = &assigns[lhs];
            let value = parse_constant_value(value_str).map_err(|e| EvalError::Internal {
                message: format!("Error parsing module-scoped CONSTANT value: {}", e),
                span: None,
            })?;
            bind_model_values_from_value(ctx, &value);
        }
    }

    Ok(())
}

fn is_syntactic_operator_replacement_name(name: &str) -> bool {
    matches!(name, "SUBSET" | "UNION" | "DOMAIN")
}

/// Recursively extract and bind model values from a Value
/// This ensures that model values like `m1`, `m2` from a set `{m1, m2, m3}`
/// can be referenced directly in the spec
fn bind_model_values_from_value(ctx: &mut EvalCtx, value: &Value) {
    match value {
        Value::ModelValue(name) => {
            // Bind this model value so it can be referenced by name
            ctx.bind_mut(name.to_string(), value.clone());
        }
        Value::Set(set) => {
            // Recursively bind model values in set elements
            for elem in set.as_ref() {
                bind_model_values_from_value(ctx, elem);
            }
        }
        Value::Tuple(elems) => {
            // Recursively bind model values in tuple elements
            for elem in elems.iter() {
                bind_model_values_from_value(ctx, elem);
            }
        }
        Value::Seq(seq) => {
            // Recursively bind model values in seq elements
            for elem in seq.iter() {
                bind_model_values_from_value(ctx, elem);
            }
        }
        Value::Record(rec) => {
            // Recursively bind model values in record field values
            for (_, value) in rec.iter() {
                bind_model_values_from_value(ctx, value);
            }
        }
        _ => {
            // Other value types don't contain model values to bind
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::ConstantValue;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bind_constants() {
        let mut ctx = EvalCtx::new();
        let mut config = Config::new();
        config
            .constants
            .insert("N".to_string(), ConstantValue::Value("3".to_string()));
        config.constants.insert(
            "Procs".to_string(),
            ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
        );

        bind_constants_from_config(&mut ctx, &config).unwrap();

        // Check N is bound
        let n = ctx.lookup("N").unwrap();
        assert_eq!(n, Value::int(3));

        // Check Procs is bound as set of model values
        let procs = ctx.lookup("Procs").unwrap();
        if let Value::Set(set) = &procs {
            assert_eq!(set.len(), 2);
            assert!(set.contains(&Value::try_model_value("p1").unwrap()));
        } else {
            panic!("Expected Procs to be a set");
        }
    }

    /// Regression test for #3356: model values inside record constants must be bound
    ///
    /// When a config has `c = [x |-> m1, y |-> m2]`, the model values m1 and m2
    /// must be bound in the eval context so specs can reference them by name.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bind_model_values_in_record_constant() {
        let mut ctx = EvalCtx::new();
        let mut config = Config::new();
        config.constants.insert(
            "c".to_string(),
            ConstantValue::Value("[x |-> m1_rec, y |-> m2_rec]".to_string()),
        );

        bind_constants_from_config(&mut ctx, &config).unwrap();

        // The record should be bound as constant "c"
        let c = ctx.lookup("c").unwrap();
        let rec = c.as_record().expect("Expected record value for c");
        assert_eq!(rec.len(), 2);

        // Model values m1_rec and m2_rec should be individually bound
        let m1 = ctx.lookup("m1_rec");
        assert!(
            m1.is_some(),
            "Model value m1_rec inside record should be bound in context"
        );
        assert_eq!(
            m1.unwrap(),
            Value::try_model_value("m1_rec").unwrap(),
            "m1_rec should be a model value"
        );

        let m2 = ctx.lookup("m2_rec");
        assert!(
            m2.is_some(),
            "Model value m2_rec inside record should be bound in context"
        );
        assert_eq!(
            m2.unwrap(),
            Value::try_model_value("m2_rec").unwrap(),
            "m2_rec should be a model value"
        );
    }

    /// Regression test for #62: config constant precedence
    ///
    /// When a constant like `Done = Done` is in the config file, it should:
    /// 1. Be marked as a config constant (is_config_constant returns true)
    /// 2. Take precedence over any operator definition like `Done == CHOOSE v : ...`
    ///
    /// This fixes specs like MCInnerSequential, MCLiveInternalMemory, MCLiveWriteThroughCache
    /// where config values should override unbounded CHOOSE operators.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_config_constant_precedence() {
        let mut ctx = EvalCtx::new();
        let mut config = Config::new();

        // Simulate config file with `Done = Done` (model value assignment)
        // This is the pattern that overrides `Done == CHOOSE v : v \notin Reg`
        config
            .constants
            .insert("Done".to_string(), ConstantValue::Value("Done".to_string()));

        // Before binding, should not be a config constant
        assert!(
            !ctx.is_config_constant("Done"),
            "Done should not be a config constant before binding"
        );

        bind_constants_from_config(&mut ctx, &config).unwrap();

        // After binding, should be marked as a config constant
        assert!(
            ctx.is_config_constant("Done"),
            "Done should be marked as a config constant after binding from config"
        );

        // The value should be the model value @Done, not evaluated from CHOOSE
        let done = ctx.lookup("Done").unwrap();
        assert_eq!(
            done,
            Value::try_model_value("Done").unwrap(),
            "Done should be model value @Done from config"
        );

        // Also test with a regular integer constant
        let mut config2 = Config::new();
        config2.constants.insert(
            "MaxRetries".to_string(),
            ConstantValue::Value("5".to_string()),
        );

        let mut ctx2 = EvalCtx::new();
        bind_constants_from_config(&mut ctx2, &config2).unwrap();

        assert!(
            ctx2.is_config_constant("MaxRetries"),
            "MaxRetries should be marked as config constant"
        );
        assert_eq!(ctx2.lookup("MaxRetries").unwrap(), Value::int(5));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_reject_syntactic_operator_replacement_names() {
        for name in ["SUBSET", "UNION", "DOMAIN"] {
            let mut ctx = EvalCtx::new();
            let mut config = Config::new();
            config.constants.insert(
                name.to_string(),
                ConstantValue::Replacement("Replacement".to_string()),
            );

            let err = bind_constants_from_config(&mut ctx, &config)
                .expect_err("syntactic operator replacements should be rejected");
            let message = err.to_string();
            assert!(
                message.contains("syntactic operator"),
                "{name}: unexpected error: {message}"
            );
            assert!(
                message.contains(name),
                "{name}: error should name rejected replacement: {message}"
            );
        }
    }
}
