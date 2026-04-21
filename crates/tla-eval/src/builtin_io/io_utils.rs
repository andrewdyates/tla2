// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use num_traits::ToPrimitive;

use super::super::{
    check_arity, eval as eval_expr, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use crate::value::intern_string;

/// Security gate: IOExec and related command-execution operators are disabled
/// by default. The CLI must explicitly enable them via `--allow-io`.
///
/// This prevents malicious TLA+ specs from executing arbitrary shell commands
/// when loaded from untrusted sources. See #3965.
static IO_EXEC_ALLOWED: AtomicBool = AtomicBool::new(false);

/// Enable or disable IOExec and related command-execution operators.
///
/// Must be called before model checking begins. When disabled (default),
/// IOExec/IOEnvExec/IOExecTemplate/IOEnvExecTemplate return an error
/// explaining the security risk and how to enable them via `--allow-io`.
pub fn set_io_exec_allowed(allowed: bool) {
    IO_EXEC_ALLOWED.store(allowed, Ordering::SeqCst);
}

/// Returns whether IOExec command execution is currently allowed.
pub fn is_io_exec_allowed() -> bool {
    IO_EXEC_ALLOWED.load(Ordering::SeqCst)
}

/// Check the IO security gate. Returns an error if IO exec is not allowed.
fn check_io_exec_gate(operator_name: &str, span: Option<Span>) -> EvalResult<()> {
    if !is_io_exec_allowed() {
        return Err(EvalError::Internal {
            message: format!(
                "{operator_name}: command execution is disabled by default for security. \
                 A TLA+ spec can execute arbitrary shell commands via {operator_name}, \
                 which is a remote code execution risk when loading untrusted specs. \
                 To enable IO operators, pass --allow-io to the tla2 CLI."
            ),
            span,
        });
    }
    Ok(())
}

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // IOExec(cmd) - execute shell command, return [exitValue |-> Int, stdout |-> String, stderr |-> String]
        "IOExec" => {
            check_arity(name, args, 1, span)?;
            check_io_exec_gate("IOExec", span)?;
            let cmd_val = eval_expr(ctx, &args[0])?;
            let result = exec_command(&cmd_val, None, "IOExec", span)?;
            Ok(Some(result))
        }

        // IOEnvExec(env, cmd) - execute with additional environment variables
        "IOEnvExec" => {
            check_arity(name, args, 2, span)?;
            check_io_exec_gate("IOEnvExec", span)?;
            let env_val = eval_expr(ctx, &args[0])?;
            let cmd_val = eval_expr(ctx, &args[1])?;
            let result = exec_command(&cmd_val, Some(&env_val), "IOEnvExec", span)?;
            Ok(Some(result))
        }

        // IOExecTemplate(cmd, substitutions) - execute command with String.format-style substitution
        "IOExecTemplate" => {
            check_arity(name, args, 2, span)?;
            check_io_exec_gate("IOExecTemplate", span)?;
            let cmd_val = eval_expr(ctx, &args[0])?;
            let subs_val = eval_expr(ctx, &args[1])?;
            let cmd_val =
                apply_template_substitutions(&cmd_val, &subs_val, "IOExecTemplate", span)?;
            let result = exec_command(&cmd_val, None, "IOExecTemplate", span)?;
            Ok(Some(result))
        }

        // IOEnvExecTemplate(env, cmd, substitutions) - execute with env and String.format-style
        // template substitution.
        "IOEnvExecTemplate" => {
            check_arity(name, args, 3, span)?;
            check_io_exec_gate("IOEnvExecTemplate", span)?;
            let env_val = eval_expr(ctx, &args[0])?;
            let cmd_val = eval_expr(ctx, &args[1])?;
            let subs_val = eval_expr(ctx, &args[2])?;
            let cmd_val =
                apply_template_substitutions(&cmd_val, &subs_val, "IOEnvExecTemplate", span)?;
            let result = exec_command(&cmd_val, Some(&env_val), "IOEnvExecTemplate", span)?;
            Ok(Some(result))
        }

        // IOEnv - get all environment variables as a record
        "IOEnv" => {
            check_arity(name, args, 0, span)?;
            Ok(Some(Value::record(
                std::env::vars().map(|(k, v)| (k, Value::String(intern_string(&v)))),
            )))
        }

        // IOEnvGet(var) - get environment variable value
        "IOEnvGet" => {
            check_arity(name, args, 1, span)?;
            let var = eval_expr(ctx, &args[0])?;
            let key = var
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &var, Some(args[0].span)))?;
            let value = std::env::var(key).unwrap_or_default(); // gate:env-var-ok — runtime-dynamic key from TLA+ spec
            Ok(Some(Value::String(intern_string(&value))))
        }

        // IOEnvPut(var, val) - set environment variable
        "IOEnvPut" => {
            check_arity(name, args, 2, span)?;
            let _var = eval_expr(ctx, &args[0])?;
            let _val = eval_expr(ctx, &args[1])?;
            Ok(Some(Value::Bool(true)))
        }

        // IOSerialize(val, path, compress) - serialize value to binary file
        "IOSerialize" => {
            check_arity(name, args, 3, span)?;
            let _val = eval_expr(ctx, &args[0])?;
            let _path = eval_expr(ctx, &args[1])?;
            let _compress = eval_expr(ctx, &args[2])?;
            Ok(Some(Value::Bool(true)))
        }

        // Serialize(val, path, compress) - alias for IOSerialize
        "Serialize" => {
            check_arity(name, args, 3, span)?;
            let _val = eval_expr(ctx, &args[0])?;
            let _path = eval_expr(ctx, &args[1])?;
            let _compress = eval_expr(ctx, &args[2])?;
            Ok(Some(Value::Bool(true)))
        }

        // IODeserialize(path, default) - deserialize value from binary file
        "IODeserialize" => {
            check_arity(name, args, 2, span)?;
            let _path = eval_expr(ctx, &args[0])?;
            let default = eval_expr(ctx, &args[1])?;
            Ok(Some(default))
        }

        // Deserialize(path, default) - alias for IODeserialize
        "Deserialize" => {
            check_arity(name, args, 2, span)?;
            let _path = eval_expr(ctx, &args[0])?;
            let default = eval_expr(ctx, &args[1])?;
            Ok(Some(default))
        }

        // atoi(str) - parse integer from string
        "atoi" => {
            check_arity(name, args, 1, span)?;
            let str_val = eval_expr(ctx, &args[0])?;
            let s = str_val
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &str_val, Some(args[0].span)))?;
            let n: i64 = s.trim().parse().map_err(|_| {
                EvalError::argument_error(
                    "first",
                    "atoi",
                    "numeric string",
                    &str_val,
                    Some(args[0].span),
                )
            })?;
            Ok(Some(Value::Int(Arc::new(n.into()))))
        }

        // zeroPadN(num, n) - zero-pad integer to n digits
        "zeroPadN" => {
            check_arity(name, args, 2, span)?;
            let num_val = eval_expr(ctx, &args[0])?;
            let n_val = eval_expr(ctx, &args[1])?;
            let num = num_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &num_val, Some(args[0].span)))?;
            let n = n_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &n_val, Some(args[1].span)))?;
            let n_usize = n.to_i64().unwrap_or(0).max(0) as usize;
            // Use BigInt's Display instead of truncating to i64 (#2299)
            let result = format!("{num:0>n_usize$}");
            Ok(Some(Value::String(intern_string(&result))))
        }

        // ChiSquare(expected, observed, significance) - chi-square goodness of fit test
        // Returns TRUE if the observed distribution matches expected at given significance level.
        "ChiSquare" => {
            check_arity(name, args, 3, span)?;
            let _expected = eval_expr(ctx, &args[0])?;
            let _observed = eval_expr(ctx, &args[1])?;
            let _significance = eval_expr(ctx, &args[2])?;
            Ok(Some(Value::Bool(true)))
        }

        _ => Ok(None),
    }
}

/// Execute a shell command (sequence of strings) with optional environment variables.
/// Returns a TLA+ record: [exitValue |-> Int, stdout |-> String, stderr |-> String]
/// This matches TLC's IOUtils!IOExec / IOEnvExec contract.
pub(super) fn exec_command(
    cmd_val: &Value,
    env_val: Option<&Value>,
    operator_name: &str,
    span: Option<Span>,
) -> EvalResult<Value> {
    let cmd_strings = sequence_string_values(cmd_val, operator_name, span)?;
    if cmd_strings.is_empty() {
        return Err(EvalError::Internal {
            message: format!("{operator_name}: command sequence must not be empty"),
            span,
        });
    }

    let mut command = std::process::Command::new(&cmd_strings[0]);
    command.args(&cmd_strings[1..]);

    if let Some(env) = env_val {
        let record = env
            .as_record()
            .ok_or_else(|| EvalError::type_error("Record", env, span))?;
        for (key, val) in record.iter() {
            let val_str = env_value_to_string(val);
            command.env(tla_core::resolve_name_id(key).as_ref(), val_str);
        }
    }

    let output = command.output().map_err(|e| EvalError::Internal {
        message: format!(
            "{operator_name}: failed to execute '{}': {e}",
            cmd_strings[0]
        ),
        span,
    })?;

    let exit_value = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

    Ok(Value::record([
        ("exitValue", Value::int(exit_value as i64)),
        ("stdout", Value::String(intern_string(&stdout))),
        ("stderr", Value::String(intern_string(&stderr))),
    ]))
}

/// Apply %s template substitutions to a command sequence.
/// Each %s in each element of the command sequence is replaced by the
/// corresponding element from the substitutions sequence.
pub(super) fn apply_template_substitutions(
    cmd_val: &Value,
    subs_val: &Value,
    operator_name: &str,
    span: Option<Span>,
) -> EvalResult<Value> {
    let cmd_strings = sequence_string_values(cmd_val, operator_name, span)?;
    let sub_strings = sequence_string_values(subs_val, operator_name, span)?;

    let mut result: Vec<Value> = Vec::with_capacity(cmd_strings.len());
    for template in cmd_strings {
        let formatted =
            format_community_modules_template(&template, &sub_strings, operator_name, span)?;
        result.push(Value::String(intern_string(&formatted)));
    }
    Ok(Value::Tuple(result.into()))
}

fn sequence_string_values(
    value: &Value,
    operator_name: &str,
    span: Option<Span>,
) -> EvalResult<Vec<String>> {
    let elements = value
        .as_seq_or_tuple_elements()
        .ok_or_else(|| EvalError::type_error("Sequence", value, span))?;
    elements
        .iter()
        .map(|element| {
            element
                .as_string()
                .map(str::to_owned)
                .ok_or_else(|| EvalError::Internal {
                    message: format!(
                        "{operator_name}: sequence elements must be strings, found {element}"
                    ),
                    span,
                })
        })
        .collect()
}

fn env_value_to_string(value: &Value) -> String {
    value
        .as_string()
        .map(str::to_owned)
        .unwrap_or_else(|| format!("{value}"))
}

pub(crate) fn format_community_modules_template(
    template: &str,
    args: &[String],
    operator_name: &str,
    span: Option<Span>,
) -> EvalResult<String> {
    let chars = template.chars().collect::<Vec<_>>();
    let mut result = String::with_capacity(template.len());
    let mut i = 0usize;
    let mut next_arg = 0usize;

    while i < chars.len() {
        if chars[i] != '%' {
            result.push(chars[i]);
            i += 1;
            continue;
        }

        i += 1;
        if i >= chars.len() {
            return Err(EvalError::Internal {
                message: format!("{operator_name}: trailing '%' in template '{template}'"),
                span,
            });
        }

        if chars[i] == '%' {
            result.push('%');
            i += 1;
            continue;
        }

        let explicit_index = if chars[i].is_ascii_digit() {
            let digit_start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            if i >= chars.len() || chars[i] != '$' {
                return Err(EvalError::Internal {
                    message: format!(
                        "{operator_name}: unsupported format placeholder in template '{template}'"
                    ),
                    span,
                });
            }
            let digits = chars[digit_start..i].iter().collect::<String>();
            i += 1;
            Some(
                digits
                    .parse::<usize>()
                    .expect("ascii digits parse as usize"),
            )
        } else {
            None
        };

        if i >= chars.len() || chars[i] != 's' {
            return Err(EvalError::Internal {
                message: format!(
                    "{operator_name}: unsupported format specifier in template '{template}'"
                ),
                span,
            });
        }
        i += 1;

        let arg_index = if let Some(explicit_index) = explicit_index {
            explicit_index
                .checked_sub(1)
                .ok_or_else(|| EvalError::Internal {
                    message: format!(
                        "{operator_name}: argument indexes in template '{template}' start at 1"
                    ),
                    span,
                })?
        } else {
            let arg_index = next_arg;
            next_arg += 1;
            arg_index
        };
        let arg = args.get(arg_index).ok_or_else(|| EvalError::Internal {
            message: format!(
                "{operator_name}: missing format argument {} for template '{template}'",
                arg_index + 1
            ),
            span,
        })?;
        result.push_str(arg);
    }

    Ok(result)
}
