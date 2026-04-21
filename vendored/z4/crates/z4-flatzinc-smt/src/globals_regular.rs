// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Regular (DFA) global constraint encoding for FlatZinc-to-SMT translation

use std::collections::HashMap;

use z4_flatzinc_parser::ast::Expr;

use crate::error::TranslateError;
use crate::translate::{Context, SmtInt};

/// Regular constraint: sequence x[1..n] must be accepted by a DFA.
///
/// args: [x_array, Q, S, d_flat, q0, F_set]
/// - x: array of variables (1-indexed values from input alphabet 1..S)
/// - Q: number of states
/// - S: size of input alphabet
/// - d_flat: flat transition table, length Q*S, d[q][s] = d_flat[(q-1)*S + (s-1)]
/// - q0: initial state (1-based)
/// - F: set of accepting states
///
/// Encoding: layered Boolean variables b[t][q] = "in state q at step t".
pub(crate) fn regular(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 6 {
        return Err(TranslateError::WrongArgCount {
            name: "regular".into(),
            expected: 6,
            got: args.len(),
        });
    }

    let x_vars = ctx.expr_to_smt_array(&args[0])?;
    let n = x_vars.len();
    if n == 0 {
        return Ok(());
    }

    let q_count = ctx.resolve_int(&args[1])? as usize;
    let s_count = ctx.resolve_int(&args[2])? as usize;
    let d_flat = ctx.resolve_int_array(&args[3])?;
    let q0 = ctx.resolve_int(&args[4])? as usize;
    let f_set = ctx.resolve_set(&args[5])?;

    if d_flat.len() != q_count * s_count {
        return Err(TranslateError::UnsupportedType(format!(
            "regular: transition table length {} != Q*S = {}*{} = {}",
            d_flat.len(),
            q_count,
            s_count,
            q_count * s_count
        )));
    }

    let aux_id = ctx.next_aux_id();

    // Declare layered Booleans and set initial state
    regular_init(ctx, aux_id, n, q_count, q0);

    // Encode DFA transitions
    regular_transitions(ctx, aux_id, &x_vars, q_count, s_count, &d_flat);

    // Encode accepting condition
    regular_accept(ctx, aux_id, n, &f_set);

    Ok(())
}

/// Declare layered Boolean variables and set initial state for regular constraint.
fn regular_init(ctx: &mut Context, aux_id: usize, n: usize, q_count: usize, q0: usize) {
    for t in 0..=n {
        for q in 1..=q_count {
            let name = format!("_reg{aux_id}_{t}_{q}");
            ctx.emit_fmt(format_args!("(declare-const {name} Bool)"));
        }
    }
    // b[0][q0] = true, b[0][q] = false for q != q0
    for q in 1..=q_count {
        let name = format!("_reg{aux_id}_0_{q}");
        if q == q0 {
            ctx.emit_fmt(format_args!("(assert {name})"));
        } else {
            ctx.emit_fmt(format_args!("(assert (not {name}))"));
        }
    }
}

/// Encode DFA transitions: b[t+1][q'] = ∨_{q,s} (b[t][q] ∧ x[t+1]=s ∧ d[q][s]=q').
///
/// Uses a pre-computed reverse transition table (q_target → [(q_src, s)]) to avoid
/// the O(n × Q² × S) inner scan. Complexity is O(Q × S) for table construction
/// plus O(n × Q × avg_fan_in) for emission. See #326.
fn regular_transitions(
    ctx: &mut Context,
    aux_id: usize,
    x_vars: &[String],
    q_count: usize,
    s_count: usize,
    d_flat: &[i64],
) {
    // Pre-compute reverse transition table: q_target -> [(q_src, s)]
    let mut reverse: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    for q_src in 1..=q_count {
        for s in 1..=s_count {
            let dest = d_flat[(q_src - 1) * s_count + (s - 1)] as usize;
            reverse.entry(dest).or_default().push((q_src, s));
        }
    }

    for (t, x_var) in x_vars.iter().enumerate() {
        for q_target in 1..=q_count {
            let b_next = format!("_reg{aux_id}_{}_{}", t + 1, q_target);
            let reaching: Vec<String> = reverse
                .get(&q_target)
                .map(|sources| {
                    sources
                        .iter()
                        .map(|(q_src, s)| {
                            let b_cur = format!("_reg{aux_id}_{t}_{q_src}");
                            format!("(and {b_cur} (= {} {}))", x_var, SmtInt(*s as i64))
                        })
                        .collect()
                })
                .unwrap_or_default();

            if reaching.is_empty() {
                ctx.emit_fmt(format_args!("(assert (not {b_next}))"));
            } else if reaching.len() == 1 {
                ctx.emit_fmt(format_args!("(assert (= {b_next} {}))", reaching[0]));
            } else {
                ctx.emit_fmt(format_args!(
                    "(assert (= {b_next} (or {})))",
                    reaching.join(" ")
                ));
            }
        }
    }
}

/// Encode DFA accepting condition: ∨_{q ∈ F} b[n][q].
fn regular_accept(ctx: &mut Context, aux_id: usize, n: usize, f_set: &[i64]) {
    if f_set.is_empty() {
        ctx.emit("(assert false)");
    } else {
        let accept: Vec<String> = f_set
            .iter()
            .map(|&q| format!("_reg{aux_id}_{n}_{q}"))
            .collect();
        if accept.len() == 1 {
            ctx.emit_fmt(format_args!("(assert {})", accept[0]));
        } else {
            ctx.emit_fmt(format_args!("(assert (or {}))", accept.join(" ")));
        }
    }
}
