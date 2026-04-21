// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cranelift IR lowering for TLA+ expressions.
//!
//! Translates TLA+ AST nodes into Cranelift IR instructions.  This is the
//! code-generation backend; the preflight pass (see `preflight.rs`) has
//! already validated that all operations are safe for i64.
//!
//! The core `compile_expr_bound` function handles arithmetic, comparison,
//! boolean, and control flow lowering. Specialized subsystems are in
//! sibling modules:
//!
//! - [`super::lower_set`]: Set membership compilation (`\in`, `\notin`)
//! - [`super::lower_quantifier`]: Quantifier compilation (`\A`, `\E`)
//! - [`super::lower_func`]: Function application lookup (`f[x]`)
//! - [`super::lower_record`]: Record field access (`r.field`)

use crate::error::JitError;
use cranelift_codegen::ir::{types, InstBuilder, TrapCode};
use cranelift_frontend::FunctionBuilder;
use num_traits::ToPrimitive;
use std::alloc::Layout;
use std::cell::RefCell;
use std::collections::HashMap;
use tla_core::ast::Expr;
use tla_core::span::Spanned;

use super::lower_func::compile_func_apply_lookup;
use super::lower_quantifier::compile_quantifier;
use super::lower_record::compile_record_access_runtime;
use super::lower_set::{
    compile_membership_chain, extract_set_elements, try_compile_range_membership,
};
use super::preflight::{preflight_const_i64, preflight_const_value, PreflightValue};

thread_local! {
    /// Collects (pointer, layout) pairs from Box::into_raw calls during
    /// JIT compilation so that JitContext::Drop can reclaim them.
    pub(crate) static LEAKED_ALLOCS: RefCell<Vec<(*mut u8, Layout)>> = RefCell::new(Vec::new());
}

/// Variable bindings: maps bound variable names to their Cranelift IR values.
///
/// Used by quantifier loop compilation to pass the current loop element
/// as a runtime value to the body expression, instead of requiring
/// compile-time substitution.
pub(crate) type Bindings<'a> = HashMap<&'a str, cranelift_codegen::ir::Value>;

/// Maximum number of domain elements before switching from unrolled
/// compilation (N copies of the body) to a loop-based compilation
/// (single body in a counted loop). Unrolling is faster for tiny
/// domains because it avoids loop overhead; looped is better for
/// larger domains because it keeps code size small (better I-cache).
pub(crate) const UNROLL_THRESHOLD: usize = 4;

/// Compile an expression to Cranelift IR, returning the Value.
///
/// Accepts `&Spanned<Expr>` to preserve span information through lowering,
/// enabling runtime error reporting with blame spans. Part of #747.
///
/// This is the top-level entry point with no variable bindings.
/// For quantifier bodies that reference bound variables, use
/// `compile_expr_bound` instead.
pub(crate) fn compile_expr_inner(
    builder: &mut FunctionBuilder,
    expr: &Spanned<Expr>,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    let empty = Bindings::new();
    compile_expr_bound(builder, expr, &empty)
}

/// Compile an expression to Cranelift IR with variable bindings.
///
/// Like `compile_expr_inner`, but additionally resolves `Ident` nodes
/// against the provided `bindings` map. This is used by quantifier loop
/// compilation where the bound variable (e.g., `x` in `\A x \in S: P(x)`)
/// is a runtime Cranelift value rather than a compile-time constant.
pub(crate) fn compile_expr_bound(
    builder: &mut FunctionBuilder,
    expr: &Spanned<Expr>,
    bindings: &Bindings<'_>,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::condcodes::IntCC;

    fn canonicalize_bool(
        builder: &mut FunctionBuilder,
        val: cranelift_codegen::ir::Value,
    ) -> cranelift_codegen::ir::Value {
        let is_true = builder.ins().icmp_imm(IntCC::NotEqual, val, 0);
        builder.ins().uextend(types::I64, is_true)
    }

    // The span is available here: expr.span
    // Future: use it for runtime error reporting (division by zero, etc.)
    let _ = expr.span; // suppress unused warning until runtime errors are added

    match &expr.node {
        // === Bound variable lookup ===
        //
        // When compiling inside a quantifier loop body, the bound variable
        // (e.g., `x` in `\A x \in S: P(x)`) is available as a Cranelift
        // Value in the bindings map. Return it directly.
        Expr::Ident(name, _) if bindings.contains_key(name.as_str()) => Ok(bindings[name.as_str()]),

        // Integer literal
        Expr::Int(n) => {
            let val = n
                .to_i64()
                .ok_or_else(|| JitError::CompileError("Integer too large for i64".to_string()))?;
            Ok(builder.ins().iconst(types::I64, val))
        }

        // Boolean literals
        Expr::Bool(true) => Ok(builder.ins().iconst(types::I64, 1)),
        Expr::Bool(false) => Ok(builder.ins().iconst(types::I64, 0)),

        // Arithmetic operations (overflow-checked — Part of #3868)
        //
        // Cranelift integer ops wrap on overflow. TLA+ integers are unbounded,
        // so wrapping would silently produce wrong results. For constant
        // expressions the preflight pass catches overflow at compile time, but
        // quantifier loop bodies contain runtime variables where preflight
        // cannot help. We therefore emit overflow-detecting instructions
        // (`sadd_overflow` / `ssub_overflow` / `smul_overflow`) and trap on
        // the overflow flag via `trapnz`.
        Expr::Add(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let (result, overflow) = builder.ins().sadd_overflow(lhs, rhs);
            builder.ins().trapnz(overflow, TrapCode::IntegerOverflow);
            Ok(result)
        }
        Expr::Sub(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let (result, overflow) = builder.ins().ssub_overflow(lhs, rhs);
            builder.ins().trapnz(overflow, TrapCode::IntegerOverflow);
            Ok(result)
        }
        Expr::Mul(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let (result, overflow) = builder.ins().smul_overflow(lhs, rhs);
            builder.ins().trapnz(overflow, TrapCode::IntegerOverflow);
            Ok(result)
        }
        Expr::Div(left, right) => {
            // Regular division (/) - truncates toward zero
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            Ok(builder.ins().sdiv(lhs, rhs))
        }
        Expr::IntDiv(left, right) => {
            // TLA+ \div - floor division, matches TLC semantics
            // q = a / b (truncated); if (a ^ b) < 0 && a % b != 0 then q - 1 else q
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;

            let q = builder.ins().sdiv(lhs, rhs);
            let r = builder.ins().srem(lhs, rhs);
            let zero = builder.ins().iconst(types::I64, 0);
            let one = builder.ins().iconst(types::I64, 1);
            // signs_differ = (a XOR b) < 0
            let lhs_xor_rhs = builder.ins().bxor(lhs, rhs);
            let signs_differ = builder.ins().icmp(IntCC::SignedLessThan, lhs_xor_rhs, zero);
            // r_nonzero = r != 0
            let r_nonzero = builder.ins().icmp(IntCC::NotEqual, r, zero);
            let need_adjust = builder.ins().band(signs_differ, r_nonzero);
            let q_minus_1 = builder.ins().isub(q, one);
            Ok(builder.ins().select(need_adjust, q_minus_1, q))
        }
        Expr::Mod(left, right) => {
            // TLA+ % - Euclidean modulo with positive divisor (guaranteed by preflight)
            // rem_euclid(a, b) with b > 0: let r = a % b; if r < 0 { r + b } else { r }
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;

            let r = builder.ins().srem(lhs, rhs);
            let zero = builder.ins().iconst(types::I64, 0);

            // Check if remainder < 0
            let r_neg = builder.ins().icmp(IntCC::SignedLessThan, r, zero);
            // Adjusted remainder: r + b (makes it non-negative)
            let r_adjusted = builder.ins().iadd(r, rhs);
            // Final: if r < 0 then r + b else r
            Ok(builder.ins().select(r_neg, r_adjusted, r))
        }
        Expr::Neg(inner) => {
            let val = compile_expr_bound(builder, inner.as_ref(), bindings)?;
            // Negating i64::MIN overflows (there is no positive i64::MAX + 1).
            let is_min = builder.ins().icmp_imm(IntCC::Equal, val, i64::MIN);
            builder.ins().trapnz(is_min, TrapCode::IntegerOverflow);
            Ok(builder.ins().ineg(val))
        }
        Expr::Pow(base, exp) => {
            let _ = (base, exp);
            // `compile_expr` only accepts constant expressions today. Reuse the
            // preflight evaluator so exponentiation matches the checked i64 path
            // for arbitrary non-negative exponents instead of hard-coding 0..=8.
            let value = preflight_const_i64(&expr.node)?;
            Ok(builder.ins().iconst(types::I64, value))
        }

        // Comparisons (return 0 or 1)
        Expr::Eq(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let cmp = builder.ins().icmp(IntCC::Equal, lhs, rhs);
            Ok(builder.ins().uextend(types::I64, cmp))
        }
        Expr::Neq(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let cmp = builder.ins().icmp(IntCC::NotEqual, lhs, rhs);
            Ok(builder.ins().uextend(types::I64, cmp))
        }
        Expr::Lt(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let cmp = builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs);
            Ok(builder.ins().uextend(types::I64, cmp))
        }
        Expr::Leq(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let cmp = builder.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs);
            Ok(builder.ins().uextend(types::I64, cmp))
        }
        Expr::Gt(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let cmp = builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs);
            Ok(builder.ins().uextend(types::I64, cmp))
        }
        Expr::Geq(left, right) => {
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let cmp = builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs);
            Ok(builder.ins().uextend(types::I64, cmp))
        }

        // Boolean operations
        Expr::And(left, right) => {
            // Short-circuit evaluation: if lhs is false, rhs is not evaluated.
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let lhs_true = builder.ins().icmp_imm(IntCC::NotEqual, lhs, 0);

            let rhs_block = builder.create_block();
            let done_block = builder.create_block();
            builder.append_block_param(done_block, types::I64);

            let zero = builder.ins().iconst(types::I64, 0);
            builder
                .ins()
                .brif(lhs_true, rhs_block, &[], done_block, &[zero]);

            builder.switch_to_block(rhs_block);
            builder.seal_block(rhs_block);
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let rhs = canonicalize_bool(builder, rhs);
            builder.ins().jump(done_block, &[rhs]);

            builder.switch_to_block(done_block);
            builder.seal_block(done_block);
            Ok(builder.block_params(done_block)[0])
        }
        Expr::Or(left, right) => {
            // Short-circuit evaluation: if lhs is true, rhs is not evaluated.
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let lhs_true = builder.ins().icmp_imm(IntCC::NotEqual, lhs, 0);

            let rhs_block = builder.create_block();
            let done_block = builder.create_block();
            builder.append_block_param(done_block, types::I64);

            let one = builder.ins().iconst(types::I64, 1);
            builder
                .ins()
                .brif(lhs_true, done_block, &[one], rhs_block, &[]);

            builder.switch_to_block(rhs_block);
            builder.seal_block(rhs_block);
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let rhs = canonicalize_bool(builder, rhs);
            builder.ins().jump(done_block, &[rhs]);

            builder.switch_to_block(done_block);
            builder.seal_block(done_block);
            Ok(builder.block_params(done_block)[0])
        }
        Expr::Not(inner) => {
            let val = compile_expr_bound(builder, inner.as_ref(), bindings)?;
            let val = canonicalize_bool(builder, val);
            let one = builder.ins().iconst(types::I64, 1);
            Ok(builder.ins().isub(one, val))
        }
        Expr::Implies(left, right) => {
            // Short-circuit evaluation: if lhs is false, rhs is not evaluated.
            //
            // NOTE: This is equivalent to (~A) \/ B, but relying on \/ in a
            // lowering is easy to get wrong; implement directly.
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let lhs_true = builder.ins().icmp_imm(IntCC::NotEqual, lhs, 0);

            let rhs_block = builder.create_block();
            let done_block = builder.create_block();
            builder.append_block_param(done_block, types::I64);

            let one = builder.ins().iconst(types::I64, 1);
            builder
                .ins()
                .brif(lhs_true, rhs_block, &[], done_block, &[one]);

            builder.switch_to_block(rhs_block);
            builder.seal_block(rhs_block);
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let rhs = canonicalize_bool(builder, rhs);
            builder.ins().jump(done_block, &[rhs]);

            builder.switch_to_block(done_block);
            builder.seal_block(done_block);
            Ok(builder.block_params(done_block)[0])
        }
        Expr::Equiv(left, right) => {
            // A <=> B  ===  (A = B)
            let lhs = compile_expr_bound(builder, left.as_ref(), bindings)?;
            let rhs = compile_expr_bound(builder, right.as_ref(), bindings)?;
            let lhs = canonicalize_bool(builder, lhs);
            let rhs = canonicalize_bool(builder, rhs);
            let cmp = builder.ins().icmp(IntCC::Equal, lhs, rhs);
            Ok(builder.ins().uextend(types::I64, cmp))
        }

        // Control flow
        Expr::If(cond, then_expr, else_expr) => {
            let cond_val = compile_expr_bound(builder, cond.as_ref(), bindings)?;
            let cond_bool = builder.ins().icmp_imm(IntCC::NotEqual, cond_val, 0);

            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let done_block = builder.create_block();
            builder.append_block_param(done_block, types::I64);

            builder
                .ins()
                .brif(cond_bool, then_block, &[], else_block, &[]);

            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            let then_val = compile_expr_bound(builder, then_expr.as_ref(), bindings)?;
            builder.ins().jump(done_block, &[then_val]);

            builder.switch_to_block(else_block);
            builder.seal_block(else_block);
            let else_val = compile_expr_bound(builder, else_expr.as_ref(), bindings)?;
            builder.ins().jump(done_block, &[else_val]);

            builder.switch_to_block(done_block);
            builder.seal_block(done_block);
            Ok(builder.block_params(done_block)[0])
        }

        // === Set membership: x \in S ===
        Expr::In(elem, set) => {
            // Try range optimization: x \in a..b -> x >= a && x <= b
            if let Some(result) = try_compile_range_membership(builder, elem, set, bindings, false)?
            {
                return Ok(result);
            }

            let set_vals = extract_set_elements(&set.node)?;
            if set_vals.is_empty() {
                return Ok(builder.ins().iconst(types::I64, 0));
            }

            let elem_val = compile_expr_bound(builder, elem.as_ref(), bindings)?;
            compile_membership_chain(builder, elem_val, &set_vals)
        }

        // === Set non-membership: x \notin S ===
        Expr::NotIn(elem, set) => {
            // Try range optimization: x \notin a..b -> x < a || x > b
            if let Some(result) = try_compile_range_membership(builder, elem, set, bindings, true)?
            {
                return Ok(result);
            }

            let set_vals = extract_set_elements(&set.node)?;
            if set_vals.is_empty() {
                return Ok(builder.ins().iconst(types::I64, 1));
            }

            let elem_val = compile_expr_bound(builder, elem.as_ref(), bindings)?;
            let in_result = compile_membership_chain(builder, elem_val, &set_vals)?;
            // NOT: 1 - in_result (in_result is already 0 or 1)
            let one = builder.ins().iconst(types::I64, 1);
            Ok(builder.ins().isub(one, in_result))
        }

        // === Quantifiers: \A x \in S : P(x) and \E x \in S : P(x) ===
        Expr::Forall(bounds, body) => {
            compile_quantifier(builder, bounds, body, expr, true, bindings)
        }
        Expr::Exists(bounds, body) => {
            compile_quantifier(builder, bounds, body, expr, false, bindings)
        }

        // === Function application: f[x] ===
        Expr::FuncApply(func, arg) => {
            // Try fully-constant evaluation first
            if let Ok(value) = preflight_const_i64(&expr.node) {
                return Ok(builder.ins().iconst(types::I64, value));
            }

            // Runtime argument path: function must be compile-time known
            let func_val = preflight_const_value(&func.node)?;
            match func_val {
                PreflightValue::Function(pairs) => {
                    let arg_val = compile_expr_bound(builder, arg.as_ref(), bindings)?;
                    compile_func_apply_lookup(builder, &pairs, arg_val)
                }
                PreflightValue::Record(pairs) => {
                    // Record used as function: r[field_string] — the argument
                    // must be a constant string key. This is rare in JIT context;
                    // fall back to preflight error for now.
                    let _ = pairs;
                    Err(JitError::UnsupportedExpr(
                        "record-as-function application with runtime arg not supported in JIT"
                            .to_string(),
                    ))
                }
                other => Err(JitError::TypeMismatch {
                    expected: "function".to_string(),
                    actual: other.ty_name().to_string(),
                }),
            }
        }

        // === Record field access: r.field ===
        Expr::RecordAccess(record, field_name) => {
            // Try fully-constant evaluation first
            if let Ok(value) = preflight_const_i64(&expr.node) {
                return Ok(builder.ins().iconst(types::I64, value));
            }

            // Runtime record path: try to resolve through function application
            compile_record_access_runtime(builder, record, field_name, bindings)
        }

        // === EXCEPT: [f EXCEPT ![a] = b] or [r EXCEPT !.field = v] ===
        Expr::Except(_, _) => {
            let val = preflight_const_value(&expr.node)?;
            match val {
                PreflightValue::Int(n) => Ok(builder.ins().iconst(types::I64, n)),
                PreflightValue::Bool(b) => Ok(builder.ins().iconst(types::I64, i64::from(b))),
                _ => Err(JitError::TypeMismatch {
                    expected: "scalar (integer or boolean)".to_string(),
                    actual: val.ty_name().to_string(),
                }),
            }
        }

        // === Function definition: [x \in S |-> body] ===
        Expr::FuncDef(_, _) => Err(JitError::TypeMismatch {
            expected: "scalar (integer or boolean)".to_string(),
            actual: "function".to_string(),
        }),

        // === Record constructor: [a |-> 1, b |-> 2] ===
        Expr::Record(_) => Err(JitError::TypeMismatch {
            expected: "scalar (integer or boolean)".to_string(),
            actual: "record".to_string(),
        }),

        // === Domain: DOMAIN f ===
        Expr::Domain(_) => Err(JitError::TypeMismatch {
            expected: "scalar (integer or boolean)".to_string(),
            actual: "set".to_string(),
        }),

        // === Set enumeration: {a, b, c} ===
        Expr::SetEnum(_) => Err(JitError::TypeMismatch {
            expected: "scalar (integer or boolean)".to_string(),
            actual: "set".to_string(),
        }),

        // === Integer range: a..b ===
        Expr::Range(_, _) => Err(JitError::TypeMismatch {
            expected: "scalar (integer or boolean)".to_string(),
            actual: "set".to_string(),
        }),

        _ => Err(JitError::UnsupportedExpr(format!(
            "{} expression type not yet supported",
            expr_type_name(&expr.node)
        ))),
    }
}

/// Get a human-readable name for an expression type.
pub(crate) fn expr_type_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Bool(_) => "Bool",
        Expr::Int(_) => "Int",
        Expr::String(_) => "String",
        Expr::Ident(_, _) => "Ident",
        Expr::StateVar(_, _, _) => "StateVar",
        Expr::Apply(_, _) => "Apply",
        Expr::OpRef(_) => "OpRef",
        Expr::ModuleRef(_, _, _) => "ModuleRef",
        Expr::InstanceExpr(_, _) => "InstanceExpr",
        Expr::Lambda(_, _) => "Lambda",
        Expr::And(_, _) => "And",
        Expr::Or(_, _) => "Or",
        Expr::Not(_) => "Not",
        Expr::Implies(_, _) => "Implies",
        Expr::Equiv(_, _) => "Equiv",
        Expr::Forall(_, _) => "Forall",
        Expr::Exists(_, _) => "Exists",
        Expr::Choose(_, _) => "Choose",
        Expr::SetEnum(_) => "SetEnum",
        Expr::SetBuilder(_, _) => "SetBuilder",
        Expr::SetFilter(_, _) => "SetFilter",
        Expr::In(_, _) => "In",
        Expr::NotIn(_, _) => "NotIn",
        Expr::Subseteq(_, _) => "Subseteq",
        Expr::Union(_, _) => "Union",
        Expr::Intersect(_, _) => "Intersect",
        Expr::SetMinus(_, _) => "SetMinus",
        Expr::Powerset(_) => "Powerset",
        Expr::BigUnion(_) => "BigUnion",
        Expr::FuncDef(_, _) => "FuncDef",
        Expr::FuncApply(_, _) => "FuncApply",
        Expr::Domain(_) => "Domain",
        Expr::Except(_, _) => "Except",
        Expr::FuncSet(_, _) => "FuncSet",
        Expr::Record(_) => "Record",
        Expr::RecordAccess(_, _) => "RecordAccess",
        Expr::RecordSet(_) => "RecordSet",
        Expr::Tuple(_) => "Tuple",
        Expr::Times(_) => "Times",
        Expr::Prime(_) => "Prime",
        Expr::Always(_) => "Always",
        Expr::Eventually(_) => "Eventually",
        Expr::LeadsTo(_, _) => "LeadsTo",
        Expr::WeakFair(_, _) => "WeakFair",
        Expr::StrongFair(_, _) => "StrongFair",
        Expr::Enabled(_) => "Enabled",
        Expr::Unchanged(_) => "Unchanged",
        Expr::If(_, _, _) => "If",
        Expr::Case(_, _) => "Case",
        Expr::Let(_, _) => "Let",
        Expr::SubstIn(_, _) => "SubstIn",
        Expr::Eq(_, _) => "Eq",
        Expr::Neq(_, _) => "Neq",
        Expr::Lt(_, _) => "Lt",
        Expr::Leq(_, _) => "Leq",
        Expr::Gt(_, _) => "Gt",
        Expr::Geq(_, _) => "Geq",
        Expr::Add(_, _) => "Add",
        Expr::Sub(_, _) => "Sub",
        Expr::Mul(_, _) => "Mul",
        Expr::Div(_, _) => "Div",
        Expr::IntDiv(_, _) => "IntDiv",
        Expr::Mod(_, _) => "Mod",
        Expr::Pow(_, _) => "Pow",
        Expr::Neg(_) => "Neg",
        Expr::Range(_, _) => "Range",
        Expr::Label(_) => "Label",
    }
}
