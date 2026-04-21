// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible model and params functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_double, c_uint};
use std::ptr;

use num_traits::Signed;
use z4_dpll::api::{ModelValue, Sort};

use super::{
    ast_to_term, cache_func_decl, cache_string, ffi_guard_ast, ffi_guard_const_ptr, ffi_guard_int,
    ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, record_ast_sort, term_to_ast, ParamsHandle,
    Z3_ast, Z3_context, Z3_func_decl, Z3_model, Z3_params, Z3_symbol,
};

// ---- Model operations ----

/// Increment model reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_inc_ref(_c: Z3_context, _m: Z3_model) {}

/// Decrement model reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_dec_ref(_c: Z3_context, _m: Z3_model) {}

/// Get number of constant declarations in model.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_num_consts(_c: Z3_context, m: Z3_model) -> c_uint {
    if m.is_null() {
        return 0;
    }
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| {
            let model = &(*m).model;
            model.len() as c_uint
        })
    }
}

/// Convert model to string.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_to_string(c: Z3_context, m: Z3_model) -> *const c_char {
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if m.is_null() {
                return cache_string(ctx, "(model)".to_string());
            }
            let model = &(*m).model;
            let mut parts = Vec::new();
            for (name, val) in model.iter_bools() {
                parts.push(format!("(define-fun {name} () Bool {val})"));
            }
            for (name, val) in model.iter_ints() {
                if val.is_negative() {
                    let abs = val.abs();
                    parts.push(format!("(define-fun {name} () Int (- {abs}))"));
                } else {
                    parts.push(format!("(define-fun {name} () Int {val})"));
                }
            }
            for (name, val) in model.iter_reals() {
                if val.is_integer() {
                    let n = val.numer();
                    if n.is_negative() {
                        parts.push(format!("(define-fun {name} () Real (- {}))", n.abs()));
                    } else {
                        parts.push(format!("(define-fun {name} () Real {n}.0)"));
                    }
                } else {
                    let n = val.numer();
                    let d = val.denom();
                    if n.is_negative() {
                        parts.push(format!(
                            "(define-fun {name} () Real (- (/ {} {d})))",
                            n.abs()
                        ));
                    } else {
                        parts.push(format!("(define-fun {name} () Real (/ {n} {d}))"));
                    }
                }
            }
            for (name, (val, width)) in model.iter_bvs() {
                let hex_str = format!("{val:x}");
                let hex_width = (*width as usize).div_ceil(4);
                let padded = format!("{hex_str:0>hex_width$}");
                parts.push(format!(
                    "(define-fun {name} () (_ BitVec {width}) #x{padded})"
                ));
            }
            for (name, val) in model.iter_strings() {
                // Escape special characters for SMT-LIB string literal
                let escaped = val.replace('\\', "\\\\").replace('"', "\\\"");
                parts.push(format!("(define-fun {name} () String \"{escaped}\")"));
            }
            for (name, val) in model.iter_fps() {
                parts.push(format!("(define-fun {name} () FloatingPoint {val})"));
            }
            for (name, val) in model.iter_seqs() {
                parts.push(format!("(define-fun {name} () Seq {val})"));
            }
            let output = parts.join("\n");
            cache_string(ctx, output)
        })
    }
}

/// Evaluate a term in the model.
///
/// Sets `*v` to the evaluated value (as an AST) and returns true on success.
/// `model_completion` controls whether to assign default values for unassigned vars.
///
/// Per the Z3 API contract, evaluation uses the model snapshot `m`, not the solver's
/// current state. For variable terms, we look up the value by name in the stored model.
/// For compound expressions or if the model lookup fails, we fall back to
/// `solver.value()` (which requires the solver to still be in SAT state).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_eval(
    c: Z3_context,
    m: Z3_model,
    t: Z3_ast,
    _model_completion: bool,
    v: *mut Z3_ast,
) -> bool {
    if t == 0 || v.is_null() {
        return false;
    }
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = ast_to_term(t);

            // Try model-based lookup first: get the variable name and look it up in the model.
            let val = if !m.is_null() {
                let model = &(*m).model;
                ctx.solver
                    .get_var_name(term)
                    .and_then(|name| model.value_by_name(&name))
            } else {
                None
            };

            // Fall back to solver.value() for compound expressions or if model lookup failed.
            let val = match val {
                Some(v) => v,
                None => match ctx.solver.value(term) {
                    Some(v) => v,
                    None => return 0,
                },
            };

            // Convert the ModelValue back to a term AST
            let result_term = match &val {
                ModelValue::Bool(b) => ctx.solver.bool_const(*b),
                ModelValue::Int(n) => ctx.solver.int_const_bigint(n),
                ModelValue::Real(r) => ctx.solver.rational_const_bigint(r.numer(), r.denom()),
                ModelValue::BitVec { value, width } => ctx.solver.bv_const_bigint(value, *width),
                ModelValue::String(s) => ctx.solver.string_const(s),
                ModelValue::FloatingPoint {
                    sign,
                    exponent,
                    significand,
                    eb,
                    sb,
                } => {
                    let sign_bv = ctx.solver.bv_const(i64::from(*sign), 1);
                    let exp_bv = ctx.solver.bv_const(*exponent as i64, *eb);
                    let sig_bv = ctx.solver.bv_const(*significand as i64, *sb - 1);
                    ctx.solver.fp_from_bvs(sign_bv, exp_bv, sig_bv, *eb, *sb)
                }
                ModelValue::FloatingPointSpecial { kind, eb, sb } => {
                    use z4_dpll::api::FpSpecialKind;
                    match kind {
                        FpSpecialKind::PosZero => ctx.solver.fp_plus_zero(*eb, *sb),
                        FpSpecialKind::NegZero => ctx.solver.fp_minus_zero(*eb, *sb),
                        FpSpecialKind::PosInf => ctx.solver.fp_plus_infinity(*eb, *sb),
                        FpSpecialKind::NegInf => ctx.solver.fp_minus_infinity(*eb, *sb),
                        FpSpecialKind::NaN => ctx.solver.fp_nan(*eb, *sb),
                        _ => return 0,
                    }
                }
                _ => return 0, // Seq, Array, Uninterpreted, Datatype, Unknown
            };
            let result_ast = term_to_ast(result_term);
            // Record sort for the result
            let sort = match &val {
                ModelValue::Bool(_) => Sort::Bool,
                ModelValue::Int(_) => Sort::Int,
                ModelValue::Real(_) => Sort::Real,
                ModelValue::BitVec { width, .. } => Sort::bitvec(*width),
                ModelValue::String(_) => Sort::String,
                ModelValue::FloatingPoint { eb, sb, .. }
                | ModelValue::FloatingPointSpecial { eb, sb, .. } => Sort::FloatingPoint(*eb, *sb),
                _ => Sort::Bool, // unreachable due to early return above
            };
            record_ast_sort(ctx, result_ast, sort);
            *v = result_ast;
            1
        }) != 0
    }
}

/// Get the i-th constant declaration from the model.
///
/// The order is: booleans, integers, reals, bitvectors, strings, floats, sequences.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_const_decl(
    c: Z3_context,
    m: Z3_model,
    i: c_uint,
) -> Z3_func_decl {
    if m.is_null() {
        return ptr::null_mut();
    }
    // All model dereferences must be inside the ffi_guard closure so that any
    // panic during model iteration is caught by catch_unwind instead of
    // propagating across the extern "C" boundary (UB).
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let model = &(*m).model;
            let idx = i as usize;

            // Collect names and sorts in a stable order: bools, ints, reals, bvs
            let mut entries: Vec<(String, Sort)> = Vec::new();
            for (name, _) in model.iter_bools() {
                entries.push((name.to_string(), Sort::Bool));
            }
            for (name, _) in model.iter_ints() {
                entries.push((name.to_string(), Sort::Int));
            }
            for (name, _) in model.iter_reals() {
                entries.push((name.to_string(), Sort::Real));
            }
            for (name, (_, width)) in model.iter_bvs() {
                entries.push((name.to_string(), Sort::bitvec(*width)));
            }
            for (name, _) in model.iter_strings() {
                entries.push((name.to_string(), Sort::String));
            }
            for (name, val) in model.iter_fps() {
                if let ModelValue::FloatingPoint { eb, sb, .. }
                | ModelValue::FloatingPointSpecial { eb, sb, .. } = val
                {
                    entries.push((name.to_string(), Sort::FloatingPoint(*eb, *sb)));
                }
            }
            for (name, _) in model.iter_seqs() {
                // Seq element sort is unknown from Model struct; use Seq(Int) as fallback.
                entries.push((name.to_string(), Sort::seq(Sort::Int)));
            }

            match entries.get(idx) {
                Some((name, sort)) => {
                    let decl = z4_dpll::api::FuncDecl::new(name.clone(), vec![], sort.clone());
                    cache_func_decl(ctx, decl)
                }
                None => ptr::null_mut(),
            }
        })
    }
}

/// Get the interpretation of a constant in the model.
///
/// Given a func_decl (obtained from `Z3_model_get_const_decl`), returns
/// the value assigned to that constant in the model.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_const_interp(
    c: Z3_context,
    m: Z3_model,
    d: Z3_func_decl,
) -> Z3_ast {
    if m.is_null() || d.is_null() {
        return 0;
    }
    // All model/decl dereferences must be inside the ffi_guard closure so that
    // any panic is caught by catch_unwind instead of propagating across the
    // extern "C" boundary (UB).
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let model = &(*m).model;
            let decl = &(*d).decl;
            let name = decl.name().to_string();

            if let Some(val) = model.bool_val(&name) {
                let t = ctx.solver.bool_const(val);
                let a = term_to_ast(t);
                record_ast_sort(ctx, a, Sort::Bool);
                return a;
            }
            if let Some(val) = model.int_val(&name) {
                let t = ctx.solver.int_const_bigint(val);
                let a = term_to_ast(t);
                record_ast_sort(ctx, a, Sort::Int);
                return a;
            }
            if let Some(val) = model.real_val(&name) {
                let t = ctx.solver.rational_const_bigint(val.numer(), val.denom());
                let a = term_to_ast(t);
                record_ast_sort(ctx, a, Sort::Real);
                return a;
            }
            if let Some((val, width)) = model.bv_val(&name) {
                let t = ctx.solver.bv_const_bigint(&val, width);
                let a = term_to_ast(t);
                record_ast_sort(ctx, a, Sort::bitvec(width));
                return a;
            }
            if let Some(val) = model.string_val(&name) {
                let t = ctx.solver.string_const(val);
                let a = term_to_ast(t);
                record_ast_sort(ctx, a, Sort::String);
                return a;
            }
            if let Some(val) = model.fp_val(&name) {
                use z4_dpll::api::FpSpecialKind;
                match val {
                    ModelValue::FloatingPoint {
                        sign,
                        exponent,
                        significand,
                        eb,
                        sb,
                    } => {
                        let sign_bv = ctx.solver.bv_const(i64::from(*sign), 1);
                        let exp_bv = ctx.solver.bv_const(*exponent as i64, *eb);
                        let sig_bv = ctx.solver.bv_const(*significand as i64, *sb - 1);
                        let t = ctx.solver.fp_from_bvs(sign_bv, exp_bv, sig_bv, *eb, *sb);
                        let a = term_to_ast(t);
                        record_ast_sort(ctx, a, Sort::FloatingPoint(*eb, *sb));
                        return a;
                    }
                    ModelValue::FloatingPointSpecial { kind, eb, sb } => {
                        let t = match kind {
                            FpSpecialKind::PosZero => ctx.solver.fp_plus_zero(*eb, *sb),
                            FpSpecialKind::NegZero => ctx.solver.fp_minus_zero(*eb, *sb),
                            FpSpecialKind::PosInf => ctx.solver.fp_plus_infinity(*eb, *sb),
                            FpSpecialKind::NegInf => ctx.solver.fp_minus_infinity(*eb, *sb),
                            FpSpecialKind::NaN => ctx.solver.fp_nan(*eb, *sb),
                            _ => return 0,
                        };
                        let a = term_to_ast(t);
                        record_ast_sort(ctx, a, Sort::FloatingPoint(*eb, *sb));
                        return a;
                    }
                    _ => {}
                }
            }
            // Seq and Array values: no direct term constructor available.
            // Return 0 (not found) for now — consumers should use Z3_model_to_string.
            0 // Not found
        })
    }
}

/// Get the number of function interpretations in the model.
///
/// Z4's Model struct only stores constant (0-arity) values, so this always returns 0.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_num_funcs(_c: Z3_context, _m: Z3_model) -> c_uint {
    0
}

/// Check whether the model has an interpretation for a given func_decl.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_has_interp(_c: Z3_context, m: Z3_model, d: Z3_func_decl) -> bool {
    if m.is_null() || d.is_null() {
        return false;
    }
    unsafe {
        ffi_guard_int(_c, 0, |_ctx| {
            let model = &(*m).model;
            let decl = &(*d).decl;
            let name = decl.name();
            i32::from(
                model.bool_val(name).is_some()
                    || model.int_val(name).is_some()
                    || model.real_val(name).is_some()
                    || model.bv_val(name).is_some()
                    || model.string_val(name).is_some()
                    || model.fp_val(name).is_some()
                    || model.seq_val(name).is_some(),
            )
        }) != 0
    }
}

// ---- Params ----

/// Create a params object stored until `Z3_solver_set_params` applies it.
///
/// Z4 currently honors only the `timeout` parameter, expressed in milliseconds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_params(c: Z3_context) -> Z3_params {
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let handle = Box::into_raw(Box::new(ParamsHandle { params: Vec::new() }));
            ctx.params_cache.push(handle);
            handle
        })
    }
}

/// Increment params reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_inc_ref(_c: Z3_context, _p: Z3_params) {}

/// Decrement params reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_dec_ref(_c: Z3_context, _p: Z3_params) {}

/// Set a boolean parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_bool(_c: Z3_context, p: Z3_params, k: Z3_symbol, v: bool) {
    if p.is_null() || k.is_null() {
        return;
    }
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = &(*k).name;
            params.push((key.clone(), v.to_string()));
        });
    }
}

/// Set an unsigned int parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_uint(_c: Z3_context, p: Z3_params, k: Z3_symbol, v: c_uint) {
    if p.is_null() || k.is_null() {
        return;
    }
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = &(*k).name;
            params.push((key.clone(), v.to_string()));
        });
    }
}

/// Set a double parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_double(
    _c: Z3_context,
    p: Z3_params,
    k: Z3_symbol,
    v: c_double,
) {
    if p.is_null() || k.is_null() {
        return;
    }
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = &(*k).name;
            params.push((key.clone(), v.to_string()));
        });
    }
}

/// Set a symbol parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_symbol(
    _c: Z3_context,
    p: Z3_params,
    k: Z3_symbol,
    v: Z3_symbol,
) {
    if p.is_null() || k.is_null() || v.is_null() {
        return;
    }
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = &(*k).name;
            let val = &(*v).name;
            params.push((key.clone(), val.clone()));
        });
    }
}
