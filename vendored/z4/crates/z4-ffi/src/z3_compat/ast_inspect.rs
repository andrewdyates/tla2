// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST inspection (extended), decl_kind mapping, error handling,
//! and AST vector functions.
//!
//! Functions that overlap with `accessors.rs` (Z3_get_ast_kind, Z3_is_app,
//! Z3_get_app_num_args, Z3_get_app_arg, Z3_get_app_decl, Z3_get_decl_name,
//! Z3_get_arity, Z3_get_domain, Z3_get_range, Z3_get_numeral_int) live in
//! `accessors.rs`. This module holds the remaining inspection/utility functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_uint};
use std::ptr;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use super::{
    ast_to_term, cache_ast_vector, cache_string, ffi_guard_ast, ffi_guard_const_ptr, ffi_guard_ptr,
    ffi_guard_uint, ffi_guard_void, lookup_ast_sort, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_func_decl, Z3_EXCEPTION, Z3_INVALID_ARG, Z3_OK, Z3_OP_ABS, Z3_OP_ADD, Z3_OP_AND, Z3_OP_BADD,
    Z3_OP_BAND, Z3_OP_BASHR, Z3_OP_BLSHR, Z3_OP_BMUL, Z3_OP_BNEG, Z3_OP_BNOT, Z3_OP_BOR,
    Z3_OP_BSDIV, Z3_OP_BSHL, Z3_OP_BSMOD, Z3_OP_BSREM, Z3_OP_BSUB, Z3_OP_BUDIV, Z3_OP_BUREM,
    Z3_OP_BXOR, Z3_OP_CONCAT, Z3_OP_CONST_ARRAY, Z3_OP_DISTINCT, Z3_OP_DIV, Z3_OP_EQ,
    Z3_OP_EXTRACT, Z3_OP_FALSE, Z3_OP_GE, Z3_OP_GT, Z3_OP_IDIV, Z3_OP_IFF, Z3_OP_IMPLIES,
    Z3_OP_IS_INT, Z3_OP_ITE, Z3_OP_LE, Z3_OP_LT, Z3_OP_MOD, Z3_OP_MUL, Z3_OP_NOT, Z3_OP_OR,
    Z3_OP_POWER, Z3_OP_SELECT, Z3_OP_SIGN_EXT, Z3_OP_SLEQ, Z3_OP_SLT, Z3_OP_STORE, Z3_OP_SUB,
    Z3_OP_TO_INT, Z3_OP_TO_REAL, Z3_OP_TRUE, Z3_OP_ULEQ, Z3_OP_ULT, Z3_OP_UMINUS,
    Z3_OP_UNINTERPRETED, Z3_OP_XOR, Z3_OP_ZERO_EXT,
};

// ---- AST string conversion ----
// Note: Z3_is_eq_ast, Z3_get_ast_id, Z3_get_ast_hash live in ast_identity.rs.

/// Get the string representation of a numeral AST.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_string(c: Z3_context, a: Z3_ast) -> *const c_char {
    if a == 0 {
        return ptr::null();
    }
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            match ctx.solver.get_numeral_string(ast_to_term(a)) {
                Some(s) => cache_string(ctx, s),
                None => cache_string(ctx, format!("{a}")),
            }
        })
    }
}

/// Get the decimal string representation of a numeral AST.
///
/// For rationals, produces a decimal expansion to `precision` places
/// (e.g., `"0.333333"` for 1/3 with precision 6).
/// For integers and bitvectors, behaves identically to `Z3_get_numeral_string`.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_decimal_string(
    c: Z3_context,
    a: Z3_ast,
    precision: c_uint,
) -> *const c_char {
    if a == 0 {
        return ptr::null();
    }
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            match ctx.solver.get_numeral_string(ast_to_term(a)) {
                Some(s) => {
                    // If it's a rational (contains '/'), convert to decimal via scaled BigInt division
                    if let Some((num_s, den_s)) = s.split_once('/') {
                        if let (Ok(num), Ok(den)) = (
                            num_s.trim().parse::<BigInt>(),
                            den_s.trim().parse::<BigInt>(),
                        ) {
                            if !den.is_zero() {
                                let prec = precision as usize;
                                let scale = BigInt::from(10).pow(prec as u32);
                                let scaled = &num * &scale / &den;
                                let (sign, abs) = if scaled.is_negative() {
                                    ("-", -scaled)
                                } else {
                                    ("", scaled)
                                };
                                let abs_str = abs.to_string();
                                let decimal = if prec == 0 {
                                    format!("{sign}{abs_str}")
                                } else if abs_str.len() <= prec {
                                    let zeros = "0".repeat(prec - abs_str.len());
                                    format!("{sign}0.{zeros}{abs_str}")
                                } else {
                                    let split = abs_str.len() - prec;
                                    format!("{sign}{}.{}", &abs_str[..split], &abs_str[split..])
                                };
                                return cache_string(ctx, decimal);
                            }
                        }
                    }
                    cache_string(ctx, s)
                }
                None => ptr::null(),
            }
        })
    }
}

/// Convert an AST to a string.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_to_string(c: Z3_context, a: Z3_ast) -> *const c_char {
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let sort_str = match lookup_ast_sort(ctx, a) {
                Some(sort) => format!("{sort:?}"),
                None => "?".to_string(),
            };
            cache_string(ctx, format!("(ast {a} : {sort_str})"))
        })
    }
}

// ---- Decl kind ----

/// Map an operator name (from Z4 TermKind) to the Z3 decl_kind constant.
fn operator_name_to_decl_kind(name: &str) -> c_uint {
    match name {
        // Boolean
        "true" => Z3_OP_TRUE,
        "false" => Z3_OP_FALSE,
        "=" => Z3_OP_EQ,
        "distinct" => Z3_OP_DISTINCT,
        "ite" => Z3_OP_ITE,
        "and" => Z3_OP_AND,
        "or" => Z3_OP_OR,
        "iff" | "<=>" => Z3_OP_IFF,
        "xor" => Z3_OP_XOR,
        "not" => Z3_OP_NOT,
        "=>" | "implies" => Z3_OP_IMPLIES,
        // Arithmetic
        "<=" => Z3_OP_LE,
        ">=" => Z3_OP_GE,
        "<" => Z3_OP_LT,
        ">" => Z3_OP_GT,
        "+" => Z3_OP_ADD,
        "-" => Z3_OP_SUB,
        "neg" | "unary_minus" => Z3_OP_UMINUS,
        "*" => Z3_OP_MUL,
        "/" | "div" => Z3_OP_DIV,
        "intdiv" | "ediv" => Z3_OP_IDIV,
        "mod" => Z3_OP_MOD,
        "to_real" => Z3_OP_TO_REAL,
        "to_int" => Z3_OP_TO_INT,
        "is_int" => Z3_OP_IS_INT,
        "^" | "power" => Z3_OP_POWER,
        "abs" => Z3_OP_ABS,
        // Arrays
        "store" => Z3_OP_STORE,
        "select" => Z3_OP_SELECT,
        "const" | "const_array" => Z3_OP_CONST_ARRAY,
        // Bitvectors
        "bvneg" => Z3_OP_BNEG,
        "bvadd" => Z3_OP_BADD,
        "bvsub" => Z3_OP_BSUB,
        "bvmul" => Z3_OP_BMUL,
        "bvsdiv" => Z3_OP_BSDIV,
        "bvudiv" => Z3_OP_BUDIV,
        "bvsrem" => Z3_OP_BSREM,
        "bvurem" => Z3_OP_BUREM,
        "bvsmod" => Z3_OP_BSMOD,
        "bvand" => Z3_OP_BAND,
        "bvor" => Z3_OP_BOR,
        "bvnot" => Z3_OP_BNOT,
        "bvxor" => Z3_OP_BXOR,
        "concat" => Z3_OP_CONCAT,
        "sign_extend" => Z3_OP_SIGN_EXT,
        "zero_extend" => Z3_OP_ZERO_EXT,
        "extract" => Z3_OP_EXTRACT,
        "bvshl" => Z3_OP_BSHL,
        "bvlshr" => Z3_OP_BLSHR,
        "bvashr" => Z3_OP_BASHR,
        "bvsle" => Z3_OP_SLEQ,
        "bvslt" => Z3_OP_SLT,
        "bvule" => Z3_OP_ULEQ,
        "bvult" => Z3_OP_ULT,
        // Default: uninterpreted function
        _ => Z3_OP_UNINTERPRETED,
    }
}

/// Return the declaration kind corresponding to a function declaration.
///
/// Maps the operator name stored in the func_decl to the Z3 `Z3_decl_kind`
/// enum value. Unrecognized operators return `Z3_OP_UNINTERPRETED`.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_kind(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return Z3_OP_UNINTERPRETED;
    }
    unsafe {
        ffi_guard_uint(_c, Z3_OP_UNINTERPRETED, |_ctx| {
            let decl = &(*d).decl;
            operator_name_to_decl_kind(decl.name())
        })
    }
}

// ---- Error handling ----

/// Get the error code from the last operation.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_error_code(c: Z3_context) -> c_uint {
    unsafe { ffi_guard_uint(c, Z3_INVALID_ARG, |ctx| ctx.last_error) }
}

/// Get the error message for a given error code.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_error_msg(c: Z3_context, err: c_uint) -> *const c_char {
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let msg = match err {
                Z3_OK => "ok".to_string(),
                Z3_EXCEPTION => ctx
                    .error_msg
                    .clone()
                    .unwrap_or_else(|| "exception".to_string()),
                _ => format!("error code {err}"),
            };
            cache_string(ctx, msg)
        })
    }
}

/// Set an error handler (currently a no-op).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_set_error_handler(
    _c: Z3_context,
    _h: Option<unsafe extern "C" fn(Z3_context, c_uint)>,
) {
}

// ---- AST vectors ----

/// Create an empty AST vector.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ast_vector(c: Z3_context) -> Z3_ast_vector {
    unsafe { ffi_guard_ptr(c, |ctx| cache_ast_vector(ctx, Vec::new())) }
}

/// Increment AST vector reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_inc_ref(_c: Z3_context, _v: Z3_ast_vector) {}

/// Decrement AST vector reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_dec_ref(_c: Z3_context, _v: Z3_ast_vector) {}

/// Get AST vector size.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_size(_c: Z3_context, v: Z3_ast_vector) -> c_uint {
    if v.is_null() {
        return 0;
    }
    unsafe { ffi_guard_uint(_c, 0, |_ctx| (*v).asts.len() as c_uint) }
}

/// Get an element from an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_get(_c: Z3_context, v: Z3_ast_vector, i: c_uint) -> Z3_ast {
    if v.is_null() {
        return 0;
    }
    unsafe {
        ffi_guard_ast(_c, |_ctx| {
            let vec = &(*v).asts;
            match vec.get(i as usize) {
                Some(&ast) => ast,
                None => 0,
            }
        })
    }
}

/// Push an element to an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_push(_c: Z3_context, v: Z3_ast_vector, a: Z3_ast) {
    if v.is_null() {
        return;
    }
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            (*v).asts.push(a);
        });
    }
}

/// Set an element in an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_set(_c: Z3_context, v: Z3_ast_vector, i: c_uint, a: Z3_ast) {
    if v.is_null() {
        return;
    }
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let vec = &mut (*v).asts;
            if (i as usize) < vec.len() {
                vec[i as usize] = a;
            }
        });
    }
}

/// Resize an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_resize(_c: Z3_context, v: Z3_ast_vector, n: c_uint) {
    if v.is_null() {
        return;
    }
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            (*v).asts.resize(n as usize, 0);
        });
    }
}
