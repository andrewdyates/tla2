// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible numeral construction functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint, CStr};

use num_bigint::BigInt;
use z4_dpll::api::Sort;

use super::{ffi_guard_ast, record_ast_sort, term_to_ast, Z3_ast, Z3_context, Z3_sort};

// ---- Numerals ----

/// Create a numeral from a string.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_numeral(
    c: Z3_context,
    numeral: *const c_char,
    ty: Z3_sort,
) -> Z3_ast {
    if numeral.is_null() || ty.is_null() {
        return 0;
    }
    let num_str = match unsafe { CStr::from_ptr(numeral).to_str() } {
        Ok(s) => s.to_string(),
        Err(_) => return 0,
    };
    let sort = unsafe { (*ty).sort.clone() };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => match num_str.parse::<BigInt>() {
                    Ok(v) => ctx.solver.int_const_bigint(&v),
                    Err(_) => return 0,
                },
                Sort::Real => {
                    if let Some((n, d)) = num_str.split_once('/') {
                        if let (Ok(numer), Ok(denom)) =
                            (n.trim().parse::<BigInt>(), d.trim().parse::<BigInt>())
                        {
                            ctx.solver.rational_const_bigint(&numer, &denom)
                        } else {
                            return 0;
                        }
                    } else if let Ok(v) = num_str.parse::<BigInt>() {
                        // Integer literal used as Real — construct as n/1
                        ctx.solver.rational_const_bigint(&v, &BigInt::from(1))
                    } else {
                        return 0;
                    }
                }
                Sort::BitVec(bvs) => match num_str.parse::<BigInt>() {
                    Ok(v) => ctx.solver.bv_const_bigint(&v, bvs.width),
                    Err(_) => return 0,
                },
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
        })
    }
}

/// Create an integer numeral.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int(c: Z3_context, v: c_int, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    let sort = unsafe { (*ty).sort.clone() };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(i64::from(v)),
                Sort::Real => ctx.solver.real_const(f64::from(v)),
                Sort::BitVec(bvs) => ctx.solver.bv_const(i64::from(v), bvs.width),
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
        })
    }
}

/// Create an unsigned integer numeral.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_unsigned_int(c: Z3_context, v: c_uint, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    let sort = unsafe { (*ty).sort.clone() };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(i64::from(v)),
                Sort::Real => ctx.solver.real_const(f64::from(v)),
                Sort::BitVec(bvs) => ctx.solver.bv_const(i64::from(v), bvs.width),
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
        })
    }
}

/// Create a numeral from a 64-bit signed integer.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int64(c: Z3_context, v: i64, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    let sort = unsafe { (*ty).sort.clone() };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(v),
                Sort::Real => {
                    let big_v = BigInt::from(v);
                    ctx.solver.rational_const_bigint(&big_v, &BigInt::from(1))
                }
                Sort::BitVec(bvs) => ctx.solver.bv_const(v, bvs.width),
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
        })
    }
}

/// Create a numeral from a 64-bit unsigned integer.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_unsigned_int64(c: Z3_context, v: u64, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    let sort = unsafe { (*ty).sort.clone() };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let big_v = BigInt::from(v);
            let term = match &sort {
                Sort::Int => ctx.solver.int_const_bigint(&big_v),
                Sort::Real => ctx.solver.rational_const_bigint(&big_v, &BigInt::from(1)),
                Sort::BitVec(bvs) => ctx.solver.bv_const_bigint(&big_v, bvs.width),
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
        })
    }
}

/// Create a real numeral from numerator/denominator.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real(c: Z3_context, num: c_int, den: c_int) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = ctx.solver.rational_const(i64::from(num), i64::from(den));
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, Sort::Real);
            ast
        })
    }
}
