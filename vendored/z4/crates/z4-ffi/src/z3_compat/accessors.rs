// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST and FuncDecl accessor functions.
//!
//! Implements the subset of z3_api.h "Accessors" section needed for
//! external consumers: AST kind queries, app introspection, func_decl
//! introspection, and boolean value retrieval.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_int, c_uint};
use std::ptr;

use z4_dpll::api::TermKind;

use super::{
    alloc_sort, ast_to_term, cache_func_decl_with_params, cache_symbol, ffi_guard_ast,
    ffi_guard_int, ffi_guard_ptr, ffi_guard_uint, parse_indexed_name, term_to_ast, Z3_ast,
    Z3_context, Z3_func_decl, Z3_sort, Z3_symbol, Z3_APP_AST, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF,
    Z3_NUMERAL_AST, Z3_QUANTIFIER_AST, Z3_UNKNOWN_AST, Z3_VAR_AST,
};

// ============================================================================
// AST kind and classification
// ============================================================================

/// Get the kind of an AST node.
///
/// Returns one of `Z3_NUMERAL_AST`, `Z3_APP_AST`, `Z3_VAR_AST`,
/// `Z3_QUANTIFIER_AST`, or `Z3_UNKNOWN_AST`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_ast_kind(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return Z3_UNKNOWN_AST;
    }
    unsafe {
        ffi_guard_uint(c, Z3_UNKNOWN_AST, |ctx| {
            match ctx.solver.term_kind(ast_to_term(a)) {
                TermKind::Const => Z3_NUMERAL_AST,
                TermKind::App { .. } | TermKind::Not | TermKind::Ite => Z3_APP_AST,
                TermKind::Var { .. } => Z3_VAR_AST,
                TermKind::Forall | TermKind::Exists => Z3_QUANTIFIER_AST,
                TermKind::Let | _ => Z3_UNKNOWN_AST,
            }
        })
    }
}

/// Return true if the AST is a numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_numeral_ast(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    unsafe { ffi_guard_int(c, 0, |ctx| i32::from(ctx.solver.is_numeral(ast_to_term(a)))) != 0 }
}

/// Return true if the AST is an application node.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_app(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    unsafe { ffi_guard_int(c, 0, |ctx| i32::from(ctx.solver.is_app(ast_to_term(a)))) != 0 }
}

/// Convert an AST to an application node.
///
/// In Z3, `Z3_app` is a typedef for `Z3_ast`. This function is a type-checked
/// identity cast: returns the AST unchanged if it represents an application,
/// or 0 (null) if it does not.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_to_app(c: Z3_context, a: Z3_ast) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if ctx.solver.is_app(ast_to_term(a)) {
                a
            } else if ctx.solver.is_numeral(ast_to_term(a)) {
                // Z3 also returns the AST for numerals (they are 0-arity applications)
                a
            } else {
                0
            }
        })
    }
}

// ============================================================================
// Application introspection
// ============================================================================

/// Get the number of arguments of an application AST.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_num_args(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.solver.app_num_args(ast_to_term(a)) as c_uint
        })
    }
}

/// Get the i-th argument of an application AST.
///
/// Returns 0 (null AST) if `a` is not an application or `i` is out of bounds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_arg(c: Z3_context, a: Z3_ast, i: c_uint) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    unsafe {
        ffi_guard_ast(c, |ctx| {
            match ctx.solver.app_arg(ast_to_term(a), i as usize) {
                Some(t) => term_to_ast(t),
                None => 0,
            }
        })
    }
}

/// Get the function declaration of an application AST.
///
/// For built-in operators (and, or, not, +, -, etc.) this returns a synthetic
/// func_decl with the operator name.
///
/// Returns null if `a` is not an application.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_decl(c: Z3_context, a: Z3_ast) -> Z3_func_decl {
    if a == 0 {
        return ptr::null_mut();
    }
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let term = ast_to_term(a);
            let name = match ctx.solver.app_symbol_name(term) {
                Some(n) => n,
                None => return ptr::null_mut(),
            };
            let num_args = ctx.solver.app_num_args(term);
            // Parse indexed operator name and extract parameters (#6580 F2).
            let (base_name, params) = parse_indexed_name(&name);
            // Reconstruct real domain sorts from the application's children (#6580 F3).
            // Falls back to null if any child lookup fails.
            let domain: Option<Vec<_>> = (0..num_args)
                .map(|i| {
                    ctx.solver
                        .app_arg(term, i)
                        .map(|arg| ctx.solver.term_sort(arg))
                })
                .collect();
            let domain = match domain {
                Some(d) => d,
                None => return ptr::null_mut(),
            };
            let range = ctx.solver.term_sort(term);
            cache_func_decl_with_params(
                ctx,
                z4_dpll::api::FuncDecl::new(base_name, domain, range),
                params,
            )
        })
    }
}

// ============================================================================
// FuncDecl introspection
// ============================================================================

/// Get the name of a function declaration as a symbol.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_name(c: Z3_context, d: Z3_func_decl) -> Z3_symbol {
    if d.is_null() {
        return ptr::null_mut();
    }
    let decl = unsafe { &(*d).decl };
    let name = decl.name().to_string();
    unsafe { ffi_guard_ptr(c, |ctx| cache_symbol(ctx, name.clone())) }
}

/// Get the number of arguments (arity) of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_arity(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| {
            let decl = &(*d).decl;
            decl.arity() as c_uint
        })
    }
}

/// Get the number of parameters in a function declaration (always 0 for Z4).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_domain_size(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| {
            let decl = &(*d).decl;
            decl.arity() as c_uint
        })
    }
}

/// Get the i-th domain sort of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_domain(c: Z3_context, d: Z3_func_decl, i: c_uint) -> Z3_sort {
    if d.is_null() {
        return ptr::null_mut();
    }
    let decl = unsafe { &(*d).decl };
    let sort = match decl.domain().get(i as usize) {
        Some(s) => s.clone(),
        None => return ptr::null_mut(),
    };
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

/// Get the range (return) sort of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_range(c: Z3_context, d: Z3_func_decl) -> Z3_sort {
    if d.is_null() {
        return ptr::null_mut();
    }
    let decl = unsafe { &(*d).decl };
    let sort = decl.range().clone();
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

// ============================================================================
// Boolean value
// ============================================================================

/// Get the boolean value of a constant AST.
///
/// Returns `Z3_L_TRUE`, `Z3_L_FALSE`, or `Z3_L_UNDEF` if not a boolean constant.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_bool_value(c: Z3_context, a: Z3_ast) -> c_int {
    if a == 0 {
        return Z3_L_UNDEF;
    }
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            match ctx.solver.get_bool_value(ast_to_term(a)) {
                Some(true) => Z3_L_TRUE,
                Some(false) => Z3_L_FALSE,
                None => Z3_L_UNDEF,
            }
        })
    }
}

// ============================================================================
// Numeral extraction
// ============================================================================

/// Try to extract an i32 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_int(c: Z3_context, a: Z3_ast, v: *mut c_int) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            if let Some(s) = ctx.solver.get_numeral_string(ast_to_term(a)) {
                if let Ok(val) = s.parse::<c_int>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract a u32 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_uint(c: Z3_context, a: Z3_ast, v: *mut c_uint) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            if let Some(s) = ctx.solver.get_numeral_string(ast_to_term(a)) {
                if let Ok(val) = s.parse::<c_uint>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract an i64 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_int64(c: Z3_context, a: Z3_ast, v: *mut i64) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            if let Some(s) = ctx.solver.get_numeral_string(ast_to_term(a)) {
                if let Ok(val) = s.parse::<i64>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract a u64 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_uint64(c: Z3_context, a: Z3_ast, v: *mut u64) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            if let Some(s) = ctx.solver.get_numeral_string(ast_to_term(a)) {
                if let Ok(val) = s.parse::<u64>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

// ============================================================================
// Function declaration parameter introspection
// ============================================================================

/// Get the number of parameters associated with a function declaration.
///
/// For indexed operators like `(_ extract 7 4)`, returns the number of
/// integer parameters (2 in that case). For non-indexed operators, returns 0.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_num_parameters(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    unsafe { (*d).params.len() as c_uint }
}

/// Get an integer parameter from a function declaration.
///
/// For indexed operators, returns the parameter at `idx`. For example,
/// `(_ extract 7 4)` has parameter 0 = 7 and parameter 1 = 4.
/// Returns 0 if `idx` is out of bounds or the decl has no parameters.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_int_parameter(
    _c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> c_int {
    if d.is_null() {
        return 0;
    }
    unsafe {
        let params = &(*d).params;
        params.get(idx as usize).copied().unwrap_or(0)
    }
}
