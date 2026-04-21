// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible term construction: function decls and boolean operations.
//! Numeral constructors are in `numerals.rs`.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_uint, CStr};
use std::ptr;

use z4_dpll::api::Sort;

use super::{
    ast_to_term, cache_func_decl, ffi_guard_ast, ffi_guard_ptr, lookup_ast_sort, record_ast_sort,
    term_to_ast, Z3_ast, Z3_context, Z3_func_decl, Z3_sort, Z3_symbol, Z3_SORT_ERROR,
};

// ---- Function declarations and constants ----

/// Declare an uninterpreted function.
///
/// # Safety
/// All pointers must be valid. `domain` must point to `domain_size` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_func_decl(
    c: Z3_context,
    s: Z3_symbol,
    domain_size: c_uint,
    domain: *const Z3_sort,
    range: Z3_sort,
) -> Z3_func_decl {
    if s.is_null() || range.is_null() {
        return ptr::null_mut();
    }
    if domain_size > 0 && domain.is_null() {
        return ptr::null_mut();
    }

    // Pre-extract data from raw pointers before entering the guard
    let name = unsafe { (*s).name.clone() };
    let mut dom_sorts = Vec::with_capacity(domain_size as usize);
    for i in 0..domain_size as usize {
        let sort_ptr = unsafe { *domain.add(i) };
        if sort_ptr.is_null() {
            return ptr::null_mut();
        }
        dom_sorts.push(unsafe { (*sort_ptr).sort.clone() });
    }
    let range_sort = unsafe { (*range).sort.clone() };

    unsafe {
        ffi_guard_ptr(c, |ctx| {
            match ctx.solver.try_declare_fun(&name, &dom_sorts, range_sort) {
                Ok(decl) => cache_func_decl(ctx, decl),
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("{e}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Create a constant (0-arity function application).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_const(c: Z3_context, s: Z3_symbol, ty: Z3_sort) -> Z3_ast {
    if s.is_null() || ty.is_null() {
        return 0;
    }
    let name = unsafe { (*s).name.clone() };
    let sort = unsafe { (*ty).sort.clone() };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = ctx.solver.declare_const(&name, sort.clone());
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort);
            ast
        })
    }
}

/// Create a fresh constant with a unique name.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fresh_const(
    c: Z3_context,
    prefix: *const c_char,
    ty: Z3_sort,
) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    let pfx = if prefix.is_null() {
        "fresh".to_string()
    } else {
        unsafe { CStr::from_ptr(prefix) }
            .to_str()
            .unwrap_or("fresh")
            .to_string()
    };
    let sort = unsafe { (*ty).sort.clone() };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = ctx
                .solver
                .declare_const(&format!("{pfx}!{}", ctx.ast_sorts.len()), sort.clone());
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort);
            ast
        })
    }
}

/// Apply a function declaration to arguments.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_app(
    c: Z3_context,
    d: Z3_func_decl,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    if d.is_null() {
        return 0;
    }
    if num_args > 0 && args.is_null() {
        return 0;
    }

    // Pre-extract data from raw pointers
    let decl = unsafe { (*d).decl.clone() };
    let term_args: Vec<_> = (0..num_args as usize)
        .map(|i| ast_to_term(unsafe { *args.add(i) }))
        .collect();

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let result = ctx.solver.apply(&decl, &term_args);
            let ast = term_to_ast(result);
            record_ast_sort(ctx, ast, decl.range().clone());
            ast
        })
    }
}

// ---- Boolean operations ----

/// Create the `true` constant.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_true(c: Z3_context) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.bool_const(true);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create the `false` constant.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_false(c: Z3_context) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.bool_const(false);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create an equality.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_eq(c: Z3_context, l: Z3_ast, r: Z3_ast) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.eq(ast_to_term(l), ast_to_term(r));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create a distinct constraint.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_distinct(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    if num_args == 0 || args.is_null() {
        return 0;
    }
    let terms: Vec<_> = (0..num_args as usize)
        .map(|i| ast_to_term(unsafe { *args.add(i) }))
        .collect();

    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.distinct(&terms);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean NOT.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_not(c: Z3_context, a: Z3_ast) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.not(ast_to_term(a));
            let r = term_to_ast(t);
            record_ast_sort(ctx, r, Sort::Bool);
            r
        })
    }
}

/// Create if-then-else.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ite(c: Z3_context, t1: Z3_ast, t2: Z3_ast, t3: Z3_ast) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx
                .solver
                .ite(ast_to_term(t1), ast_to_term(t2), ast_to_term(t3));
            let r = term_to_ast(t);
            if let Some(sort) = lookup_ast_sort(ctx, t2).cloned() {
                record_ast_sort(ctx, r, sort);
            }
            r
        })
    }
}

/// Create boolean iff.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_iff(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.eq(ast_to_term(t1), ast_to_term(t2));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean implication.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_implies(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.implies(ast_to_term(t1), ast_to_term(t2));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean XOR.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_xor(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.xor(ast_to_term(t1), ast_to_term(t2));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean AND.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_and(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    let terms: Vec<_> = if num_args == 0 || args.is_null() {
        Vec::new()
    } else {
        (0..num_args as usize)
            .map(|i| ast_to_term(unsafe { *args.add(i) }))
            .collect()
    };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            if terms.is_empty() {
                let t = ctx.solver.bool_const(true);
                return term_to_ast(t);
            }
            let t = ctx.solver.and_many(&terms);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean OR.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_or(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    let terms: Vec<_> = if num_args == 0 || args.is_null() {
        Vec::new()
    } else {
        (0..num_args as usize)
            .map(|i| ast_to_term(unsafe { *args.add(i) }))
            .collect()
    };

    unsafe {
        ffi_guard_ast(c, |ctx| {
            if terms.is_empty() {
                let t = ctx.solver.bool_const(false);
                return term_to_ast(t);
            }
            let t = ctx.solver.or_many(&terms);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

// ---- Simplification ----

/// Simplify an AST (identity in Z4 — the solver simplifies internally).
///
/// Z4 performs simplification eagerly during term construction,
/// so this returns the term unchanged.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplify(_c: Z3_context, a: Z3_ast) -> Z3_ast {
    a
}
