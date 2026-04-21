// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST identity, comparison, symbol, and sort introspection.
//!
//! Split from accessors.rs for file size compliance. Implements Z3 API
//! functions for AST equality, hashing, FuncDecl comparison/stringification,
//! symbol kind inspection, and sort identity/naming.

use std::ffi::{c_char, c_int, c_uint};
use std::ptr;

use super::{
    cache_string, cache_symbol, ffi_guard_const_ptr, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint,
    Z3_ast, Z3_context, Z3_func_decl, Z3_sort, Z3_symbol,
};

// ============================================================================
// AST identity and comparison
// ============================================================================

/// Check if two AST nodes are equal (same internal ID).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_eq_ast(_c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> bool {
    t1 == t2
}

/// Get a unique identifier for an AST node.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_ast_id(_c: Z3_context, a: Z3_ast) -> c_uint {
    a as c_uint
}

/// Get a hash value for an AST node (same as the ID for Z4).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_ast_hash(_c: Z3_context, a: Z3_ast) -> c_uint {
    a as c_uint
}

// ============================================================================
// FuncDecl conversions and comparison
// ============================================================================

/// Convert a func_decl to an AST (returns 0 as func_decls are not ASTs in Z4).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_decl_to_ast(_c: Z3_context, _d: Z3_func_decl) -> Z3_ast {
    0
}

/// Check if two func_decl handles are equal (pointer equality).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_eq_func_decl(
    c: Z3_context,
    f1: Z3_func_decl,
    f2: Z3_func_decl,
) -> bool {
    if f1.is_null() || f2.is_null() {
        return f1 == f2;
    }
    // Guard the pointer dereferences
    unsafe {
        ffi_guard_int(c, 0, |_ctx| {
            let d1 = &(*f1).decl;
            let d2 = &(*f2).decl;
            i32::from(d1 == d2)
        }) != 0
    }
}

/// Convert a func_decl to a string representation.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_decl_to_string(c: Z3_context, d: Z3_func_decl) -> *const c_char {
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if d.is_null() {
                return cache_string(ctx, "(null)".to_string());
            }
            let decl = &(*d).decl;
            cache_string(ctx, format!("{decl}"))
        })
    }
}

// ============================================================================
// Symbol introspection
// ============================================================================

/// Get the kind of a symbol.
///
/// Returns 0 for int symbol (Z3_INT_SYMBOL), 1 for string symbol (Z3_STRING_SYMBOL).
/// Int symbols created by `Z3_mk_int_symbol` use an internal `"s!N"` prefix.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_symbol_kind(c: Z3_context, s: Z3_symbol) -> c_uint {
    if s.is_null() {
        return 1; // string kind
    }
    unsafe {
        ffi_guard_uint(c, 1, |_ctx| {
            let sym = &(*s).name;
            // Int symbols are stored as "s!N" by Z3_mk_int_symbol
            if sym.starts_with("s!") && sym[2..].parse::<i32>().is_ok() {
                0 // Z3_INT_SYMBOL
            } else {
                1 // Z3_STRING_SYMBOL
            }
        })
    }
}

/// Get the integer value of an int symbol.
///
/// Returns -1 if the symbol is not an integer symbol.
/// Int symbols created by `Z3_mk_int_symbol` use an internal `"s!N"` prefix.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_symbol_int(c: Z3_context, s: Z3_symbol) -> c_int {
    if s.is_null() {
        return -1;
    }
    unsafe {
        ffi_guard_int(c, -1, |_ctx| {
            let sym = &(*s).name;
            // Int symbols are stored as "s!N" by Z3_mk_int_symbol
            if let Some(num_str) = sym.strip_prefix("s!") {
                num_str.parse::<c_int>().unwrap_or(-1)
            } else {
                -1
            }
        })
    }
}

// ============================================================================
// Sort identity and naming
// ============================================================================

/// Get the name of a sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort_name(c: Z3_context, s: Z3_sort) -> Z3_symbol {
    if s.is_null() {
        return ptr::null_mut();
    }
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let sort = &(*s).sort;
            let name = format!("{sort}");
            cache_symbol(ctx, name)
        })
    }
}

/// Check if two sorts are equal.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_eq_sort(c: Z3_context, s1: Z3_sort, s2: Z3_sort) -> bool {
    if s1.is_null() || s2.is_null() {
        return s1 == s2;
    }
    unsafe {
        ffi_guard_int(c, 0, |_ctx| {
            let sort1 = &(*s1).sort;
            let sort2 = &(*s2).sort;
            i32::from(sort1 == sort2)
        }) != 0
    }
}

/// Get the unique ID of a sort.
///
/// Returns a stable semantic sort ID: same `Sort` value → same ID within
/// this context. Different sorts → different IDs. Null → 0. (#6580)
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort_id(_c: Z3_context, s: Z3_sort) -> c_uint {
    if s.is_null() {
        return 0;
    }
    unsafe { (*s).sort_id }
}
