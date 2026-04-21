// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible context, config, and symbol lifecycle functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint, CStr};
use std::ptr;

use z4_dpll::api::{Logic, Solver};

use super::{
    apply_supported_params, cache_string, cache_symbol, ffi_guard_const_ptr, ffi_guard_ptr,
    ffi_guard_void, Z3Config, Z3Context, Z3_ast, Z3_config, Z3_context, Z3_symbol, Z3_OK,
};

/// Create a new configuration object.
#[no_mangle]
pub extern "C" fn Z3_mk_config() -> Z3_config {
    Box::into_raw(Box::new(Z3Config { params: Vec::new() }))
}

/// Delete a configuration object.
///
/// # Safety
/// `c` must be a valid config pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_del_config(c: Z3_config) {
    if c.is_null() {
        return;
    }
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        let _ = Box::from_raw(c);
    }));
}

/// Set a configuration parameter.
///
/// Only `timeout` is currently honored by Z4.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_set_param_value(
    c: Z3_config,
    param_id: *const c_char,
    param_value: *const c_char,
) {
    if c.is_null() || param_id.is_null() || param_value.is_null() {
        return;
    }
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        let cfg = &mut *c;
        if let (Ok(k), Ok(v)) = (
            CStr::from_ptr(param_id).to_str(),
            CStr::from_ptr(param_value).to_str(),
        ) {
            cfg.params.push((k.to_string(), v.to_string()));
        }
    }));
}

/// Create a new context with the given configuration.
///
/// Uses `Logic::All` since Z3 contexts are logic-agnostic. Recognized config
/// parameters are copied onto the new solver during construction.
///
/// # Safety
/// `c` must be a valid config pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_context(c: Z3_config) -> Z3_context {
    // Solver::new could theoretically panic; use catch_unwind directly since
    // we don't have a context yet to pass to ffi_guard.
    match std::panic::catch_unwind(|| {
        let mut solver = Solver::new(Logic::All);
        if !c.is_null() {
            unsafe {
                apply_supported_params(&mut solver, &(*c).params);
            }
        }
        Box::into_raw(Box::new(Z3Context {
            solver,
            last_error: Z3_OK,
            error_msg: None,
            string_cache: Vec::new(),
            symbol_cache: Vec::new(),
            ast_sorts: Vec::new(),
            sort_cache: Vec::new(),
            func_decl_cache: Vec::new(),
            solver_handle_cache: Vec::new(),
            model_cache: Vec::new(),
            params_cache: Vec::new(),
            ast_vector_cache: Vec::new(),
            pattern_cache: Vec::new(),
            sort_ids: std::collections::HashMap::new(),
            next_sort_id: 1,
        }))
    }) {
        Ok(ctx) => ctx,
        Err(_) => ptr::null_mut(),
    }
}

/// Create a new context with reference counting enabled.
/// Identical to `Z3_mk_context`. Z4 does not distinguish reference-counted contexts.
///
/// # Safety
/// `c` must be a valid config pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_context_rc(c: Z3_config) -> Z3_context {
    unsafe { Z3_mk_context(c) }
}

/// Delete a context and all associated resources.
///
/// # Safety
/// `c` must be a valid context pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_del_context(c: Z3_context) {
    if c.is_null() {
        return;
    }
    // Drop of Z3Context runs drain_arena on all cached handles; catch any panic
    // to prevent UB across the FFI boundary.
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        let _ = Box::from_raw(c);
    }));
}

/// Increment reference count for an AST (no-op in Z4).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_inc_ref(_c: Z3_context, _a: Z3_ast) {}

/// Decrement reference count for an AST (no-op in Z4).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_dec_ref(_c: Z3_context, _a: Z3_ast) {}

/// Interrupt the context (cancel ongoing computation).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_interrupt(c: Z3_context) {
    unsafe {
        ffi_guard_void(c, |ctx| {
            ctx.solver.interrupt();
        });
    }
}

/// Create an integer symbol.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int_symbol(c: Z3_context, i: c_int) -> Z3_symbol {
    unsafe { ffi_guard_ptr(c, |ctx| cache_symbol(ctx, format!("s!{i}"))) }
}

/// Create a string symbol.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_string_symbol(c: Z3_context, s: *const c_char) -> Z3_symbol {
    if s.is_null() {
        return ptr::null_mut();
    }
    let name = match unsafe { CStr::from_ptr(s).to_str() } {
        Ok(n) => n.to_string(),
        Err(_) => return ptr::null_mut(),
    };
    unsafe { ffi_guard_ptr(c, |ctx| cache_symbol(ctx, name.clone())) }
}

/// Get the string representation of a symbol.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_symbol_string(c: Z3_context, s: Z3_symbol) -> *const c_char {
    if s.is_null() {
        return ptr::null();
    }
    let sym = unsafe { &*s };
    let name = sym.name.clone();
    unsafe { ffi_guard_const_ptr(c, |ctx| cache_string(ctx, name.clone())) }
}

/// Get Z3 version numbers.
/// Reports Z4's version as the Z3 compatibility version.
///
/// # Safety
/// All pointers must be valid or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_version(
    major: *mut c_uint,
    minor: *mut c_uint,
    build_number: *mut c_uint,
    revision_number: *mut c_uint,
) {
    unsafe {
        // Report Z3 API compatibility version 4.13.0.0
        if !major.is_null() {
            *major = 4;
        }
        if !minor.is_null() {
            *minor = 13;
        }
        if !build_number.is_null() {
            *build_number = 0;
        }
        if !revision_number.is_null() {
            *revision_number = 0;
        }
    }
}
