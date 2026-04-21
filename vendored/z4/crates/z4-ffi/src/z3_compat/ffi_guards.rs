// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FFI panic guards (#6192): `catch_unwind` wrappers for extern "C" functions.
//!
//! Panics unwinding across `extern "C"` boundaries are undefined behavior.
//! These guards catch panics, record the error in the Z3Context, and return
//! a type-appropriate sentinel value.

use std::ffi::{c_char, c_int, c_uint};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::ptr;

use super::{Z3Context, Z3_ast, Z3_context, Z3_EXCEPTION};

/// Extract a human-readable message from a panic payload.
pub(crate) fn panic_payload_to_string(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

/// Guard an FFI function body that needs a context pointer and returns void.
/// On panic, sets `last_error = Z3_EXCEPTION` and records the panic message.
///
/// # Safety
/// Caller must ensure `c` is valid if non-null.
pub(crate) unsafe fn ffi_guard_void(c: Z3_context, f: impl FnOnce(&mut Z3Context)) {
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return;
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    if let Err(panic) = catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        let ctx = unsafe { &mut *ctx_ptr };
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(format!(
            "panic in FFI: {}",
            panic_payload_to_string(&*panic)
        ));
    }
}

/// Guard an FFI function body that needs a context pointer and returns `c_int`.
/// On panic, sets error state and returns `default_val`.
///
/// # Safety
/// Caller must ensure `c` is valid if non-null.
pub(crate) unsafe fn ffi_guard_int(
    c: Z3_context,
    default_val: c_int,
    f: impl FnOnce(&mut Z3Context) -> c_int,
) -> c_int {
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return default_val;
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            default_val
        }
    }
}

/// Guard an FFI function body that needs a context pointer and returns a pointer.
/// On panic, sets error state and returns null.
///
/// # Safety
/// Caller must ensure `c` is valid if non-null.
pub(crate) unsafe fn ffi_guard_ptr<T>(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> *mut T,
) -> *mut T {
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return ptr::null_mut();
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            ptr::null_mut()
        }
    }
}

/// Guard an FFI function body that needs a context pointer and returns `*const c_char`.
/// On panic, sets error state and returns null.
///
/// # Safety
/// Caller must ensure `c` is valid if non-null.
pub(crate) unsafe fn ffi_guard_const_ptr(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> *const c_char,
) -> *const c_char {
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return ptr::null();
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            ptr::null()
        }
    }
}

/// Guard an FFI function body that needs a context pointer and returns `Z3_ast` (u64).
/// On panic, sets error state and returns 0 (null AST).
///
/// # Safety
/// Caller must ensure `c` is valid if non-null.
pub(crate) unsafe fn ffi_guard_ast(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> Z3_ast,
) -> Z3_ast {
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return 0;
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            0
        }
    }
}

/// Guard an FFI function body that needs a context pointer and returns `c_uint`.
/// On panic, sets error state and returns `default_val`.
///
/// # Safety
/// Caller must ensure `c` is valid if non-null.
pub(crate) unsafe fn ffi_guard_uint(
    c: Z3_context,
    default_val: c_uint,
    f: impl FnOnce(&mut Z3Context) -> c_uint,
) -> c_uint {
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return default_val;
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            default_val
        }
    }
}
