// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible sort construction and inspection functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_uint};
use std::ptr;

use z4_dpll::api::Sort;

use super::{
    alloc_sort, cache_string, ffi_guard_const_ptr, ffi_guard_ptr, ffi_guard_uint, Z3_context,
    Z3_sort, Z3_symbol, Z3_ARRAY_SORT, Z3_BOOL_SORT, Z3_BV_SORT, Z3_INT_SORT, Z3_REAL_SORT,
    Z3_UNINTERPRETED_SORT, Z3_UNKNOWN_AST,
};

/// Create Bool sort.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bool_sort(c: Z3_context) -> Z3_sort {
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Bool)) }
}

/// Create Int sort.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int_sort(c: Z3_context) -> Z3_sort {
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Int)) }
}

/// Create Real sort.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real_sort(c: Z3_context) -> Z3_sort {
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Real)) }
}

/// Create bitvector sort of given width.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bv_sort(c: Z3_context, sz: c_uint) -> Z3_sort {
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::bitvec(sz))) }
}

/// Create array sort with given domain and range sorts.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_array_sort(
    c: Z3_context,
    domain: Z3_sort,
    range: Z3_sort,
) -> Z3_sort {
    if domain.is_null() || range.is_null() {
        return ptr::null_mut();
    }
    let d = unsafe { (*domain).sort.clone() };
    let r = unsafe { (*range).sort.clone() };
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::array(d.clone(), r.clone()))) }
}

/// Create uninterpreted sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_uninterpreted_sort(c: Z3_context, s: Z3_symbol) -> Z3_sort {
    if s.is_null() {
        return ptr::null_mut();
    }
    let name = unsafe { (*s).name.clone() };
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Uninterpreted(name.clone()))) }
}

/// Get the sort kind.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort_kind(_c: Z3_context, t: Z3_sort) -> c_uint {
    if t.is_null() {
        return Z3_UNKNOWN_AST;
    }
    unsafe {
        ffi_guard_uint(_c, Z3_UNKNOWN_AST, |_ctx| match &(*t).sort {
            Sort::Bool => Z3_BOOL_SORT,
            Sort::Int => Z3_INT_SORT,
            Sort::Real => Z3_REAL_SORT,
            Sort::BitVec(_) => Z3_BV_SORT,
            Sort::Array(_) => Z3_ARRAY_SORT,
            Sort::Uninterpreted(_) => Z3_UNINTERPRETED_SORT,
            _ => Z3_UNKNOWN_AST,
        })
    }
}

/// Get the size of a bitvector sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_bv_sort_size(_c: Z3_context, t: Z3_sort) -> c_uint {
    if t.is_null() {
        return 0;
    }
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| match &(*t).sort {
            Sort::BitVec(bvs) => bvs.width,
            _ => 0,
        })
    }
}

/// Get the domain sort of an array sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_array_sort_domain(c: Z3_context, t: Z3_sort) -> Z3_sort {
    if t.is_null() {
        return ptr::null_mut();
    }
    let sort = match unsafe { &(*t).sort } {
        Sort::Array(a) => a.index_sort.clone(),
        _ => return ptr::null_mut(),
    };
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

/// Get the range sort of an array sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_array_sort_range(c: Z3_context, t: Z3_sort) -> Z3_sort {
    if t.is_null() {
        return ptr::null_mut();
    }
    let sort = match unsafe { &(*t).sort } {
        Sort::Array(a) => a.element_sort.clone(),
        _ => return ptr::null_mut(),
    };
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

/// Convert a sort to a string representation.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_sort_to_string(c: Z3_context, s: Z3_sort) -> *const c_char {
    if s.is_null() {
        return ptr::null();
    }
    let sort_str = format!("{:?}", unsafe { &(*s).sort });
    unsafe { ffi_guard_const_ptr(c, |ctx| cache_string(ctx, sort_str.clone())) }
}
