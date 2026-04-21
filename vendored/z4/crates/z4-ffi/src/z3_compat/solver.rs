// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible solver lifecycle and check-sat functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint, CStr};
use std::ptr;

use z4_dpll::api::SolveResult;

use super::{
    apply_supported_params, ast_to_term, cache_ast_vector, cache_string, ctx_ref,
    ffi_guard_const_ptr, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, term_to_ast,
    ModelHandle, Z3SolverHandle, Z3_ast, Z3_ast_vector, Z3_context, Z3_func_decl, Z3_model,
    Z3_params, Z3_solver, Z3_sort, Z3_symbol, Z3_EXCEPTION, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF,
    Z3_OK,
};

// ---- Solver lifecycle ----

/// Create a solver.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_solver(c: Z3_context) -> Z3_solver {
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let handle = Box::into_raw(Box::new(Z3SolverHandle { _ctx: c }));
            ctx.solver_handle_cache.push(handle);
            handle
        })
    }
}

/// Create a solver for a specific logic (same as `Z3_mk_solver` in Z4).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_solver_for_logic(c: Z3_context, _logic: Z3_symbol) -> Z3_solver {
    unsafe { Z3_mk_solver(c) }
}

/// Increment solver reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_inc_ref(_c: Z3_context, _s: Z3_solver) {}

/// Decrement solver reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_dec_ref(_c: Z3_context, _s: Z3_solver) {}

/// Push a solver scope.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_push(c: Z3_context, _s: Z3_solver) {
    unsafe {
        ffi_guard_void(c, |ctx| {
            if let Err(e) = ctx.solver.try_push() {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
            }
        });
    }
}

/// Pop `n` solver scopes.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_pop(c: Z3_context, _s: Z3_solver, n: c_uint) {
    unsafe {
        ffi_guard_void(c, |ctx| {
            for _ in 0..n {
                if let Err(e) = ctx.solver.try_pop() {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    return;
                }
            }
        });
    }
}

/// Reset the solver.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_reset(c: Z3_context, _s: Z3_solver) {
    unsafe {
        ffi_guard_void(c, |ctx| {
            if let Err(e) = ctx.solver.try_reset() {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
            }
        });
    }
}

/// Assert a formula in the solver.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_assert(c: Z3_context, _s: Z3_solver, a: Z3_ast) {
    unsafe {
        ffi_guard_void(c, |ctx| {
            if let Err(e) = ctx.solver.try_assert_term(ast_to_term(a)) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
            }
        });
    }
}

/// Set solver params.
///
/// Only `timeout` is currently honored by Z4.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_set_params(c: Z3_context, _s: Z3_solver, p: Z3_params) {
    if c.is_null() || p.is_null() {
        return;
    }
    let params = unsafe { &(*p).params };
    // Clone params to avoid referencing raw pointer inside catch_unwind
    let params_owned: Vec<(String, String)> = params.clone();
    unsafe {
        ffi_guard_void(c, |ctx| {
            apply_supported_params(&mut ctx.solver, &params_owned);
        });
    }
}

/// Check satisfiability.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_check(c: Z3_context, _s: Z3_solver) -> c_int {
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| match ctx.solver.check_sat().result() {
            SolveResult::Sat => Z3_L_TRUE,
            SolveResult::Unsat => Z3_L_FALSE,
            SolveResult::Unknown | _ => Z3_L_UNDEF,
        })
    }
}

/// Check satisfiability under assumptions.
///
/// # Safety
/// All pointers must be valid. `assumptions` must point to `num_assumptions` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_check_assumptions(
    c: Z3_context,
    _s: Z3_solver,
    num_assumptions: c_uint,
    assumptions: *const Z3_ast,
) -> c_int {
    // Pre-extract assumption terms before entering the guard, since raw pointer
    // dereferences need to happen in the unsafe extern "C" context.
    let terms: Vec<_> = if num_assumptions == 0 || assumptions.is_null() {
        Vec::new()
    } else {
        (0..num_assumptions as usize)
            .map(|i| ast_to_term(unsafe { *assumptions.add(i) }))
            .collect()
    };
    let has_assumptions = num_assumptions > 0 && !assumptions.is_null();

    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            if !has_assumptions {
                return match ctx.solver.check_sat().result() {
                    SolveResult::Sat => Z3_L_TRUE,
                    SolveResult::Unsat => Z3_L_FALSE,
                    SolveResult::Unknown | _ => Z3_L_UNDEF,
                };
            }
            match ctx.solver.check_sat_assuming(&terms).result() {
                SolveResult::Sat => Z3_L_TRUE,
                SolveResult::Unsat => Z3_L_FALSE,
                SolveResult::Unknown | _ => Z3_L_UNDEF,
            }
        })
    }
}

/// Get the model from the last SAT check.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_model(c: Z3_context, _s: Z3_solver) -> Z3_model {
    unsafe {
        ffi_guard_ptr(c, |ctx| match ctx.solver.model() {
            Some(model) => {
                let handle = Box::into_raw(Box::new(ModelHandle {
                    model: model.into_inner(),
                    _ctx: c,
                }));
                ctx.model_cache.push(handle);
                handle
            }
            None => ptr::null_mut(),
        })
    }
}

/// Convert solver state to a string.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_to_string(c: Z3_context, _s: Z3_solver) -> *const c_char {
    unsafe { ffi_guard_const_ptr(c, |ctx| cache_string(ctx, "(solver)".to_string())) }
}

/// Get the reason for the last Unknown result.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_reason_unknown(
    c: Z3_context,
    _s: Z3_solver,
) -> *const c_char {
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let reason = ctx
                .solver
                .reason_unknown_smtlib()
                .unwrap_or_else(|| "unknown".to_string());
            cache_string(ctx, reason)
        })
    }
}

/// Get the number of scopes pushed on the solver.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_num_scopes(c: Z3_context, _s: Z3_solver) -> c_uint {
    unsafe { ffi_guard_uint(c, 0, |ctx| ctx.solver.num_scopes()) }
}

/// Interrupt the solver from another thread.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_interrupt(c: Z3_context, _s: Z3_solver) {
    unsafe {
        ffi_guard_void(c, |ctx| {
            ctx.solver.interrupt();
        });
    }
}

/// Get the assertions currently in the solver as an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_assertions(c: Z3_context, _s: Z3_solver) -> Z3_ast_vector {
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let asts = ctx
                .solver
                .assertions()
                .into_iter()
                .map(term_to_ast)
                .collect();
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Get the unsat core from the last UNSAT check-sat-assuming result.
///
/// Returns an AST vector containing the subset of assumptions that
/// contributed to unsatisfiability. Returns an empty vector if the last
/// result was not UNSAT or was not produced by check-sat-assuming.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_unsat_core(c: Z3_context, _s: Z3_solver) -> Z3_ast_vector {
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let asts = match ctx.solver.unsat_assumptions() {
                Some(terms) => terms.into_iter().map(term_to_ast).collect(),
                None => Vec::new(),
            };
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Parse an SMT-LIB2 string and return assertions as an AST vector.
///
/// Parses declarations and assertions from the input string.
/// Query commands (check-sat, get-model, etc.) are ignored.
/// The `sort_names`/`sorts` and `decl_names`/`decls` parameters allow
/// pre-declaring sorts and functions (currently ignored — all declarations
/// must be in the string itself).
///
/// # Safety
/// All pointers must be valid. `str` must be a null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_parse_smtlib2_string(
    c: Z3_context,
    str: *const c_char,
    _num_sorts: c_uint,
    _sort_names: *const Z3_symbol,
    _sorts: *const Z3_sort,
    _num_decls: c_uint,
    _decl_names: *const Z3_symbol,
    _decls: *const Z3_func_decl,
) -> Z3_ast_vector {
    // Pre-validate and extract the input string outside the guard,
    // since raw pointer dereferences happen in the unsafe extern "C" context.
    let input_string = if str.is_null() {
        None
    } else {
        match unsafe { CStr::from_ptr(str) }.to_str() {
            Ok(s) => Some(s.to_string()),
            Err(_) => {
                // Set error before returning
                if let Some(ctx) = unsafe { ctx_ref(c) } {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some("invalid UTF-8 in input string".to_string());
                    return cache_ast_vector(ctx, Vec::new());
                }
                return ptr::null_mut();
            }
        }
    };

    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(ref input) = input_string else {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some("null input string".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            match ctx.solver.parse_smtlib2(input) {
                Ok(terms) => {
                    ctx.last_error = Z3_OK;
                    let asts = terms.into_iter().map(term_to_ast).collect();
                    cache_ast_vector(ctx, asts)
                }
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    cache_ast_vector(ctx, Vec::new())
                }
            }
        })
    }
}
