// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// z4-dpll panicking convenience methods are deprecated in favor of try_* variants.
// This FFI layer uses catch_unwind guards; migration to try_* tracked in z4#6183.
#![allow(deprecated)]
#![deny(clippy::unwrap_used)]

//! z4-ffi: C FFI bindings for Z4 SMT solver
//!
//! This crate provides C-compatible FFI bindings for Z4, enabling integration
//! with Lean 5, other language runtimes, and external tools.
//!
//! # Thread Safety
//!
//! Z4Solver handles are NOT thread-safe. Each solver instance should be used
//! from a single thread. For concurrent use, create separate solver instances.
//!
//! # Memory Management
//!
//! - Solver handles must be freed with `z4_solver_free`
//! - String results must be freed with `z4_string_free`
//! - Failure to free memory will cause leaks
//!
//! # Example (C)
//!
//! ```c
//! Z4Solver* solver = z4_solver_new();
//! const char* smtlib = "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(check-sat)";
//! int result = z4_solve_smtlib(solver, smtlib);
//! if (result == Z4_SAT) {
//!     char* model = z4_get_model(solver);
//!     printf("Model: %s\n", model);
//!     z4_string_free(model);
//! }
//! z4_solver_free(solver);
//! ```
//!
//! Author: Andrew Yates

#[allow(non_camel_case_types, non_snake_case)]
pub mod z3_compat;

use std::ffi::{c_char, c_int, CStr, CString};
use std::panic::{catch_unwind, AssertUnwindSafe};

use z4_dpll::Executor;
use z4_frontend::{parse, Command};

// ============================================================================
// Result Codes
// ============================================================================

/// Satisfiable - a model exists
pub const Z4_SAT: c_int = 1;
/// Unsatisfiable - no model exists
pub const Z4_UNSAT: c_int = 0;
/// Unknown - solver could not determine satisfiability
pub const Z4_UNKNOWN: c_int = -1;
/// Error - invalid input or internal error
pub const Z4_ERROR: c_int = -2;

// ============================================================================
// Solver Handle
// ============================================================================

/// Opaque solver handle for FFI
///
/// This wraps the internal Z4 executor and maintains state between calls.
pub struct Z4Solver {
    executor: Executor,
    last_error: Option<String>,
}

impl Z4Solver {
    fn new() -> Self {
        Self {
            executor: Executor::new(),
            last_error: None,
        }
    }

    fn set_error(&mut self, msg: String) {
        self.last_error = Some(msg);
    }

    fn clear_error(&mut self) {
        self.last_error = None;
    }
}

// ============================================================================
// Core FFI Functions
// ============================================================================

/// Create a new solver instance
///
/// # Returns
/// - Non-null pointer to solver handle on success
/// - Null pointer on failure (out of memory)
///
/// # Safety
/// The returned pointer must be freed with `z4_solver_free`.
#[no_mangle]
pub extern "C" fn z4_solver_new() -> *mut Z4Solver {
    match catch_unwind(Z4Solver::new) {
        Ok(solver) => Box::into_raw(Box::new(solver)),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Destroy a solver instance and free associated memory
///
/// # Safety
/// - `solver` must be a valid pointer returned by `z4_solver_new`
/// - `solver` must not be used after this call
/// - Safe to call with null pointer (no-op)
#[no_mangle]
pub unsafe extern "C" fn z4_solver_free(solver: *mut Z4Solver) {
    if solver.is_null() {
        return;
    }
    // Drop could panic (e.g., Executor cleanup); catch to prevent UB across FFI.
    let _ = catch_unwind(AssertUnwindSafe(|| unsafe {
        let _ = Box::from_raw(solver);
    }));
}

/// Solve SMT-LIB input and return result
///
/// Parses and executes the given SMT-LIB commands, returning the result
/// of the last `(check-sat)` command.
///
/// # Arguments
/// - `solver` - Solver handle from `z4_solver_new`
/// - `smtlib` - Null-terminated UTF-8 string containing SMT-LIB commands
///
/// # Returns
/// - `Z4_SAT` (1) if satisfiable
/// - `Z4_UNSAT` (0) if unsatisfiable
/// - `Z4_UNKNOWN` (-1) if solver could not determine
/// - `Z4_ERROR` (-2) if parse error or invalid input
///
/// # Safety
/// - `solver` must be a valid pointer from `z4_solver_new`
/// - `smtlib` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn z4_solve_smtlib(solver: *mut Z4Solver, smtlib: *const c_char) -> c_int {
    // Validate pointers before entering catch_unwind
    if solver.is_null() || smtlib.is_null() {
        return Z4_ERROR;
    }

    let result = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.clear_error();

        // Parse input string
        let smtlib_str = match CStr::from_ptr(smtlib).to_str() {
            Ok(s) => s,
            Err(_) => {
                solver.set_error("Input is not valid UTF-8".to_string());
                return Z4_ERROR;
            }
        };

        // Parse SMT-LIB commands
        let commands = match parse(smtlib_str) {
            Ok(cmds) => cmds,
            Err(e) => {
                solver.set_error(format!("Parse error: {e}"));
                return Z4_ERROR;
            }
        };

        // Execute commands and track last check-sat result
        let mut last_result = Z4_UNKNOWN;

        for cmd in &commands {
            match solver.executor.execute(cmd) {
                Ok(Some(output)) => {
                    // Check if this is a check-sat result
                    match output.as_str() {
                        "sat" => last_result = Z4_SAT,
                        "unsat" => last_result = Z4_UNSAT,
                        "unknown" => last_result = Z4_UNKNOWN,
                        _ => {} // Other outputs (e.g., get-model) don't change result
                    }
                }
                Ok(None) => {}
                Err(e) => {
                    solver.set_error(format!("Execution error: {e}"));
                    return Z4_ERROR;
                }
            }
        }

        last_result
    }));

    match result {
        Ok(val) => val,
        Err(panic) => unsafe {
            let solver = &mut *solver;
            solver.set_error(format!(
                "panic in z4_solve_smtlib: {}",
                z3_compat::panic_payload_to_string(&*panic)
            ));
            Z4_ERROR
        },
    }
}

/// Get the model from the last SAT result
///
/// Returns the model as an SMT-LIB formatted string. Only valid after
/// a `check-sat` that returned SAT.
///
/// # Returns
/// - Pointer to null-terminated string on success (caller must free with `z4_string_free`)
/// - Null pointer if no model available or error
///
/// # Safety
/// - `solver` must be a valid pointer from `z4_solver_new`
/// - Returned string must be freed with `z4_string_free`
#[no_mangle]
pub unsafe extern "C" fn z4_get_model(solver: *mut Z4Solver) -> *mut c_char {
    if solver.is_null() {
        return std::ptr::null_mut();
    }

    match catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;

        // Execute get-model command
        let cmd = Command::GetModel;
        match solver.executor.execute(&cmd) {
            Ok(Some(model)) => match CString::new(model) {
                Ok(s) => s.into_raw(),
                Err(_) => std::ptr::null_mut(),
            },
            _ => std::ptr::null_mut(),
        }
    })) {
        Ok(val) => val,
        Err(_) => std::ptr::null_mut(),
    }
}

/// Get the last error message
///
/// # Returns
/// - Pointer to null-terminated error message (caller must free with `z4_string_free`)
/// - Null pointer if no error
///
/// # Safety
/// - `solver` must be a valid pointer from `z4_solver_new`
#[no_mangle]
pub unsafe extern "C" fn z4_get_error(solver: *mut Z4Solver) -> *mut c_char {
    if solver.is_null() {
        return std::ptr::null_mut();
    }

    match catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &*solver;

        match &solver.last_error {
            Some(msg) => match CString::new(msg.as_str()) {
                Ok(s) => s.into_raw(),
                Err(_) => std::ptr::null_mut(),
            },
            None => std::ptr::null_mut(),
        }
    })) {
        Ok(val) => val,
        Err(_) => std::ptr::null_mut(),
    }
}

/// Free a string returned by z4 functions
///
/// # Safety
/// - `s` must be a pointer returned by z4 string functions
/// - `s` must not be used after this call
/// - Safe to call with null pointer (no-op)
#[no_mangle]
pub unsafe extern "C" fn z4_string_free(s: *mut c_char) {
    unsafe {
        if !s.is_null() {
            let _ = CString::from_raw(s);
        }
    }
}

/// Reset the solver state
///
/// Clears all assertions and declarations, returning the solver to
/// its initial state. Equivalent to creating a new solver.
///
/// # Safety
/// - `solver` must be a valid pointer from `z4_solver_new`
#[no_mangle]
pub unsafe extern "C" fn z4_reset(solver: *mut Z4Solver) {
    if solver.is_null() {
        return;
    }

    let _ = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.executor = Executor::new();
        solver.clear_error();
    }));
}

// ============================================================================
// Quick Solve Functions (One-shot, no handle needed)
// ============================================================================

/// Quick SMT solve (one-shot, no handle management)
///
/// Convenience function for simple solve operations. Creates a temporary
/// solver, runs the input, and returns the result.
///
/// # Arguments
/// - `smtlib` - Null-terminated UTF-8 string containing SMT-LIB commands
///
/// # Returns
/// - `Z4_SAT`, `Z4_UNSAT`, `Z4_UNKNOWN`, or `Z4_ERROR`
///
/// # Safety
/// - `smtlib` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn z4_quick_solve(smtlib: *const c_char) -> c_int {
    unsafe {
        let solver = z4_solver_new();
        if solver.is_null() {
            return Z4_ERROR;
        }

        let result = z4_solve_smtlib(solver, smtlib);
        z4_solver_free(solver);
        result
    }
}

/// Shared helper: wrap a formula with a logic declaration and quick-solve.
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
unsafe fn solve_with_logic(formula: *const c_char, logic: &str) -> c_int {
    unsafe {
        if formula.is_null() {
            return Z4_ERROR;
        }

        let formula_str = match CStr::from_ptr(formula).to_str() {
            Ok(s) => s,
            Err(_) => return Z4_ERROR,
        };

        let full_input = format!("(set-logic {logic})\n{formula_str}");

        let c_input = match CString::new(full_input) {
            Ok(s) => s,
            Err(_) => return Z4_ERROR,
        };

        z4_quick_solve(c_input.as_ptr())
    }
}

/// Quick LIA solve for linear integer arithmetic formulas
///
/// Convenience function for QF_LIA problems. Automatically wraps the
/// formula with appropriate logic declaration.
///
/// # Arguments
/// - `formula` - SMT-LIB formula without logic declaration
///
/// # Example
/// ```c
/// // Just the assertions and check-sat
/// const char* formula = "(declare-const x Int)(assert (> x 0))(check-sat)";
/// int result = z4_solve_lia(formula);
/// ```
///
/// # Returns
/// - `Z4_SAT`, `Z4_UNSAT`, `Z4_UNKNOWN`, or `Z4_ERROR`
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn z4_solve_lia(formula: *const c_char) -> c_int {
    unsafe { solve_with_logic(formula, "QF_LIA") }
}

/// Quick SAT solve for propositional formulas
///
/// Convenience function for QF_UF (propositional) problems.
///
/// # Arguments
/// - `formula` - SMT-LIB formula with Bool declarations
///
/// # Returns
/// - `Z4_SAT`, `Z4_UNSAT`, `Z4_UNKNOWN`, or `Z4_ERROR`
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn z4_solve_sat(formula: *const c_char) -> c_int {
    unsafe { solve_with_logic(formula, "QF_UF") }
}

/// Quick BV solve for bitvector formulas
///
/// Convenience function for QF_BV problems.
///
/// # Arguments
/// - `formula` - SMT-LIB formula with BitVec declarations
///
/// # Returns
/// - `Z4_SAT`, `Z4_UNSAT`, `Z4_UNKNOWN`, or `Z4_ERROR`
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn z4_solve_bv(formula: *const c_char) -> c_int {
    unsafe { solve_with_logic(formula, "QF_BV") }
}

// ============================================================================
// Version and Info
// ============================================================================

/// Get Z4 version string
///
/// Returns the crate version from Cargo.toml via compile-time macro.
///
/// # Returns
/// - Pointer to heap-allocated version string (caller must free with `z4_string_free`)
/// - Null pointer if allocation fails (should not happen in practice)
#[no_mangle]
pub extern "C" fn z4_version() -> *mut c_char {
    // CString::new cannot fail here since VERSION has no interior NULs
    match CString::new(env!("CARGO_PKG_VERSION")) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
