// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::ffi::CString;

#[test]
fn test_solver_new_free() {
    unsafe {
        let solver = z4_solver_new();
        assert!(!solver.is_null());
        z4_solver_free(solver);
    }
}

/// SMOKE TEST: Verifies z4_solver_free handles null pointers gracefully.
/// This is critical for FFI safety - callers may pass invalid pointers.
#[test]
fn test_solver_free_null() {
    unsafe {
        // Should not crash - null pointer handling is required for safe FFI.
        // No assertion needed: reaching this point without crash = success.
        z4_solver_free(std::ptr::null_mut());
    }
}

#[test]
fn test_solve_sat() {
    unsafe {
        let solver = z4_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = z4_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, Z4_SAT);

        z4_solver_free(solver);
    }
}

#[test]
fn test_solve_unsat() {
    unsafe {
        let solver = z4_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (assert (< x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = z4_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, Z4_UNSAT);

        z4_solver_free(solver);
    }
}

#[test]
fn test_parse_error() {
    unsafe {
        let solver = z4_solver_new();
        let input = CString::new("(invalid syntax here").expect("test should succeed");

        let result = z4_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, Z4_ERROR);

        // Should have error message
        let error = z4_get_error(solver);
        assert!(!error.is_null());
        z4_string_free(error);

        z4_solver_free(solver);
    }
}

#[test]
fn test_quick_solve() {
    unsafe {
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = z4_quick_solve(input.as_ptr());
        assert_eq!(result, Z4_SAT);
    }
}

#[test]
fn test_solve_lia() {
    unsafe {
        let input = CString::new(
            "(declare-const x Int)
             (declare-const y Int)
             (assert (> x 0))
             (assert (> y 0))
             (assert (= (+ x y) 10))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = z4_solve_lia(input.as_ptr());
        assert_eq!(result, Z4_SAT);
    }
}

#[test]
fn test_solve_sat_propositional() {
    unsafe {
        let input = CString::new(
            "(declare-const p Bool)
             (declare-const q Bool)
             (assert (or p q))
             (assert (not p))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = z4_solve_sat(input.as_ptr());
        assert_eq!(result, Z4_SAT);
    }
}

#[test]
fn test_version() {
    let version = z4_version();
    assert!(!version.is_null());
    unsafe {
        let s = CStr::from_ptr(version)
            .to_str()
            .expect("test should succeed");
        assert!(s.starts_with("1."));
        z4_string_free(version);
    }
}

#[test]
fn test_reset() {
    unsafe {
        let solver = z4_solver_new();

        // First solve
        let input1 = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");
        let result1 = z4_solve_smtlib(solver, input1.as_ptr());
        assert_eq!(result1, Z4_SAT);

        // Reset
        z4_reset(solver);

        // Second solve (fresh state)
        let input2 = CString::new(
            "(set-logic QF_LIA)
             (declare-const y Int)
             (assert (< y 0))
             (check-sat)",
        )
        .expect("test should succeed");
        let result2 = z4_solve_smtlib(solver, input2.as_ptr());
        assert_eq!(result2, Z4_SAT);

        z4_solver_free(solver);
    }
}

#[test]
fn test_get_model() {
    unsafe {
        let solver = z4_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = z4_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, Z4_SAT);

        let model = z4_get_model(solver);
        assert!(!model.is_null());

        let model_str = CStr::from_ptr(model).to_str().expect("test should succeed");
        assert!(model_str.contains('x'));
        assert!(model_str.contains("42"));

        z4_string_free(model);
        z4_solver_free(solver);
    }
}

// ========================================================================
// Memory lifecycle tests (#895)
// These tests verify CString allocation/free patterns don't cause UB.
// ========================================================================

/// Test repeated z4_get_model calls with proper freeing between each.
/// Verifies no double-free or use-after-free occurs.
#[test]
fn test_get_model_repeated_alloc_free() {
    unsafe {
        let solver = z4_solver_new();

        // First SAT solve
        let input1 = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(z4_solve_smtlib(solver, input1.as_ptr()), Z4_SAT);

        // First model retrieval and free
        let model1 = z4_get_model(solver);
        assert!(!model1.is_null());
        let model1_str = CStr::from_ptr(model1)
            .to_str()
            .expect("test should succeed");
        assert!(model1_str.contains("42"));
        z4_string_free(model1);

        // Reset and second SAT solve with different value
        z4_reset(solver);
        let input2 = CString::new(
            "(set-logic QF_LIA)
             (declare-const y Int)
             (assert (= y 99))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(z4_solve_smtlib(solver, input2.as_ptr()), Z4_SAT);

        // Second model retrieval and free
        let model2 = z4_get_model(solver);
        assert!(!model2.is_null());
        let model2_str = CStr::from_ptr(model2)
            .to_str()
            .expect("test should succeed");
        assert!(model2_str.contains("99"));
        z4_string_free(model2);

        z4_solver_free(solver);
    }
}

/// Test z4_get_error lifecycle: call after error, free, call again when no error.
/// Verifies error state is properly cleared and string pointers are valid.
#[test]
fn test_get_error_lifecycle() {
    unsafe {
        let solver = z4_solver_new();

        // Initially no error - should return null
        let error_before = z4_get_error(solver);
        assert!(
            error_before.is_null(),
            "No error expected before any operations"
        );

        // Trigger a parse error
        let bad_input = CString::new("(invalid syntax").expect("test should succeed");
        let result = z4_solve_smtlib(solver, bad_input.as_ptr());
        assert_eq!(result, Z4_ERROR);

        // Error should be set now
        let error1 = z4_get_error(solver);
        assert!(
            !error1.is_null(),
            "Error message expected after parse failure"
        );
        let error1_str = CStr::from_ptr(error1)
            .to_str()
            .expect("test should succeed");
        assert!(
            error1_str.contains("Parse") || error1_str.contains("error"),
            "Error should mention parse issue"
        );
        z4_string_free(error1);

        // Can retrieve error again (independent allocation each time)
        let error2 = z4_get_error(solver);
        assert!(!error2.is_null(), "Error should persist until cleared");
        z4_string_free(error2);

        // Successful operation should clear error
        let good_input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");
        let result2 = z4_solve_smtlib(solver, good_input.as_ptr());
        assert_eq!(result2, Z4_SAT);

        // Error should be cleared now
        let error_after = z4_get_error(solver);
        assert!(
            error_after.is_null(),
            "Error should be cleared after successful operation"
        );

        z4_solver_free(solver);
    }
}

/// Test that strings obtained before z4_reset remain valid for freeing.
/// The reset shouldn't invalidate previously returned CStrings.
#[test]
fn test_reset_preserves_returned_string_validity() {
    unsafe {
        let solver = z4_solver_new();

        // Get a model
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(z4_solve_smtlib(solver, input.as_ptr()), Z4_SAT);

        let model = z4_get_model(solver);
        assert!(!model.is_null());

        // Reset the solver (this should NOT affect the returned string)
        z4_reset(solver);

        // The model string should still be valid (independent allocation)
        // This tests that into_raw() properly transfers ownership
        let model_str = CStr::from_ptr(model).to_str().expect("test should succeed");
        assert!(model_str.contains("42"));

        // And can be freed safely after reset
        z4_string_free(model);

        z4_solver_free(solver);
    }
}

/// Test null pointer handling in z4_string_free (idempotent).
/// Multiple null frees should be safe.
#[test]
fn test_string_free_null_idempotent() {
    unsafe {
        // First null free
        z4_string_free(std::ptr::null_mut());
        // Second null free (should remain safe)
        z4_string_free(std::ptr::null_mut());
    }
}

/// Test z4_get_model handles UNSAT result without memory issues.
/// SMT-LIB doesn't define get-model behavior after UNSAT, so we just
/// ensure no memory errors occur regardless of what's returned.
#[test]
fn test_get_model_safe_after_unsat() {
    unsafe {
        let solver = z4_solver_new();

        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (assert (< x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = z4_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, Z4_UNSAT);

        // Behavior after UNSAT is undefined per SMT-LIB; we just ensure
        // no memory errors. If non-null, we must free it properly.
        let model = z4_get_model(solver);
        if !model.is_null() {
            z4_string_free(model);
        }

        z4_solver_free(solver);
    }
}

/// Test calling z4_get_model twice on the same SAT result without reset.
/// Each call should return an independently allocated string.
#[test]
fn test_get_model_twice_without_reset() {
    unsafe {
        let solver = z4_solver_new();

        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(z4_solve_smtlib(solver, input.as_ptr()), Z4_SAT);

        // First call - get and free
        let model1 = z4_get_model(solver);
        assert!(!model1.is_null());
        z4_string_free(model1);

        // Second call on same result - get and free again
        let model2 = z4_get_model(solver);
        assert!(!model2.is_null());
        z4_string_free(model2);

        z4_solver_free(solver);
    }
}

/// Test calling z4_get_error twice and freeing both.
/// Each call should return an independently allocated string.
#[test]
fn test_get_error_twice_and_free_both() {
    unsafe {
        let solver = z4_solver_new();

        // Trigger error
        let bad_input = CString::new("(invalid").expect("test should succeed");
        assert_eq!(z4_solve_smtlib(solver, bad_input.as_ptr()), Z4_ERROR);

        // First call - get and free
        let error1 = z4_get_error(solver);
        assert!(!error1.is_null());
        z4_string_free(error1);

        // Second call - get and free again (error still present)
        let error2 = z4_get_error(solver);
        assert!(!error2.is_null());
        z4_string_free(error2);

        z4_solver_free(solver);
    }
}

/// Test that independent solver instances don't share state.
/// Each solver must have its own executor, error state, and model.
/// Memory corruption would show as cross-contamination between instances.
#[test]
fn test_independent_solver_instances_no_cross_contamination() {
    unsafe {
        let solver_a = z4_solver_new();
        let solver_b = z4_solver_new();
        assert!(!solver_a.is_null());
        assert!(!solver_b.is_null());
        assert_ne!(solver_a, solver_b, "Solvers must be distinct allocations");

        // Give solver_a a SAT problem
        let sat_input =
            CString::new("(set-logic QF_LIA)(declare-const x Int)(assert (= x 42))(check-sat)")
                .expect("test should succeed");
        assert_eq!(z4_solve_smtlib(solver_a, sat_input.as_ptr()), Z4_SAT);

        // Give solver_b an UNSAT problem
        let unsat_input = CString::new(
            "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(assert (< x 0))(check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(z4_solve_smtlib(solver_b, unsat_input.as_ptr()), Z4_UNSAT);

        // solver_a should still have a model (not affected by solver_b)
        let model_a = z4_get_model(solver_a);
        assert!(!model_a.is_null(), "solver_a model should be available");
        let model_str = CStr::from_ptr(model_a)
            .to_str()
            .expect("test should succeed");
        assert!(model_str.contains("42"), "solver_a model should contain 42");
        z4_string_free(model_a);

        // solver_b should have no error (UNSAT is not an error)
        let error_b = z4_get_error(solver_b);
        assert!(
            error_b.is_null(),
            "solver_b should have no error after clean UNSAT"
        );

        z4_solver_free(solver_a);
        z4_solver_free(solver_b);
    }
}

/// Test null pointer handling on all convenience solve functions.
/// Every entry point that accepts a pointer must handle null without UB.
#[test]
fn test_null_pointer_handling_all_entry_points() {
    unsafe {
        // Solver-level null handling
        assert_eq!(
            z4_solve_smtlib(std::ptr::null_mut(), std::ptr::null()),
            Z4_ERROR
        );
        assert!(z4_get_model(std::ptr::null_mut()).is_null());
        assert!(z4_get_error(std::ptr::null_mut()).is_null());
        z4_reset(std::ptr::null_mut()); // Should be no-op

        // Convenience function null handling
        assert_eq!(z4_quick_solve(std::ptr::null()), Z4_ERROR);
        assert_eq!(z4_solve_lia(std::ptr::null()), Z4_ERROR);
        assert_eq!(z4_solve_sat(std::ptr::null()), Z4_ERROR);
        assert_eq!(z4_solve_bv(std::ptr::null()), Z4_ERROR);

        // Null smtlib with valid solver
        let solver = z4_solver_new();
        assert_eq!(z4_solve_smtlib(solver, std::ptr::null()), Z4_ERROR);
        z4_solver_free(solver);
    }
}

/// Test that z4_version returns heap-allocated strings.
/// Each call must return an independently freeable pointer.
#[test]
fn test_version_returns_heap_allocated() {
    let v1 = z4_version();
    let v2 = z4_version();
    assert!(!v1.is_null());
    assert!(!v2.is_null());
    // Each call returns a separate heap allocation
    assert_ne!(
        v1, v2,
        "z4_version must return a fresh heap allocation each call"
    );
    unsafe {
        // Both must be freed via z4_string_free, same as all other FFI strings
        z4_string_free(v1);
        z4_string_free(v2);
    }
}
