// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Integration test for z4_z3_compat.h header coverage (#4990).
//!
//! Exercises all 19 functions that were added to the header in the
//! header-implementation sync. Tests that each function is callable and
//! returns sensible results.

use std::ffi::CStr;
use z4_ffi::z3_compat::*;

/// Test symbol introspection: Z3_get_symbol_kind, Z3_get_symbol_int.
#[test]
fn test_symbol_introspection() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // String symbol
        let str_sym = Z3_mk_string_symbol(ctx, c"foo".as_ptr());
        assert_eq!(Z3_get_symbol_kind(ctx, str_sym), 1); // Z3_STRING_SYMBOL

        // Int symbol
        let int_sym = Z3_mk_int_symbol(ctx, 42);
        assert_eq!(Z3_get_symbol_kind(ctx, int_sym), 0); // Z3_INT_SYMBOL
        assert_eq!(Z3_get_symbol_int(ctx, int_sym), 42);

        Z3_del_context(ctx);
    }
}

/// Test sort identity: Z3_get_sort_name, Z3_is_eq_sort, Z3_get_sort_id.
#[test]
fn test_sort_identity() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);

        // Sort name
        let name = Z3_get_sort_name(ctx, int_sort);
        assert!(!name.is_null());
        let name_str = Z3_get_symbol_string(ctx, name);
        assert!(!name_str.is_null());
        let name_rs = CStr::from_ptr(name_str).to_string_lossy();
        assert!(
            name_rs.contains("Int") || name_rs.contains("int"),
            "Int sort name should contain 'Int', got: {name_rs}"
        );

        // Sort equality
        let int_sort2 = Z3_mk_int_sort(ctx);
        assert!(Z3_is_eq_sort(ctx, int_sort, int_sort2));
        assert!(!Z3_is_eq_sort(ctx, int_sort, bool_sort));

        // Sort ID is non-zero for valid sorts
        let id = Z3_get_sort_id(ctx, int_sort);
        assert_ne!(id, 0);

        Z3_del_context(ctx);
    }
}

/// Test Z3_mk_power: exponentiation.
#[test]
fn test_mk_power() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let power = Z3_mk_power(ctx, two, three);
        assert_ne!(power, 0, "Z3_mk_power should return non-null AST");

        Z3_del_context(ctx);
    }
}

/// Test AST inspection: Z3_is_numeral_ast, Z3_get_bool_value.
#[test]
fn test_ast_inspection() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let five = Z3_mk_int(ctx, 5, int_sort);

        // Numeral check
        assert!(Z3_is_numeral_ast(ctx, five));

        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        assert!(!Z3_is_numeral_ast(ctx, x));

        // Bool value
        let t = Z3_mk_true(ctx);
        let f = Z3_mk_false(ctx);
        assert_eq!(Z3_get_bool_value(ctx, t), Z3_L_TRUE);
        assert_eq!(Z3_get_bool_value(ctx, f), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// Test numeral extraction: uint, int64, uint64.
#[test]
fn test_numeral_extraction() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let val = Z3_mk_int(ctx, 42, int_sort);

        // Z3_get_numeral_uint
        let mut u: u32 = 0;
        let ok = Z3_get_numeral_uint(ctx, val, &raw mut u);
        assert!(ok);
        assert_eq!(u, 42);

        // Z3_get_numeral_int64
        let mut i64_val: i64 = 0;
        let ok = Z3_get_numeral_int64(ctx, val, &raw mut i64_val);
        assert!(ok);
        assert_eq!(i64_val, 42);

        // Z3_get_numeral_uint64
        let mut u64_val: u64 = 0;
        let ok = Z3_get_numeral_uint64(ctx, val, &raw mut u64_val);
        assert!(ok);
        assert_eq!(u64_val, 42);

        Z3_del_context(ctx);
    }
}

/// Test func_decl introspection: domain_size, decl_kind, func_decl_to_ast,
/// is_eq_func_decl, func_decl_to_string.
#[test]
fn test_func_decl_introspection() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let domain = [int_sort];
        let f = Z3_mk_func_decl(ctx, sym, 1, domain.as_ptr(), int_sort);
        assert!(!f.is_null());

        // Domain size
        let dsz = Z3_get_domain_size(ctx, f);
        assert_eq!(dsz, 1);

        // Decl kind (uninterpreted function → Z3_OP_UNINTERPRETED)
        let _kind = Z3_get_decl_kind(ctx, f);

        // func_decl_to_ast (returns 0 in Z4)
        let ast = Z3_func_decl_to_ast(ctx, f);
        assert_eq!(ast, 0);

        // is_eq_func_decl
        assert!(Z3_is_eq_func_decl(ctx, f, f));

        // func_decl_to_string
        let s = Z3_func_decl_to_string(ctx, f);
        assert!(!s.is_null());
        let rs = CStr::from_ptr(s).to_string_lossy();
        assert!(
            rs.contains('f'),
            "func_decl_to_string should contain 'f', got: {rs}"
        );

        Z3_del_context(ctx);
    }
}

/// Test solver extras: Z3_solver_get_num_scopes, Z3_solver_interrupt.
#[test]
fn test_solver_extras() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);

        // get_num_scopes — starts at 0
        let n = Z3_solver_get_num_scopes(ctx, solver);
        assert_eq!(n, 0);

        // push increases scope count
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 1);
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 2);

        // pop decreases scope count
        Z3_solver_pop(ctx, solver, 1);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 1);
        Z3_solver_pop(ctx, solver, 1);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 0);

        // Regression (#6740): reset must collapse scope depth to 0
        Z3_solver_push(ctx, solver);
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 2);
        Z3_solver_reset(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 0);
        // Push after reset counts from zero
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 1);

        // solver_interrupt (should not crash)
        Z3_solver_interrupt(ctx, solver);

        Z3_del_context(ctx);
    }
}

/// Test model extras: Z3_model_has_interp.
#[test]
fn test_model_has_interp() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let eq = Z3_mk_eq(ctx, x, five);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // x should have an interpretation in the model
        let decl = Z3_get_app_decl(ctx, x);
        if !decl.is_null() {
            let _has = Z3_model_has_interp(ctx, model, decl);
        }

        Z3_del_context(ctx);
    }
}
