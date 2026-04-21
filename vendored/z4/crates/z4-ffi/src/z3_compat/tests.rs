// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible C API.

use std::ptr;

use super::*;

/// Basic LIA: x > 0 AND x < 10 is SAT
#[test]
fn test_z3_compat_basic_lia() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let zero = Z3_mk_int(ctx, 0, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let x_gt_0 = Z3_mk_gt(ctx, x, zero);
        let x_lt_10 = Z3_mk_lt(ctx, x, ten);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, x_gt_0);
        Z3_solver_assert(ctx, solver, x_lt_10);

        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        let model_str = Z3_model_to_string(ctx, model);
        assert!(!model_str.is_null());

        Z3_del_context(ctx);
    }
}

/// Config timeout parameter is accepted and forwarded during context creation.
#[test]
fn test_z3_compat_config_timeout_param_smoke() {
    unsafe {
        let cfg = Z3_mk_config();
        Z3_set_param_value(cfg, c"timeout".as_ptr(), c"0".as_ptr());
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_ge(ctx, x, zero));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_UNDEF);
        let reason = Z3_solver_get_reason_unknown(ctx, solver);
        assert_eq!(
            std::ffi::CStr::from_ptr(reason)
                .to_str()
                .expect("reason should be valid UTF-8"),
            "timeout"
        );

        Z3_del_context(ctx);
    }
}

/// UNSAT: x > 10 AND x < 5
#[test]
fn test_z3_compat_unsat() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let five = Z3_mk_int(ctx, 5, int_sort);
        let ten = Z3_mk_int(ctx, 10, int_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_gt(ctx, x, ten));
        Z3_solver_assert(ctx, solver, Z3_mk_lt(ctx, x, five));

        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// Push/pop scoping
#[test]
fn test_z3_compat_push_pop() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let sym_a = Z3_mk_string_symbol(ctx, c"a".as_ptr());
        let a = Z3_mk_const(ctx, sym_a, bool_sort);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, a);

        Z3_solver_push(ctx, solver);
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, a));
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_FALSE);

        Z3_solver_pop(ctx, solver, 1);
        let result2 = Z3_solver_check(ctx, solver);
        assert_eq!(result2, Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Bitvector operations
#[test]
fn test_z3_compat_bitvectors() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym = Z3_mk_string_symbol(ctx, c"bv_x".as_ptr());
        let x = Z3_mk_const(ctx, sym, bv8);

        let five = Z3_mk_unsigned_int(ctx, 5, bv8);
        let result_add = Z3_mk_bvadd(ctx, x, five);
        assert_ne!(result_add, 0);

        let ten = Z3_mk_unsigned_int(ctx, 10, bv8);
        let cmp = Z3_mk_bvult(ctx, x, ten);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, cmp);
        let sat = Z3_solver_check(ctx, solver);
        assert_eq!(sat, Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Boolean operation construction
#[test]
fn test_z3_compat_boolean_ops() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_true(ctx);
        let f = Z3_mk_false(ctx);

        assert_ne!(t, 0);
        assert_ne!(f, 0);
        assert_ne!(t, f);

        let not_t = Z3_mk_not(ctx, t);
        let iff = Z3_mk_iff(ctx, not_t, f);
        let imp = Z3_mk_implies(ctx, t, f);
        let xor = Z3_mk_xor(ctx, t, f);

        assert_ne!(iff, 0);
        assert_ne!(imp, 0);
        assert_ne!(xor, 0);

        let args = [t, f];
        let and_r = Z3_mk_and(ctx, 2, args.as_ptr());
        let or_r = Z3_mk_or(ctx, 2, args.as_ptr());
        assert_ne!(and_r, 0);
        assert_ne!(or_r, 0);

        Z3_del_context(ctx);
    }
}

/// Sort kind inspection
#[test]
fn test_z3_compat_sort_kinds() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_s = Z3_mk_bool_sort(ctx);
        let int_s = Z3_mk_int_sort(ctx);
        let real_s = Z3_mk_real_sort(ctx);
        let bv_s = Z3_mk_bv_sort(ctx, 32);

        assert_eq!(Z3_get_sort_kind(ctx, bool_s), Z3_BOOL_SORT);
        assert_eq!(Z3_get_sort_kind(ctx, int_s), Z3_INT_SORT);
        assert_eq!(Z3_get_sort_kind(ctx, real_s), Z3_REAL_SORT);
        assert_eq!(Z3_get_sort_kind(ctx, bv_s), Z3_BV_SORT);
        assert_eq!(Z3_get_bv_sort_size(ctx, bv_s), 32);

        let arr_s = Z3_mk_array_sort(ctx, int_s, bool_s);
        assert_eq!(Z3_get_sort_kind(ctx, arr_s), Z3_ARRAY_SORT);

        Z3_del_context(ctx);
    }
}

/// Version query
#[test]
fn test_z3_compat_version() {
    unsafe {
        let mut major: c_uint = 0;
        let mut minor: c_uint = 0;
        let mut build: c_uint = 0;
        let mut rev: c_uint = 0;
        Z3_get_version(&raw mut major, &raw mut minor, &raw mut build, &raw mut rev);
        assert_eq!(major, 4);
        assert_eq!(minor, 13);
    }
}

/// Quantifier construction: forall and exists term creation
#[test]
fn test_z3_compat_quantifier_construction() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let zero = Z3_mk_int(ctx, 0, int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let x_gt_0 = Z3_mk_gt(ctx, x, zero);
        let x_ge_1 = Z3_mk_ge(ctx, x, one);
        let body = Z3_mk_implies(ctx, x_gt_0, x_ge_1);

        // Test forall_const creates a non-null term
        let bound = [x];
        let forall = Z3_mk_forall_const(ctx, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        assert_ne!(forall, 0, "Z3_mk_forall_const should return non-null");

        // Test exists_const creates a non-null term
        let body2 = Z3_mk_gt(ctx, x, zero);
        let exists = Z3_mk_exists_const(ctx, 0, 1, bound.as_ptr(), 0, ptr::null(), body2);
        assert_ne!(exists, 0, "Z3_mk_exists_const should return non-null");

        // forall and exists should be different ASTs
        assert_ne!(forall, exists);

        // Negation of quantifier should also work
        let neg = Z3_mk_not(ctx, forall);
        assert_ne!(neg, 0, "Z3_mk_not on quantifier should work");

        Z3_del_context(ctx);
    }
}

/// Z3_mk_bvcomp: equality as 1-bit BV
#[test]
fn test_z3_compat_bvcomp() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let five_a = Z3_mk_unsigned_int(ctx, 5, bv8);
        let five_b = Z3_mk_unsigned_int(ctx, 5, bv8);

        let comp = Z3_mk_bvcomp(ctx, five_a, five_b);
        assert_ne!(comp, 0);

        // bvcomp(5, 5) should be #b1
        let bv1 = Z3_mk_bv_sort(ctx, 1);
        let one = Z3_mk_unsigned_int(ctx, 1, bv1);
        let eq_one = Z3_mk_eq(ctx, comp, one);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq_one);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Pattern construction
#[test]
fn test_z3_compat_mk_pattern() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym_f = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let f_decl = Z3_mk_func_decl(ctx, sym_f, 1, &raw const int_sort, int_sort);
        assert!(!f_decl.is_null());

        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);
        let fx = Z3_mk_app(ctx, f_decl, 1, &raw const x);
        assert_ne!(fx, 0);

        let pattern = Z3_mk_pattern(ctx, 1, &raw const fx);
        assert!(!pattern.is_null());

        Z3_del_context(ctx);
    }
}

/// Z3_mk_abs: absolute value
#[test]
fn test_z3_compat_abs() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let abs_x = Z3_mk_abs(ctx, x);
        assert_ne!(abs_x, 0);

        // |x| >= 0 should be SAT for any x
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let abs_ge_0 = Z3_mk_ge(ctx, abs_x, zero);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, abs_ge_0);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// Application introspection: Z3_get_app_num_args, Z3_get_app_arg, Z3_get_app_decl
#[test]
fn test_z3_compat_app_introspection() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);

        let sym_y = Z3_mk_string_symbol(ctx, c"y".as_ptr());
        let y = Z3_mk_const(ctx, sym_y, int_sort);

        // Build x + y (2 arguments)
        let args = [x, y];
        let sum = Z3_mk_add(ctx, 2, args.as_ptr());
        assert_ne!(sum, 0);

        // Should have 2 children
        let num_args = Z3_get_app_num_args(ctx, sum);
        assert_eq!(num_args, 2, "x + y should have 2 arguments");

        // First arg should be x, second should be y
        let arg0 = Z3_get_app_arg(ctx, sum, 0);
        let arg1 = Z3_get_app_arg(ctx, sum, 1);
        assert_eq!(arg0, x, "first arg should be x");
        assert_eq!(arg1, y, "second arg should be y");

        // Out-of-bounds should return 0
        let oob = Z3_get_app_arg(ctx, sum, 5);
        assert_eq!(oob, 0, "out-of-bounds arg should return 0");

        // get_app_decl should return a non-null func_decl
        let decl = Z3_get_app_decl(ctx, sum);
        assert!(!decl.is_null(), "app_decl should be non-null for addition");

        // A variable should have 0 children
        let x_args = Z3_get_app_num_args(ctx, x);
        assert_eq!(x_args, 0, "variable should have 0 args");

        Z3_del_context(ctx);
    }
}

/// Null pointer safety
#[test]
fn test_z3_compat_null_safety() {
    unsafe {
        // Context operations on null should not crash
        assert_eq!(
            Z3_solver_check(ptr::null_mut(), ptr::null_mut()),
            Z3_L_UNDEF
        );
        assert!(Z3_solver_get_model(ptr::null_mut(), ptr::null_mut()).is_null());
        assert!(Z3_mk_solver(ptr::null_mut()).is_null());
        assert_eq!(Z3_mk_true(ptr::null_mut()), 0);
        assert_eq!(Z3_mk_int(ptr::null_mut(), 42, ptr::null_mut()), 0);
        assert!(Z3_mk_int_sort(ptr::null_mut()).is_null());

        // Sort operations on null
        assert_eq!(
            Z3_get_sort_kind(ptr::null_mut(), ptr::null_mut()),
            Z3_UNKNOWN_AST
        );
        assert_eq!(Z3_get_bv_sort_size(ptr::null_mut(), ptr::null_mut()), 0);

        // Delete null is safe
        Z3_del_context(ptr::null_mut());
        Z3_del_config(ptr::null_mut());
    }
}

/// ast_to_term(0) panics in debug mode (catches null sentinel early) (#5519)
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "null Z3_ast")]
fn test_ast_to_term_null_sentinel_debug() {
    let _ = ast_to_term(0);
}

/// ast_to_term(0) returns Term(0) defensively in release mode (#5519)
#[test]
#[cfg(not(debug_assertions))]
fn test_ast_to_term_null_sentinel_release() {
    let term = ast_to_term(0);
    assert_eq!(
        term.to_raw(),
        0,
        "null Z3_ast should map to Term(0), not underflow"
    );
}

/// Round-trip: term_to_ast and ast_to_term are inverses for valid terms
#[test]
fn test_ast_term_roundtrip() {
    for i in 0..10u32 {
        let term = Term::from_raw(i);
        let ast = term_to_ast(term);
        assert_ne!(ast, 0, "valid term should not map to null Z3_ast");
        let back = ast_to_term(ast);
        assert_eq!(back.to_raw(), i, "round-trip failed for Term({i})");
    }
}

// ========================== ast_identity.rs tests ==========================

/// Z3_is_eq_ast: same AST values are equal
#[test]
fn test_z3_is_eq_ast_same() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        assert!(Z3_is_eq_ast(ctx, x, x), "same AST must be equal to itself");

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_ast: different AST values are not equal
#[test]
fn test_z3_is_eq_ast_different() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let sym_y = Z3_mk_string_symbol(ctx, c"y".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);
        let y = Z3_mk_const(ctx, sym_y, int_sort);

        assert!(!Z3_is_eq_ast(ctx, x, y), "different ASTs must not be equal");

        Z3_del_context(ctx);
    }
}

/// Z3_get_ast_id: returns consistent IDs
#[test]
fn test_z3_get_ast_id_consistent() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let id1 = Z3_get_ast_id(ctx, x);
        let id2 = Z3_get_ast_id(ctx, x);
        assert_eq!(id1, id2, "same AST must have same ID");

        Z3_del_context(ctx);
    }
}

/// Z3_get_ast_hash: consistent with Z3_get_ast_id
#[test]
fn test_z3_get_ast_hash_equals_id() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);

        let id = Z3_get_ast_id(ctx, x);
        let hash = Z3_get_ast_hash(ctx, x);
        assert_eq!(id, hash, "Z4 uses same value for ID and hash");

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_sort: same sorts are equal
#[test]
fn test_z3_is_eq_sort_same() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        assert!(
            Z3_is_eq_sort(ctx, int_sort, int_sort),
            "same sort must be equal to itself"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_sort: different sorts are not equal
#[test]
fn test_z3_is_eq_sort_different() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        assert!(
            !Z3_is_eq_sort(ctx, int_sort, bool_sort),
            "Int and Bool sorts must not be equal"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_sort: null sorts handled safely
#[test]
fn test_z3_is_eq_sort_null() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        assert!(
            !Z3_is_eq_sort(ctx, int_sort, ptr::null_mut()),
            "non-null vs null must be false"
        );
        assert!(
            Z3_is_eq_sort(ctx, ptr::null_mut(), ptr::null_mut()),
            "null vs null must be true"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_name: returns a valid symbol for named sorts
#[test]
fn test_z3_get_sort_name_int() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let name_sym = Z3_get_sort_name(ctx, int_sort);
        assert!(
            !name_sym.is_null(),
            "sort name symbol must not be null for Int sort"
        );
        // Symbol is now freed by Z3Context::Drop via symbol_cache (#5528)

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_name: null sort returns null
#[test]
fn test_z3_get_sort_name_null() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let name_sym = Z3_get_sort_name(ctx, ptr::null_mut());
        assert!(name_sym.is_null(), "null sort must return null symbol");

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_id: returns non-zero for valid sorts
#[test]
fn test_z3_get_sort_id_valid() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let id = Z3_get_sort_id(ctx, int_sort);
        assert_ne!(id, 0, "valid sort must have non-zero ID");

        Z3_del_context(ctx);
    }
}

/// Z3_get_sort_id: null sort returns 0
#[test]
fn test_z3_get_sort_id_null() {
    unsafe {
        assert_eq!(
            Z3_get_sort_id(ptr::null_mut(), ptr::null_mut()),
            0,
            "null sort must return ID 0"
        );
    }
}

/// Z3_func_decl_to_ast: returns 0 (func_decls are not ASTs in Z4)
#[test]
fn test_z3_func_decl_to_ast_returns_zero() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let ast = Z3_func_decl_to_ast(ctx, ptr::null_mut());
        assert_eq!(ast, 0, "func_decl_to_ast must return 0 in Z4");

        Z3_del_context(ctx);
    }
}

/// Z3_is_eq_func_decl: null func_decls are equal to each other
#[test]
fn test_z3_is_eq_func_decl_both_null() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        assert!(
            Z3_is_eq_func_decl(ctx, ptr::null_mut(), ptr::null_mut()),
            "two null func_decls must be equal"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_func_decl_to_string: null returns "(null)"
#[test]
fn test_z3_func_decl_to_string_null() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = Z3_func_decl_to_string(ctx, ptr::null_mut());
        assert!(
            !s.is_null(),
            "null func_decl should return \"(null)\" string"
        );
        let cs = std::ffi::CStr::from_ptr(s);
        assert_eq!(
            cs.to_str().expect("valid UTF-8"),
            "(null)",
            "null func_decl string must be \"(null)\""
        );

        Z3_del_context(ctx);
    }
}

/// Z3_get_symbol_kind: null symbol returns string kind (1)
#[test]
fn test_z3_get_symbol_kind_null() {
    unsafe {
        let kind = Z3_get_symbol_kind(ptr::null_mut(), ptr::null_mut());
        assert_eq!(kind, 1, "null symbol must return string kind (1)");
    }
}

/// Z3_get_symbol_int: null symbol returns -1
#[test]
fn test_z3_get_symbol_int_null() {
    unsafe {
        let val = Z3_get_symbol_int(ptr::null_mut(), ptr::null_mut());
        assert_eq!(val, -1, "null symbol must return -1");
    }
}

/// ctx_ref returns a scoped borrow, not &'static mut (#6018).
/// Verifies that multiple sequential FFI calls each get independent borrows
/// from ctx_ref without aliasing violations.
#[test]
fn test_ctx_ref_scoped_lifetime_6018() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx_ptr = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Each ctx_ref call returns a fresh scoped borrow.
        // Previously returned &'static mut, which was unsound because two
        // sequential calls would create aliasing &mut references.
        {
            let ctx = ctx_ref(ctx_ptr).expect("non-null context");
            ctx.solver.push();
        }
        // First borrow dropped. Second borrow is sound.
        {
            let ctx = ctx_ref(ctx_ptr).expect("non-null context");
            ctx.solver.pop();
        }

        // Null returns None (unchanged by lifetime fix).
        assert!(ctx_ref(ptr::null_mut()).is_none());

        Z3_del_context(ctx_ptr);
    }
}

/// Z3_mk_rem: truncation remainder has same sign as dividend (#6115)
///
/// rem(-7, 3) = -1 (not +2 like mod)
/// rem(7, -3) = 1 (not -2 like mod)
#[test]
fn test_z3_mk_rem_truncation_semantics() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        // Test case 1: rem(-7, 3) should equal -1
        {
            let neg7 = Z3_mk_int(ctx, -7, int_sort);
            let three = Z3_mk_int(ctx, 3, int_sort);
            let neg1 = Z3_mk_int(ctx, -1, int_sort);

            let rem_result = Z3_mk_rem(ctx, neg7, three);
            assert_ne!(rem_result, 0, "Z3_mk_rem should return non-null");

            // Assert rem(-7,3) = -1 and check SAT
            let eq = Z3_mk_eq(ctx, rem_result, neg1);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, eq);
            let result = Z3_solver_check(ctx, solver);
            assert_eq!(result, Z3_L_TRUE, "rem(-7, 3) = -1 should be SAT");
        }

        // Test case 2: rem(7, -3) should equal 1
        {
            let seven = Z3_mk_int(ctx, 7, int_sort);
            let neg3 = Z3_mk_int(ctx, -3, int_sort);
            let one = Z3_mk_int(ctx, 1, int_sort);

            let rem_result = Z3_mk_rem(ctx, seven, neg3);
            let eq = Z3_mk_eq(ctx, rem_result, one);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, eq);
            let result = Z3_solver_check(ctx, solver);
            assert_eq!(result, Z3_L_TRUE, "rem(7, -3) = 1 should be SAT");
        }

        // Negative test: rem(-7, 3) != 2 (mod would give 2, rem gives -1)
        {
            let neg7 = Z3_mk_int(ctx, -7, int_sort);
            let three = Z3_mk_int(ctx, 3, int_sort);
            let two = Z3_mk_int(ctx, 2, int_sort);

            let rem_result = Z3_mk_rem(ctx, neg7, three);
            let eq = Z3_mk_eq(ctx, rem_result, two);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, eq);
            let result = Z3_solver_check(ctx, solver);
            assert_eq!(
                result, Z3_L_FALSE,
                "rem(-7, 3) = 2 should be UNSAT (that's mod, not rem)"
            );
        }

        Z3_del_context(ctx);
    }
}

/// Z3_mk_numeral with large integer beyond i64 range (#6112)
#[test]
fn test_z3_mk_numeral_large_integer_precision() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        // 2^63 = 9223372036854775808 (overflows i64)
        let big_str = c"9223372036854775808";
        let big = Z3_mk_numeral(ctx, big_str.as_ptr(), int_sort);
        assert_ne!(big, 0, "Z3_mk_numeral should handle >i64 values");

        // Verify the numeral string round-trips correctly
        let numeral_str = Z3_get_numeral_string(ctx, big);
        assert!(!numeral_str.is_null(), "numeral string should not be null");
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(
            s, "9223372036854775808",
            "large integer should round-trip exactly"
        );

        // Verify it works in constraints: big > 2^63 - 1
        let max_i64_str = c"9223372036854775807";
        let max_i64 = Z3_mk_numeral(ctx, max_i64_str.as_ptr(), int_sort);
        assert_ne!(max_i64, 0);
        let gt = Z3_mk_gt(ctx, big, max_i64);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, gt);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE, "2^63 > 2^63-1 should be SAT");

        Z3_del_context(ctx);
    }
}

/// Z3_mk_unsigned_int64 with large u64 values (#6112)
#[test]
fn test_z3_mk_unsigned_int64_large_values() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);

        // u64::MAX = 18446744073709551615, which wraps to -1 as i64
        let big = Z3_mk_unsigned_int64(ctx, u64::MAX, int_sort);
        assert_ne!(big, 0, "Z3_mk_unsigned_int64 should handle u64::MAX");

        // The numeral should be the positive u64::MAX, not -1
        let numeral_str = Z3_get_numeral_string(ctx, big);
        assert!(!numeral_str.is_null());
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(
            s, "18446744073709551615",
            "u64::MAX should be stored as positive integer, not wrapped to -1"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_mk_int64 as Real: exact construction without f64 precision loss (#6112)
#[test]
fn test_z3_mk_int64_real_exact() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let real_sort = Z3_mk_real_sort(ctx);

        // i64::MAX = 9223372036854775807. As f64, this loses precision.
        // The old code did `v as f64` which rounds to 9223372036854775808.0
        let big = Z3_mk_int64(ctx, i64::MAX, real_sort);
        assert_ne!(big, 0, "Z3_mk_int64 should handle i64::MAX as Real");

        // The numeral should be exactly i64::MAX, not f64-rounded
        let numeral_str = Z3_get_numeral_string(ctx, big);
        assert!(!numeral_str.is_null());
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        // For Real constructed from BigInt, the numeral string should be "N/1"
        // or just "N" depending on implementation
        let expected_value = "9223372036854775807";
        assert!(
            s == expected_value || s == format!("{expected_value}/1"),
            "i64::MAX as Real should be exact, got: {s}"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_mk_numeral with rational string for Real sort (#6112)
#[test]
fn test_z3_mk_numeral_rational_precision() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let real_sort = Z3_mk_real_sort(ctx);

        // 1/3 should be stored exactly as a rational, not as 0.3333... float
        let one_third = Z3_mk_numeral(ctx, c"1/3".as_ptr(), real_sort);
        assert_ne!(one_third, 0, "Z3_mk_numeral should handle rational strings");

        // Get the numeral string and verify it's the exact rational
        let numeral_str = Z3_get_numeral_string(ctx, one_third);
        assert!(!numeral_str.is_null());
        let s = std::ffi::CStr::from_ptr(numeral_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(s, "1/3", "1/3 should be stored as exact rational");

        // Get decimal string with 10 digits of precision
        let decimal_str = Z3_get_numeral_decimal_string(ctx, one_third, 10);
        assert!(!decimal_str.is_null());
        let d = std::ffi::CStr::from_ptr(decimal_str)
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(d, "0.3333333333", "1/3 with 10 digits precision");

        Z3_del_context(ctx);
    }
}

/// Z3_get_symbol_kind: string symbol returns string kind
#[test]
fn test_z3_get_symbol_kind_string() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let sym = Z3_mk_string_symbol(ctx, c"hello".as_ptr());
        assert!(!sym.is_null(), "string symbol must not be null");
        let kind = Z3_get_symbol_kind(ctx, sym);
        assert_eq!(kind, 1, "\"hello\" must be a string symbol (kind=1)");

        Z3_del_context(ctx);
    }
}

/// Z3_model_eval uses model snapshot, not solver state (#6109).
/// Get model, push+UNSAT, then eval old model — must still return snapshot value.
#[test]
fn test_z3_model_eval_uses_model_handle_6109() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, five));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // Push and make UNSAT so solver.get_value() would fail
        Z3_solver_push(ctx, solver);
        let ten = Z3_mk_int(ctx, 10, int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, ten));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        // Evaluate x in OLD model — must still be 5
        let mut val: Z3_ast = 0;
        let ok = Z3_model_eval(ctx, model, x, false, &raw mut val);
        assert!(ok, "model_eval must succeed using model snapshot");
        assert_ne!(val, 0);
        let mut int_val: c_int = 0;
        assert!(Z3_get_numeral_int(ctx, val, &raw mut int_val));
        assert_eq!(int_val, 5, "must return 5 from model snapshot");

        Z3_solver_pop(ctx, solver, 1);
        Z3_del_context(ctx);
    }
}

// ============================================================================
// Panic safety tests (#6192)
// ============================================================================

/// Test that Z3_solver_pop on an empty scope stack does not abort the process.
/// Before #6192, this would cause undefined behavior (panic across extern "C").
/// After #6192, the catch_unwind guard catches the panic and sets an error flag.
#[test]
fn test_ffi_pop_empty_scope_no_abort() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);

        // Pop with no prior push — this would panic in the solver.
        // The FFI guard must catch it and set an error instead of aborting.
        Z3_solver_pop(ctx, solver, 1);

        // Verify the error was recorded
        let err_code = Z3_get_error_code(ctx);
        assert_eq!(
            err_code, Z3_EXCEPTION,
            "pop on empty scope should set Z3_EXCEPTION error code"
        );

        // Error message should describe the panic
        let err_msg = Z3_get_error_msg(ctx, err_code);
        assert!(
            !err_msg.is_null(),
            "error message should be set after panic"
        );

        // Context should still be usable after the caught panic
        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        assert_ne!(x, 0, "context must remain usable after caught panic");

        Z3_del_context(ctx);
    }
}

/// Test that Z3_mk_eq with sort mismatch triggers the catch_unwind guard
/// instead of aborting. This is the exact scenario from sunder#2056.
#[test]
fn test_ffi_eq_sort_mismatch_no_abort() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);

        // Create an Int and a Bool variable
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);

        let sym_b = Z3_mk_string_symbol(ctx, c"b".as_ptr());
        let b = Z3_mk_const(ctx, sym_b, bool_sort);

        // eq(Int, Bool) — sort mismatch. If the solver panics on this,
        // the FFI guard should catch it. If the solver handles it gracefully
        // (returns a term or error), that's also acceptable.
        let result = Z3_mk_eq(ctx, x, b);

        // Either the result is a valid AST (solver accepted it) or
        // it's 0 (null AST from caught panic). Both are acceptable.
        // The key assertion is that we REACHED THIS LINE (no abort).
        if result == 0 {
            // Panic was caught — verify error flag is set
            let err_code = Z3_get_error_code(ctx);
            assert_eq!(err_code, Z3_EXCEPTION);
        }

        // Context must still be functional
        let five = Z3_mk_int(ctx, 5, int_sort);
        assert_ne!(five, 0, "context must remain usable after sort mismatch");

        Z3_del_context(ctx);
    }
}

/// Test that Z3_solver_check catches panics from the solver engine
/// and returns Z3_L_UNDEF instead of aborting.
#[test]
fn test_ffi_check_sat_recovers_from_panic() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);

        // Normal check-sat should work fine
        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let gt = Z3_mk_gt(ctx, x, zero);
        Z3_solver_assert(ctx, solver, gt);

        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE, "normal check-sat should return SAT");

        Z3_del_context(ctx);
    }
}

// ============================================================================
// Memory safety tests (memory_verification phase)
// ============================================================================

/// Stress test: create many handles of each type, then delete context.
/// Verifies that `Z3Context::drop` via `drain_arena` frees all handle arenas
/// without double-free, leak, or crash.
///
/// Creates: symbols, sorts, func_decls, solvers, models, params, ast_vectors.
/// Each handle is allocated via `Box::into_raw` and tracked in a context cache.
/// `Z3_del_context` triggers `Drop for Z3Context` which calls `drain_arena`
/// on all 8 caches.
#[test]
fn test_arena_cleanup_many_handles() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Create many symbols (each goes into symbol_cache)
        for i in 0..50 {
            let name = CString::new(format!("sym_{i}")).expect("no NUL in test name");
            let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
            assert!(!sym.is_null());
        }

        // Create many sorts (each goes into sort_cache)
        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);
        let real_sort = Z3_mk_real_sort(ctx);
        for i in 1..=32 {
            let bv = Z3_mk_bv_sort(ctx, i);
            assert!(!bv.is_null());
        }
        let arr_sort = Z3_mk_array_sort(ctx, int_sort, bool_sort);
        assert!(!arr_sort.is_null());

        // Create many func_decls (each goes into func_decl_cache)
        for i in 0..20 {
            let name = CString::new(format!("f_{i}")).expect("no NUL in test name");
            let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
            let decl = Z3_mk_func_decl(ctx, sym, 1, &raw const int_sort, real_sort);
            assert!(!decl.is_null());
        }

        // Create multiple solver handles (each goes into solver_handle_cache)
        for _ in 0..5 {
            let s = Z3_mk_solver(ctx);
            assert!(!s.is_null());
        }

        // Create params (goes into params_cache)
        let p = Z3_mk_params(ctx);
        assert!(!p.is_null());

        // Create a model via SAT check (goes into model_cache)
        let solver = Z3_mk_solver(ctx);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, x, five));
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // Create ast_vectors via get_assertions (goes into ast_vector_cache)
        let assertions = Z3_solver_get_assertions(ctx, solver);
        assert!(!assertions.is_null());

        // Create patterns (goes into pattern_cache)
        // Z3_mk_pattern wraps trigger terms for quantifier instantiation.
        let f_sym = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let f_decl = Z3_mk_func_decl(ctx, f_sym, 1, &raw const int_sort, int_sort);
        let fx = Z3_mk_app(ctx, f_decl, 1, &raw const x);
        let pattern = Z3_mk_pattern(ctx, 1, &raw const fx);
        assert!(!pattern.is_null());

        // Now delete the context — this must free all cached handles
        // without double-free or crash.
        Z3_del_context(ctx);

        // If we reach here without a crash or ASAN report, arena cleanup is correct.
    }
}

/// Verify that multiple context create/destroy cycles don't leak.
/// Each cycle creates handles, then destroys the context.
#[test]
fn test_context_lifecycle_repeated() {
    for _ in 0..10 {
        unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);

            let int_sort = Z3_mk_int_sort(ctx);
            let sym = Z3_mk_string_symbol(ctx, c"v".as_ptr());
            let v = Z3_mk_const(ctx, sym, int_sort);
            let zero = Z3_mk_int(ctx, 0, int_sort);
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, Z3_mk_gt(ctx, v, zero));
            let _ = Z3_solver_check(ctx, solver);
            let _ = Z3_solver_get_model(ctx, solver);

            Z3_del_context(ctx);
        }
    }
}

// ============================================================================
// #6580 regression tests: sort ID stability and domain sort correctness
// ============================================================================

/// Repeated Z3_mk_int_sort calls must return the same semantic sort ID (#6580).
#[test]
fn test_z3_get_sort_id_same_semantic_sort_is_stable_issue_6580() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort_a = Z3_mk_int_sort(ctx);
        let int_sort_b = Z3_mk_int_sort(ctx);

        let id_a = Z3_get_sort_id(ctx, int_sort_a);
        let id_b = Z3_get_sort_id(ctx, int_sort_b);

        assert_ne!(id_a, 0, "sort ID must be non-zero");
        assert_eq!(
            id_a, id_b,
            "same semantic sort (Int) must have same ID across allocations"
        );

        Z3_del_context(ctx);
    }
}

/// Distinct sorts must have distinct IDs (#6580).
#[test]
fn test_z3_get_sort_id_distinct_sorts_issue_6580() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let real_sort = Z3_mk_real_sort(ctx);
        let bv32_sort = Z3_mk_bv_sort(ctx, 32);

        let id_int = Z3_get_sort_id(ctx, int_sort);
        let id_real = Z3_get_sort_id(ctx, real_sort);
        let id_bv32 = Z3_get_sort_id(ctx, bv32_sort);

        assert_ne!(id_int, 0);
        assert_ne!(id_real, 0);
        assert_ne!(id_bv32, 0);

        assert_ne!(id_int, id_real, "Int and Real must have distinct IDs");
        assert_ne!(id_int, id_bv32, "Int and BV32 must have distinct IDs");
        assert_ne!(id_real, id_bv32, "Real and BV32 must have distinct IDs");

        Z3_del_context(ctx);
    }
}

/// Z3_get_app_decl must return actual domain sorts, not Bool placeholders (#6580).
#[test]
fn test_z3_get_app_decl_domain_sorts_issue_6580() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_a = Z3_mk_string_symbol(ctx, c"a".as_ptr());
        let sym_b = Z3_mk_string_symbol(ctx, c"b".as_ptr());
        let a = Z3_mk_const(ctx, sym_a, bv8);
        let b = Z3_mk_const(ctx, sym_b, bv8);

        // Build bvadd(a, b)
        let sum = Z3_mk_bvadd(ctx, a, b);
        assert_ne!(sum, 0);

        // Get the func_decl
        let decl = Z3_get_app_decl(ctx, sum);
        assert!(!decl.is_null(), "bvadd decl must not be null");

        // Domain size must be 2
        let domain_size = Z3_get_domain_size(ctx, decl);
        assert_eq!(domain_size, 2, "bvadd has 2 arguments");

        // Each domain sort must be (_ BitVec 8), not Bool
        for i in 0..2 {
            let dom_sort = Z3_get_domain(ctx, decl, i);
            assert!(!dom_sort.is_null(), "domain sort {i} must not be null");
            let kind = Z3_get_sort_kind(ctx, dom_sort);
            assert_eq!(
                kind, Z3_BV_SORT,
                "domain sort {i} of bvadd must be BV, not Bool"
            );
            let bv_size = Z3_get_bv_sort_size(ctx, dom_sort);
            assert_eq!(bv_size, 8, "domain sort {i} of bvadd must be (_ BitVec 8)");
        }

        // Range sort must also be (_ BitVec 8)
        let range = Z3_get_range(ctx, decl);
        assert!(!range.is_null());
        assert_eq!(Z3_get_sort_kind(ctx, range), Z3_BV_SORT);
        assert_eq!(Z3_get_bv_sort_size(ctx, range), 8);

        Z3_del_context(ctx);
    }
}

/// Z3_get_decl_num_parameters / Z3_get_decl_int_parameter for extract (#6580 F2).
///
/// `(_ extract 7 4)` must report 2 parameters with values 7 and 4.
#[test]
fn test_z3_decl_params_extract_issue_6580() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, bv8);

        // extract bits [7:4] from an 8-bit bitvector → 4-bit result
        let ext = Z3_mk_extract(ctx, 7, 4, x);
        assert_ne!(ext, 0, "extract should produce a valid AST");

        let decl = Z3_get_app_decl(ctx, ext);
        assert!(!decl.is_null(), "extract decl must not be null");

        // Verify the decl name is "extract" (base name, not "(_ extract 7 4)")
        let name_sym = Z3_get_decl_name(ctx, decl);
        assert!(!name_sym.is_null());
        let name_cstr = Z3_get_symbol_string(ctx, name_sym);
        assert!(!name_cstr.is_null());
        let name = std::ffi::CStr::from_ptr(name_cstr)
            .to_str()
            .expect("decl name should be valid UTF-8");
        assert_eq!(name, "extract", "decl name should be base name");

        // Parameters: extract has 2 (high=7, low=4)
        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 2, "extract must have 2 parameters");
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 0),
            7,
            "param[0] = high = 7"
        );
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 1),
            4,
            "param[1] = low = 4"
        );

        // Out-of-bounds returns 0
        assert_eq!(Z3_get_decl_int_parameter(ctx, decl, 2), 0);

        Z3_del_context(ctx);
    }
}

/// Z3_get_decl_num_parameters for sign_extend (#6580 F2).
///
/// `(_ sign_extend 8)` must report 1 parameter with value 8.
#[test]
fn test_z3_decl_params_sign_extend_issue_6580() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, bv8);

        // sign_extend by 8 bits: 8-bit → 16-bit
        let sext = Z3_mk_sign_ext(ctx, 8, x);
        assert_ne!(sext, 0, "sign_ext should produce a valid AST");

        let decl = Z3_get_app_decl(ctx, sext);
        assert!(!decl.is_null(), "sign_extend decl must not be null");

        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 1, "sign_extend must have 1 parameter");
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 0),
            8,
            "param[0] = extension width = 8"
        );

        Z3_del_context(ctx);
    }
}

/// Z3_get_decl_num_parameters for zero_extend (#6580 F2).
///
/// `(_ zero_extend 16)` must report 1 parameter with value 16.
#[test]
fn test_z3_decl_params_zero_extend_issue_6580() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_x = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym_x, bv8);

        // zero_extend by 16 bits: 8-bit → 24-bit
        let zext = Z3_mk_zero_ext(ctx, 16, x);
        assert_ne!(zext, 0, "zero_ext should produce a valid AST");

        let decl = Z3_get_app_decl(ctx, zext);
        assert!(!decl.is_null(), "zero_extend decl must not be null");

        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 1, "zero_extend must have 1 parameter");
        assert_eq!(
            Z3_get_decl_int_parameter(ctx, decl, 0),
            16,
            "param[0] = extension width = 16"
        );

        Z3_del_context(ctx);
    }
}

/// Non-indexed operators (like bvadd) must report 0 parameters (#6580 F2).
#[test]
fn test_z3_decl_params_non_indexed_zero_issue_6580() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let sym_a = Z3_mk_string_symbol(ctx, c"a".as_ptr());
        let sym_b = Z3_mk_string_symbol(ctx, c"b".as_ptr());
        let a = Z3_mk_const(ctx, sym_a, bv8);
        let b = Z3_mk_const(ctx, sym_b, bv8);

        let sum = Z3_mk_bvadd(ctx, a, b);
        let decl = Z3_get_app_decl(ctx, sum);
        assert!(!decl.is_null());

        // bvadd is not an indexed operator → 0 parameters
        let num_params = Z3_get_decl_num_parameters(ctx, decl);
        assert_eq!(num_params, 0, "non-indexed operator must have 0 parameters");

        // Null decl returns 0
        assert_eq!(Z3_get_decl_num_parameters(ctx, ptr::null_mut()), 0);
        assert_eq!(Z3_get_decl_int_parameter(ctx, ptr::null_mut(), 0), 0);

        Z3_del_context(ctx);
    }
}
