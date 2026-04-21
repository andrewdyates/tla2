// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Minimal Z3 C API consumer for z4-ffi header compatibility test (#4990).
//
// This program exercises the core Z3 API workflow that external consumers
// (Lean, KLEE, Seahorn) use: create context, declare variables, assert
// constraints, check satisfiability, inspect model. If this compiles and
// links against libz4_ffi, the header is compatible.

#include "z4_z3_compat.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

// Core workflow: create, assert, check-sat, model, cleanup
static int test_basic_sat(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Declare integer variable x
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);

    // Assert x > 0
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast x_gt_0 = Z3_mk_gt(ctx, x, zero);

    // Assert x < 10
    Z3_ast ten = Z3_mk_int(ctx, 10, int_sort);
    Z3_ast x_lt_10 = Z3_mk_lt(ctx, x, ten);

    Z3_solver solver = Z3_mk_solver(ctx);

    Z3_solver_assert(ctx, solver, x_gt_0);
    Z3_solver_assert(ctx, solver, x_lt_10);

    int result = Z3_solver_check(ctx, solver);
    assert(result == Z3_L_TRUE);

    // Get model and inspect
    Z3_model model = Z3_solver_get_model(ctx, solver);
    assert(model != NULL);

    unsigned int num_consts = Z3_model_get_num_consts(ctx, model);
    (void)num_consts; // may be 0 or 1 depending on implementation

    Z3_string model_str = Z3_model_to_string(ctx, model);
    assert(model_str != NULL);
    printf("Model: %s\n", model_str);

    Z3_del_context(ctx);
    return 0;
}

// Arithmetic and boolean operations
static int test_arithmetic(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
    Z3_ast three = Z3_mk_int(ctx, 3, int_sort);

    // 2 + 3
    Z3_ast args[2] = { two, three };
    Z3_ast sum = Z3_mk_add(ctx, 2, args);
    assert(sum != 0);

    // 2 * 3
    Z3_ast prod = Z3_mk_mul(ctx, 2, args);
    assert(prod != 0);

    // 2 ^ 3
    Z3_ast power = Z3_mk_power(ctx, two, three);
    assert(power != 0);

    // Numeral inspection
    assert(Z3_is_numeral_ast(ctx, two));

    unsigned int val = 0;
    bool ok = Z3_get_numeral_uint(ctx, two, &val);
    assert(ok);
    assert(val == 2);

    Z3_del_context(ctx);
    return 0;
}

// Sort and symbol inspection
static int test_sorts_and_symbols(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Sorts
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort real_sort = Z3_mk_real_sort(ctx);
    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);

    assert(Z3_get_sort_kind(ctx, bool_sort) == Z3_BOOL_SORT);
    assert(Z3_get_sort_kind(ctx, int_sort) == Z3_INT_SORT);
    assert(Z3_get_sort_kind(ctx, real_sort) == Z3_REAL_SORT);
    assert(Z3_get_sort_kind(ctx, bv8) == Z3_BV_SORT);

    assert(Z3_is_eq_sort(ctx, int_sort, Z3_mk_int_sort(ctx)));
    assert(!Z3_is_eq_sort(ctx, int_sort, bool_sort));

    // Symbols
    Z3_symbol str_sym = Z3_mk_string_symbol(ctx, "hello");
    assert(Z3_get_symbol_kind(ctx, str_sym) == Z3_STRING_SYMBOL);

    Z3_symbol int_sym = Z3_mk_int_symbol(ctx, 42);
    assert(Z3_get_symbol_kind(ctx, int_sym) == Z3_INT_SYMBOL);
    assert(Z3_get_symbol_int(ctx, int_sym) == 42);

    Z3_del_context(ctx);
    return 0;
}

// Boolean and bitvector operations
static int test_bv_and_bool(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Boolean
    Z3_ast t = Z3_mk_true(ctx);
    Z3_ast f = Z3_mk_false(ctx);
    assert(Z3_get_bool_value(ctx, t) == Z3_L_TRUE);
    assert(Z3_get_bool_value(ctx, f) == Z3_L_FALSE);

    Z3_ast not_t = Z3_mk_not(ctx, t);
    assert(not_t != 0);

    // Bitvector
    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    assert(Z3_get_bv_sort_size(ctx, bv8) == 8);

    Z3_symbol a_sym = Z3_mk_string_symbol(ctx, "a");
    Z3_symbol b_sym = Z3_mk_string_symbol(ctx, "b");
    Z3_ast a = Z3_mk_const(ctx, a_sym, bv8);
    Z3_ast b = Z3_mk_const(ctx, b_sym, bv8);

    Z3_ast bvand = Z3_mk_bvand(ctx, a, b);
    Z3_ast bvor = Z3_mk_bvor(ctx, a, b);
    Z3_ast bvxor = Z3_mk_bvxor(ctx, a, b);
    Z3_ast bvadd = Z3_mk_bvadd(ctx, a, b);
    assert(bvand != 0);
    assert(bvor != 0);
    assert(bvxor != 0);
    assert(bvadd != 0);

    Z3_del_context(ctx);
    return 0;
}

// Error handling
static int test_error_handling(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    unsigned int err = Z3_get_error_code(ctx);
    assert(err == Z3_OK);

    Z3_string msg = Z3_get_error_msg(ctx, Z3_OK);
    // msg may be NULL or a string, both acceptable
    (void)msg;

    Z3_del_context(ctx);
    return 0;
}

int main(void) {
    printf("z4-ffi C consumer test (#4990)\n");

    test_basic_sat();
    printf("  PASS: basic_sat\n");

    test_arithmetic();
    printf("  PASS: arithmetic\n");

    test_sorts_and_symbols();
    printf("  PASS: sorts_and_symbols\n");

    test_bv_and_bool();
    printf("  PASS: bv_and_bool\n");

    test_error_handling();
    printf("  PASS: error_handling\n");

    printf("All 5 C consumer tests passed.\n");
    return 0;
}
