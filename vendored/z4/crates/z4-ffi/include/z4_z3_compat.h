// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Z4 Z3-Compatible C API Header
//
// Drop-in replacement for a subset of z3.h (Z3 C API).
// Link against libz4_ffi (cdylib or staticlib) to use.
//
// Functions covering: context, solver, sorts, terms, arithmetic,
// bitvectors, arrays, quantifiers, model, AST inspection, error handling,
// and parsing.

#ifndef Z4_Z3_COMPAT_H
#define Z4_Z3_COMPAT_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// Opaque Types
// ============================================================================

typedef void* Z3_context;
typedef void* Z3_config;
typedef void* Z3_sort;
typedef void* Z3_func_decl;
typedef void* Z3_solver;
typedef void* Z3_model;
typedef void* Z3_symbol;
typedef void* Z3_params;
typedef void* Z3_ast_vector;
typedef void* Z3_pattern;

// Z3_ast is a 64-bit handle (not a pointer)
typedef uint64_t Z3_ast;

// Z3 string type
typedef const char* Z3_string;

// ============================================================================
// Constants
// ============================================================================

// Z3_lbool
#define Z3_L_FALSE (-1)
#define Z3_L_UNDEF 0
#define Z3_L_TRUE  1

// Z3_sort_kind
#define Z3_BOOL_SORT          1
#define Z3_INT_SORT           2
#define Z3_REAL_SORT          3
#define Z3_BV_SORT            4
#define Z3_ARRAY_SORT         5
#define Z3_UNINTERPRETED_SORT 6

// Z3_ast_kind
#define Z3_NUMERAL_AST    0
#define Z3_APP_AST        1
#define Z3_VAR_AST        2
#define Z3_QUANTIFIER_AST 3
#define Z3_UNKNOWN_AST    1000

// Z3_symbol_kind
#define Z3_INT_SYMBOL    0
#define Z3_STRING_SYMBOL 1

// Z3_error_code
#define Z3_OK               0
#define Z3_SORT_ERROR       1
#define Z3_IOB              2
#define Z3_INVALID_ARG      3
#define Z3_PARSER_ERROR     4
#define Z3_NO_PARSER        5
#define Z3_INVALID_PATTERN  6
#define Z3_MEMOUT_FAIL      7
#define Z3_FILE_ACCESS_ERROR 8
#define Z3_INTERNAL_FATAL   9
#define Z3_INVALID_USAGE    10
#define Z3_DEC_REF_ERROR    11
#define Z3_EXCEPTION        12

// ============================================================================
// Config & Context
// ============================================================================

Z3_config    Z3_mk_config(void);
void         Z3_del_config(Z3_config c);
void         Z3_set_param_value(Z3_config c, Z3_string param_id, Z3_string param_value);
Z3_context   Z3_mk_context(Z3_config c);
Z3_context   Z3_mk_context_rc(Z3_config c);
void         Z3_del_context(Z3_context c);

// ============================================================================
// Version
// ============================================================================

void Z3_get_version(unsigned int* major, unsigned int* minor,
                    unsigned int* build_number, unsigned int* revision_number);

// ============================================================================
// Reference Counting (no-op in Z4)
// ============================================================================

void Z3_inc_ref(Z3_context c, Z3_ast a);
void Z3_dec_ref(Z3_context c, Z3_ast a);

// ============================================================================
// Interrupt
// ============================================================================

void Z3_interrupt(Z3_context c);

// ============================================================================
// Symbols
// ============================================================================

Z3_symbol    Z3_mk_int_symbol(Z3_context c, int i);
Z3_symbol    Z3_mk_string_symbol(Z3_context c, Z3_string s);
Z3_string    Z3_get_symbol_string(Z3_context c, Z3_symbol s);
unsigned int Z3_get_symbol_kind(Z3_context c, Z3_symbol s);
int          Z3_get_symbol_int(Z3_context c, Z3_symbol s);

// ============================================================================
// Sorts
// ============================================================================

Z3_sort      Z3_mk_bool_sort(Z3_context c);
Z3_sort      Z3_mk_int_sort(Z3_context c);
Z3_sort      Z3_mk_real_sort(Z3_context c);
Z3_sort      Z3_mk_bv_sort(Z3_context c, unsigned int sz);
Z3_sort      Z3_mk_array_sort(Z3_context c, Z3_sort domain, Z3_sort range);
Z3_sort      Z3_mk_uninterpreted_sort(Z3_context c, Z3_symbol s);
unsigned int Z3_get_sort_kind(Z3_context c, Z3_sort t);
unsigned int Z3_get_bv_sort_size(Z3_context c, Z3_sort t);
Z3_sort      Z3_get_array_sort_domain(Z3_context c, Z3_sort t);
Z3_sort      Z3_get_array_sort_range(Z3_context c, Z3_sort t);
Z3_string    Z3_sort_to_string(Z3_context c, Z3_sort s);
Z3_symbol    Z3_get_sort_name(Z3_context c, Z3_sort s);
bool         Z3_is_eq_sort(Z3_context c, Z3_sort s1, Z3_sort s2);
unsigned int Z3_get_sort_id(Z3_context c, Z3_sort s);

// ============================================================================
// Terms: Constants, Functions, Numerals, Boolean
// ============================================================================

Z3_func_decl Z3_mk_func_decl(Z3_context c, Z3_symbol s, unsigned int domain_size,
                              const Z3_sort* domain, Z3_sort range);
Z3_ast       Z3_mk_const(Z3_context c, Z3_symbol s, Z3_sort ty);
Z3_ast       Z3_mk_fresh_const(Z3_context c, Z3_string prefix, Z3_sort ty);
Z3_ast       Z3_mk_app(Z3_context c, Z3_func_decl d, unsigned int num_args,
                        const Z3_ast* args);

Z3_ast       Z3_mk_numeral(Z3_context c, Z3_string numeral, Z3_sort ty);
Z3_ast       Z3_mk_int(Z3_context c, int v, Z3_sort ty);
Z3_ast       Z3_mk_unsigned_int(Z3_context c, unsigned int v, Z3_sort ty);
Z3_ast       Z3_mk_int64(Z3_context c, int64_t v, Z3_sort ty);
Z3_ast       Z3_mk_unsigned_int64(Z3_context c, uint64_t v, Z3_sort ty);
Z3_ast       Z3_mk_real(Z3_context c, int num, int den);

Z3_ast       Z3_mk_true(Z3_context c);
Z3_ast       Z3_mk_false(Z3_context c);
Z3_ast       Z3_mk_eq(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast       Z3_mk_distinct(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_not(Z3_context c, Z3_ast a);
Z3_ast       Z3_mk_ite(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3);
Z3_ast       Z3_mk_iff(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_implies(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_xor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_and(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_or(Z3_context c, unsigned int num_args, const Z3_ast* args);

// ============================================================================
// Arithmetic
// ============================================================================

Z3_ast       Z3_mk_add(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_mul(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_sub(Z3_context c, unsigned int num_args, const Z3_ast* args);
Z3_ast       Z3_mk_unary_minus(Z3_context c, Z3_ast arg);
Z3_ast       Z3_mk_div(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast       Z3_mk_mod(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast       Z3_mk_rem(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast       Z3_mk_abs(Z3_context c, Z3_ast arg);
Z3_ast       Z3_mk_power(Z3_context c, Z3_ast arg1, Z3_ast arg2);

Z3_ast       Z3_mk_lt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_le(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_gt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_ge(Z3_context c, Z3_ast t1, Z3_ast t2);

Z3_ast       Z3_mk_int2real(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_real2int(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_is_int(Z3_context c, Z3_ast t1);

// ============================================================================
// Arrays
// ============================================================================

Z3_ast       Z3_mk_select(Z3_context c, Z3_ast a, Z3_ast i);
Z3_ast       Z3_mk_store(Z3_context c, Z3_ast a, Z3_ast i, Z3_ast v);
Z3_ast       Z3_mk_const_array(Z3_context c, Z3_sort domain, Z3_ast v);

// ============================================================================
// Bitvectors
// ============================================================================

// Binary BV operations
Z3_ast       Z3_mk_bvand(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvxor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvadd(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsub(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvmul(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvudiv(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsdiv(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvurem(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsrem(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsmod(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvshl(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvlshr(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvashr(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvnand(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvnor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvxnor(Z3_context c, Z3_ast t1, Z3_ast t2);

// BV comparison operations
Z3_ast       Z3_mk_bvult(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvslt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvule(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsle(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvugt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvuge(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsgt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsge(Z3_context c, Z3_ast t1, Z3_ast t2);

// BV unary operations
Z3_ast       Z3_mk_bvnot(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_bvneg(Z3_context c, Z3_ast t1);

// BV width-changing operations
Z3_ast       Z3_mk_concat(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_extract(Z3_context c, unsigned int high, unsigned int low, Z3_ast t1);
Z3_ast       Z3_mk_sign_ext(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_zero_ext(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_repeat(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_rotate_left(Z3_context c, unsigned int i, Z3_ast t1);
Z3_ast       Z3_mk_rotate_right(Z3_context c, unsigned int i, Z3_ast t1);

// BV-Int conversions
Z3_ast       Z3_mk_bv2int(Z3_context c, Z3_ast t1, bool is_signed);
Z3_ast       Z3_mk_int2bv(Z3_context c, unsigned int n, Z3_ast t1);

// BV overflow/underflow checks
Z3_ast       Z3_mk_bvadd_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast       Z3_mk_bvadd_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsub_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvsub_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast       Z3_mk_bvsdiv_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast       Z3_mk_bvneg_no_overflow(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_bvmul_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast       Z3_mk_bvmul_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);

// BV reduction operations
Z3_ast       Z3_mk_bvredand(Z3_context c, Z3_ast t1);
Z3_ast       Z3_mk_bvredor(Z3_context c, Z3_ast t1);

// BV equality comparison (returns 1-bit BV)
Z3_ast       Z3_mk_bvcomp(Z3_context c, Z3_ast t1, Z3_ast t2);

// ============================================================================
// Quantifiers
// ============================================================================

// Patterns (triggers) for quantifier instantiation
Z3_pattern   Z3_mk_pattern(Z3_context c, unsigned int num_patterns,
                            const Z3_ast* terms);

// De Bruijn indexed bound variable
Z3_ast       Z3_mk_bound(Z3_context c, unsigned int index, Z3_sort ty);

// De Bruijn style quantifiers
Z3_ast       Z3_mk_forall(Z3_context c, unsigned int weight,
                           unsigned int num_patterns, const Z3_pattern* patterns,
                           unsigned int num_decls, const Z3_sort* sorts,
                           const Z3_symbol* decl_names, Z3_ast body);
Z3_ast       Z3_mk_exists(Z3_context c, unsigned int weight,
                           unsigned int num_patterns, const Z3_pattern* patterns,
                           unsigned int num_decls, const Z3_sort* sorts,
                           const Z3_symbol* decl_names, Z3_ast body);

// Constant-style quantifiers (preferred — uses term constants as bound vars)
Z3_ast       Z3_mk_forall_const(Z3_context c, unsigned int weight,
                                 unsigned int num_bound, const Z3_ast* bound,
                                 unsigned int num_patterns, const Z3_pattern* patterns,
                                 Z3_ast body);
Z3_ast       Z3_mk_exists_const(Z3_context c, unsigned int weight,
                                 unsigned int num_bound, const Z3_ast* bound,
                                 unsigned int num_patterns, const Z3_pattern* patterns,
                                 Z3_ast body);

// Quantifier introspection
bool         Z3_is_quantifier_forall(Z3_context c, Z3_ast a);
bool         Z3_is_quantifier_exists(Z3_context c, Z3_ast a);
Z3_ast       Z3_get_quantifier_body(Z3_context c, Z3_ast a);
unsigned int Z3_get_quantifier_num_bound(Z3_context c, Z3_ast a);
Z3_symbol    Z3_get_quantifier_bound_name(Z3_context c, Z3_ast a, unsigned int i);
Z3_sort      Z3_get_quantifier_bound_sort(Z3_context c, Z3_ast a, unsigned int i);
unsigned int Z3_get_quantifier_num_patterns(Z3_context c, Z3_ast a);
Z3_pattern   Z3_get_quantifier_pattern_ast(Z3_context c, Z3_ast a, unsigned int i);
unsigned int Z3_get_quantifier_weight(Z3_context c, Z3_ast a);
unsigned int Z3_get_quantifier_num_no_patterns(Z3_context c, Z3_ast a);
Z3_ast       Z3_get_quantifier_no_pattern_ast(Z3_context c, Z3_ast a, unsigned int i);

// ============================================================================
// AST Inspection
// ============================================================================

unsigned int Z3_get_ast_kind(Z3_context c, Z3_ast a);
bool         Z3_is_numeral_ast(Z3_context c, Z3_ast a);
bool         Z3_is_eq_ast(Z3_context c, Z3_ast t1, Z3_ast t2);
bool         Z3_is_app(Z3_context c, Z3_ast a);
Z3_ast       Z3_to_app(Z3_context c, Z3_ast a);
unsigned int Z3_get_ast_id(Z3_context c, Z3_ast a);
unsigned int Z3_get_ast_hash(Z3_context c, Z3_ast a);
Z3_string    Z3_get_numeral_string(Z3_context c, Z3_ast a);
Z3_string    Z3_get_numeral_decimal_string(Z3_context c, Z3_ast a, unsigned int precision);
Z3_string    Z3_ast_to_string(Z3_context c, Z3_ast a);
int          Z3_get_bool_value(Z3_context c, Z3_ast a);
bool         Z3_get_numeral_int(Z3_context c, Z3_ast a, int* v);
bool         Z3_get_numeral_uint(Z3_context c, Z3_ast a, unsigned int* v);
bool         Z3_get_numeral_int64(Z3_context c, Z3_ast a, int64_t* v);
bool         Z3_get_numeral_uint64(Z3_context c, Z3_ast a, uint64_t* v);
Z3_sort      Z3_get_sort(Z3_context c, Z3_ast a);
unsigned int Z3_get_app_num_args(Z3_context c, Z3_ast a);
Z3_ast       Z3_get_app_arg(Z3_context c, Z3_ast a, unsigned int i);
Z3_func_decl Z3_get_app_decl(Z3_context c, Z3_ast a);

// Simplification
Z3_ast       Z3_simplify(Z3_context c, Z3_ast a);

// ============================================================================
// Function Declaration Inspection
// ============================================================================

Z3_symbol    Z3_get_decl_name(Z3_context c, Z3_func_decl d);
unsigned int Z3_get_arity(Z3_context c, Z3_func_decl d);
unsigned int Z3_get_domain_size(Z3_context c, Z3_func_decl d);
Z3_sort      Z3_get_range(Z3_context c, Z3_func_decl d);
Z3_sort      Z3_get_domain(Z3_context c, Z3_func_decl d, unsigned int i);
unsigned int Z3_get_decl_kind(Z3_context c, Z3_func_decl d);
unsigned int Z3_get_decl_num_parameters(Z3_context c, Z3_func_decl d);
int          Z3_get_decl_int_parameter(Z3_context c, Z3_func_decl d, unsigned int idx);
Z3_ast       Z3_func_decl_to_ast(Z3_context c, Z3_func_decl d);
bool         Z3_is_eq_func_decl(Z3_context c, Z3_func_decl f1, Z3_func_decl f2);
Z3_string    Z3_func_decl_to_string(Z3_context c, Z3_func_decl d);

// ============================================================================
// Error Handling
// ============================================================================

unsigned int Z3_get_error_code(Z3_context c);
Z3_string    Z3_get_error_msg(Z3_context c, unsigned int err);
void         Z3_set_error_handler(Z3_context c, void (*h)(Z3_context, unsigned int));

// ============================================================================
// AST Vectors
// ============================================================================

Z3_ast_vector Z3_mk_ast_vector(Z3_context c);
void          Z3_ast_vector_inc_ref(Z3_context c, Z3_ast_vector v);
void          Z3_ast_vector_dec_ref(Z3_context c, Z3_ast_vector v);
unsigned int  Z3_ast_vector_size(Z3_context c, Z3_ast_vector v);
Z3_ast        Z3_ast_vector_get(Z3_context c, Z3_ast_vector v, unsigned int i);
void          Z3_ast_vector_push(Z3_context c, Z3_ast_vector v, Z3_ast a);
void          Z3_ast_vector_set(Z3_context c, Z3_ast_vector v, unsigned int i, Z3_ast a);
void          Z3_ast_vector_resize(Z3_context c, Z3_ast_vector v, unsigned int n);

// ============================================================================
// Solver
// ============================================================================

Z3_solver     Z3_mk_solver(Z3_context c);
Z3_solver     Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic);
void          Z3_solver_inc_ref(Z3_context c, Z3_solver s);
void          Z3_solver_dec_ref(Z3_context c, Z3_solver s);
void          Z3_solver_push(Z3_context c, Z3_solver s);
void          Z3_solver_pop(Z3_context c, Z3_solver s, unsigned int n);
void          Z3_solver_reset(Z3_context c, Z3_solver s);
void          Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a);
void          Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p);
int           Z3_solver_check(Z3_context c, Z3_solver s);
int           Z3_solver_check_assumptions(Z3_context c, Z3_solver s,
                                          unsigned int num_assumptions,
                                          const Z3_ast* assumptions);
Z3_model      Z3_solver_get_model(Z3_context c, Z3_solver s);
Z3_string     Z3_solver_to_string(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_assertions(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_unsat_core(Z3_context c, Z3_solver s);
Z3_string     Z3_solver_get_reason_unknown(Z3_context c, Z3_solver s);
unsigned int  Z3_solver_get_num_scopes(Z3_context c, Z3_solver s);
void          Z3_solver_interrupt(Z3_context c, Z3_solver s);

// ============================================================================
// Model
// ============================================================================

void          Z3_model_inc_ref(Z3_context c, Z3_model m);
void          Z3_model_dec_ref(Z3_context c, Z3_model m);
unsigned int  Z3_model_get_num_consts(Z3_context c, Z3_model m);
Z3_string     Z3_model_to_string(Z3_context c, Z3_model m);
Z3_func_decl  Z3_model_get_const_decl(Z3_context c, Z3_model m, unsigned int i);
Z3_ast        Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a);
unsigned int  Z3_model_get_num_funcs(Z3_context c, Z3_model m);
bool          Z3_model_has_interp(Z3_context c, Z3_model m, Z3_func_decl d);
bool          Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, bool model_completion,
                            Z3_ast* v);

// ============================================================================
// Parameters
// ============================================================================

Z3_params     Z3_mk_params(Z3_context c);
void          Z3_params_inc_ref(Z3_context c, Z3_params p);
void          Z3_params_dec_ref(Z3_context c, Z3_params p);
void          Z3_params_set_bool(Z3_context c, Z3_params p, Z3_symbol k, bool v);
void          Z3_params_set_uint(Z3_context c, Z3_params p, Z3_symbol k, unsigned int v);
void          Z3_params_set_double(Z3_context c, Z3_params p, Z3_symbol k, double v);
void          Z3_params_set_symbol(Z3_context c, Z3_params p, Z3_symbol k, Z3_symbol v);

// ============================================================================
// SMT-LIB2 Parsing
// ============================================================================

Z3_ast_vector Z3_parse_smtlib2_string(Z3_context c, Z3_string str,
                                      unsigned int num_sorts,
                                      const Z3_symbol* sort_names,
                                      const Z3_sort* sorts,
                                      unsigned int num_decls,
                                      const Z3_symbol* decl_names,
                                      const Z3_func_decl* decls);

#ifdef __cplusplus
}
#endif

#endif // Z4_Z3_COMPAT_H
