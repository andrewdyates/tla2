// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/**
 * Z4 SMT Solver - C FFI Header
 *
 * This header provides C-compatible bindings for the Z4 SMT solver.
 * Link against libz4_ffi.a (static) or libz4_ffi.so/dylib (dynamic).
 *
 * Thread Safety:
 * - Z4Solver handles are NOT thread-safe
 * - Use separate solver instances for concurrent access
 *
 * Memory Management:
 * - z4_solver_new() returns handles that must be freed with z4_solver_free()
 * - String returns (z4_get_model, z4_get_error, z4_version) must be freed with z4_string_free()
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 */

#ifndef Z4_H
#define Z4_H

#ifdef __cplusplus
extern "C" {
#endif

/* Result codes */
#define Z4_SAT      1    /* Satisfiable - a model exists */
#define Z4_UNSAT    0    /* Unsatisfiable - no model exists */
#define Z4_UNKNOWN  (-1) /* Unknown - solver could not determine */
#define Z4_ERROR    (-2) /* Error - invalid input or internal error */

/* Opaque solver handle */
typedef struct Z4Solver Z4Solver;

/* ============================================================================
 * Core Functions
 * ============================================================================ */

/**
 * Create a new solver instance.
 *
 * @return Non-null pointer on success, null on failure (out of memory)
 */
Z4Solver* z4_solver_new(void);

/**
 * Destroy a solver instance and free associated memory.
 *
 * @param solver Solver handle (safe to call with null)
 */
void z4_solver_free(Z4Solver* solver);

/**
 * Solve SMT-LIB input.
 *
 * Parses and executes the given SMT-LIB commands, returning the result
 * of the last (check-sat) command.
 *
 * @param solver Solver handle
 * @param smtlib Null-terminated SMT-LIB string
 * @return Z4_SAT, Z4_UNSAT, Z4_UNKNOWN, or Z4_ERROR
 */
int z4_solve_smtlib(Z4Solver* solver, const char* smtlib);

/**
 * Get the model from the last SAT result.
 *
 * @param solver Solver handle
 * @return Model string (caller must free with z4_string_free), or null
 */
char* z4_get_model(Z4Solver* solver);

/**
 * Get the last error message.
 *
 * @param solver Solver handle
 * @return Error string (caller must free with z4_string_free), or null
 */
char* z4_get_error(Z4Solver* solver);

/**
 * Free a string returned by z4 functions.
 *
 * @param s String to free (safe to call with null)
 */
void z4_string_free(char* s);

/**
 * Reset the solver state.
 *
 * Clears all assertions and declarations.
 *
 * @param solver Solver handle
 */
void z4_reset(Z4Solver* solver);

/* ============================================================================
 * Quick Solve Functions (One-shot, no handle management)
 * ============================================================================ */

/**
 * Quick SMT solve (one-shot).
 *
 * Creates a temporary solver, runs the input, returns result.
 *
 * @param smtlib Null-terminated SMT-LIB string
 * @return Z4_SAT, Z4_UNSAT, Z4_UNKNOWN, or Z4_ERROR
 */
int z4_quick_solve(const char* smtlib);

/**
 * Quick LIA solve.
 *
 * Convenience for QF_LIA problems (automatically adds logic declaration).
 *
 * @param formula SMT-LIB formula without logic declaration
 * @return Z4_SAT, Z4_UNSAT, Z4_UNKNOWN, or Z4_ERROR
 */
int z4_solve_lia(const char* formula);

/**
 * Quick SAT solve.
 *
 * Convenience for propositional problems.
 *
 * @param formula SMT-LIB formula with Bool declarations
 * @return Z4_SAT, Z4_UNSAT, Z4_UNKNOWN, or Z4_ERROR
 */
int z4_solve_sat(const char* formula);

/**
 * Quick BV solve.
 *
 * Convenience for QF_BV problems.
 *
 * @param formula SMT-LIB formula with BitVec declarations
 * @return Z4_SAT, Z4_UNSAT, Z4_UNKNOWN, or Z4_ERROR
 */
int z4_solve_bv(const char* formula);

/* ============================================================================
 * Version Info
 * ============================================================================ */

/**
 * Get Z4 version string.
 *
 * @return Heap-allocated version string (caller must free with z4_string_free)
 */
char* z4_version(void);

#ifdef __cplusplus
}
#endif

#endif /* Z4_H */
