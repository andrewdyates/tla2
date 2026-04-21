// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible C API for Z4
//!
//! Implements a subset of the Z3 C API (`z3_api.h`) so that external consumers
//! (Lean, KLEE, Seahorn) can link against Z4 as a drop-in replacement.
//!
//! # Architecture
//!
//! - `Z3_context` wraps a `z4_dpll::api::Solver` (Z4 combines context + solver)
//! - `Z3_ast` is a 32-bit term handle (wraps `z4_dpll::api::Term`)
//! - `Z3_sort` is a heap-allocated sort descriptor
//! - `Z3_func_decl` is a heap-allocated function declaration
//! - `Z3_model` is a heap-allocated model from a SAT result
//! - `Z3_solver` aliases `Z3_context` (Z4 has one solver per context)
//!
//! Reference counting (`inc_ref`/`dec_ref`) is a no-op in this implementation.
//! Objects are freed when their parent context is destroyed.

mod accessors;
mod arithmetic;
mod ast_identity;
#[allow(unreachable_pub)] // FFI functions are pub for linker visibility
mod ast_inspect;
mod bitvectors;
mod bitvectors_overflow;
mod context;
mod ffi_guards;
pub(crate) use ffi_guards::*;
mod model_params;
mod numerals;
mod quantifier_inspect;
mod quantifiers;
mod solver;
mod sorts;
mod terms;

#[cfg(test)]
mod tests;

// Re-export all public items from submodules
pub use accessors::*;
pub use arithmetic::*;
pub use ast_identity::*;
pub use ast_inspect::*;
pub use bitvectors::*;
pub use bitvectors_overflow::*;
pub use context::*;
pub use model_params::*;
pub use numerals::*;
pub use quantifier_inspect::*;
pub use quantifiers::*;
pub use solver::*;
pub use sorts::*;
pub use terms::*;

use std::collections::HashMap;
use std::ffi::{c_char, c_int, c_uint, CString};
use std::ptr;
use std::time::Duration;

use z4_dpll::api::{FuncDecl, Model, Solver, Sort, Term};
// PatternHandle is available via `pub use quantifiers::*` above.

// ============================================================================
// Z3 Type Aliases (Opaque Pointers)
// ============================================================================

/// Opaque context handle (wraps Z4 Solver)
pub type Z3_context = *mut Z3Context;
/// Opaque config handle
pub type Z3_config = *mut Z3Config;
/// AST handle (wraps Z4 Term — a Copy 32-bit index)
pub type Z3_ast = u64;
/// Sort handle (heap-allocated)
pub type Z3_sort = *mut SortHandle;
/// Function declaration handle (heap-allocated)
pub type Z3_func_decl = *mut FuncDeclHandle;
/// Solver handle (aliases context in Z4)
pub type Z3_solver = *mut Z3SolverHandle;
/// Model handle (heap-allocated)
pub type Z3_model = *mut ModelHandle;
/// Symbol handle (heap-allocated)
pub type Z3_symbol = *mut SymbolHandle;
/// Params handle (heap-allocated)
pub type Z3_params = *mut ParamsHandle;
/// AST vector handle
pub type Z3_ast_vector = *mut AstVectorHandle;

// ============================================================================
// Z3 Constants
// ============================================================================

/// Z3_lbool values
pub const Z3_L_FALSE: c_int = -1;
pub const Z3_L_UNDEF: c_int = 0;
pub const Z3_L_TRUE: c_int = 1;

/// Z3_sort_kind values
pub const Z3_BOOL_SORT: c_uint = 1;
pub const Z3_INT_SORT: c_uint = 2;
pub const Z3_REAL_SORT: c_uint = 3;
pub const Z3_BV_SORT: c_uint = 4;
pub const Z3_ARRAY_SORT: c_uint = 5;
pub const Z3_UNINTERPRETED_SORT: c_uint = 6;

/// Z3_ast_kind values
pub const Z3_NUMERAL_AST: c_uint = 0;
pub const Z3_APP_AST: c_uint = 1;
pub const Z3_VAR_AST: c_uint = 2;
pub const Z3_QUANTIFIER_AST: c_uint = 3;
pub const Z3_UNKNOWN_AST: c_uint = 1000;

/// Z3_decl_kind values (operator kinds for function declarations).
/// These match the Z3 C API enum values from z3_api.h.
// Basic
pub const Z3_OP_TRUE: c_uint = 0x100;
pub const Z3_OP_FALSE: c_uint = 0x101;
pub const Z3_OP_EQ: c_uint = 0x102;
pub const Z3_OP_DISTINCT: c_uint = 0x103;
pub const Z3_OP_ITE: c_uint = 0x104;
pub const Z3_OP_AND: c_uint = 0x105;
pub const Z3_OP_OR: c_uint = 0x106;
pub const Z3_OP_IFF: c_uint = 0x107;
pub const Z3_OP_XOR: c_uint = 0x108;
pub const Z3_OP_NOT: c_uint = 0x109;
pub const Z3_OP_IMPLIES: c_uint = 0x10a;
// Arithmetic
pub const Z3_OP_ANUM: c_uint = 0x200;
pub const Z3_OP_AGNUM: c_uint = 0x201;
pub const Z3_OP_LE: c_uint = 0x202;
pub const Z3_OP_GE: c_uint = 0x203;
pub const Z3_OP_LT: c_uint = 0x204;
pub const Z3_OP_GT: c_uint = 0x205;
pub const Z3_OP_ADD: c_uint = 0x206;
pub const Z3_OP_SUB: c_uint = 0x207;
pub const Z3_OP_UMINUS: c_uint = 0x208;
pub const Z3_OP_MUL: c_uint = 0x209;
pub const Z3_OP_DIV: c_uint = 0x20a;
pub const Z3_OP_IDIV: c_uint = 0x20b;
pub const Z3_OP_REM: c_uint = 0x20c;
pub const Z3_OP_MOD: c_uint = 0x20d;
pub const Z3_OP_TO_REAL: c_uint = 0x20e;
pub const Z3_OP_TO_INT: c_uint = 0x20f;
pub const Z3_OP_IS_INT: c_uint = 0x210;
pub const Z3_OP_POWER: c_uint = 0x211;
pub const Z3_OP_ABS: c_uint = 0x212;
// Arrays
pub const Z3_OP_STORE: c_uint = 0x300;
pub const Z3_OP_SELECT: c_uint = 0x301;
pub const Z3_OP_CONST_ARRAY: c_uint = 0x302;
// Bitvectors
pub const Z3_OP_BNUM: c_uint = 0x400;
pub const Z3_OP_BIT1: c_uint = 0x401;
pub const Z3_OP_BIT0: c_uint = 0x402;
pub const Z3_OP_BNEG: c_uint = 0x403;
pub const Z3_OP_BADD: c_uint = 0x404;
pub const Z3_OP_BSUB: c_uint = 0x405;
pub const Z3_OP_BMUL: c_uint = 0x406;
pub const Z3_OP_BSDIV: c_uint = 0x407;
pub const Z3_OP_BUDIV: c_uint = 0x408;
pub const Z3_OP_BSREM: c_uint = 0x409;
pub const Z3_OP_BUREM: c_uint = 0x40a;
pub const Z3_OP_BSMOD: c_uint = 0x40b;
pub const Z3_OP_BAND: c_uint = 0x412;
pub const Z3_OP_BOR: c_uint = 0x413;
pub const Z3_OP_BNOT: c_uint = 0x414;
pub const Z3_OP_BXOR: c_uint = 0x415;
pub const Z3_OP_BNAND: c_uint = 0x416;
pub const Z3_OP_BNOR: c_uint = 0x417;
pub const Z3_OP_BXNOR: c_uint = 0x418;
pub const Z3_OP_CONCAT: c_uint = 0x419;
pub const Z3_OP_SIGN_EXT: c_uint = 0x41a;
pub const Z3_OP_ZERO_EXT: c_uint = 0x41b;
pub const Z3_OP_EXTRACT: c_uint = 0x41c;
pub const Z3_OP_REPEAT: c_uint = 0x41d;
pub const Z3_OP_BSHL: c_uint = 0x43c;
pub const Z3_OP_BLSHR: c_uint = 0x43d;
pub const Z3_OP_BASHR: c_uint = 0x43e;
pub const Z3_OP_ROTATE_LEFT: c_uint = 0x43f;
pub const Z3_OP_ROTATE_RIGHT: c_uint = 0x440;
pub const Z3_OP_SLEQ: c_uint = 0x42c;
pub const Z3_OP_SGEQ: c_uint = 0x42e;
pub const Z3_OP_SLT: c_uint = 0x42d;
pub const Z3_OP_SGT: c_uint = 0x42f;
pub const Z3_OP_ULEQ: c_uint = 0x428;
pub const Z3_OP_UGEQ: c_uint = 0x42a;
pub const Z3_OP_ULT: c_uint = 0x429;
pub const Z3_OP_UGT: c_uint = 0x42b;
// Uninterpreted
pub const Z3_OP_UNINTERPRETED: c_uint = 0x600;

/// Z3_error_code values
pub const Z3_OK: c_uint = 0;
pub const Z3_SORT_ERROR: c_uint = 1;
pub const Z3_IOB: c_uint = 2;
pub const Z3_INVALID_ARG: c_uint = 3;
pub const Z3_PARSER_ERROR: c_uint = 4;
pub const Z3_NO_PARSER: c_uint = 5;
pub const Z3_INVALID_PATTERN: c_uint = 6;
pub const Z3_MEMOUT_FAIL: c_uint = 7;
pub const Z3_FILE_ACCESS_ERROR: c_uint = 8;
pub const Z3_INTERNAL_FATAL: c_uint = 9;
pub const Z3_INVALID_USAGE: c_uint = 10;
pub const Z3_DEC_REF_ERROR: c_uint = 11;
pub const Z3_EXCEPTION: c_uint = 12;

// ============================================================================
// Internal Handle Types
// ============================================================================

/// Internal context state
pub struct Z3Context {
    pub(crate) solver: Solver,
    pub(crate) last_error: c_uint,
    pub(crate) error_msg: Option<String>,
    /// Interned strings for Z3_ast_to_string etc. (Z3 returns context-owned ptrs)
    pub(crate) string_cache: Vec<CString>,
    /// Cached symbol handles — freed on context deletion (#5528).
    pub(crate) symbol_cache: Vec<*mut SymbolHandle>,
    /// Track sorts associated with AST handles for sort queries
    pub(crate) ast_sorts: Vec<Option<Sort>>,
    /// Arena for heap-allocated handles — freed on context deletion (#5498).
    pub(crate) sort_cache: Vec<*mut SortHandle>,
    pub(crate) func_decl_cache: Vec<*mut FuncDeclHandle>,
    pub(crate) solver_handle_cache: Vec<*mut Z3SolverHandle>,
    pub(crate) model_cache: Vec<*mut ModelHandle>,
    pub(crate) params_cache: Vec<*mut ParamsHandle>,
    pub(crate) ast_vector_cache: Vec<*mut AstVectorHandle>,
    pub(crate) pattern_cache: Vec<*mut PatternHandle>,
    /// Stable semantic sort IDs: same Sort → same ID within a context (#6580).
    pub(crate) sort_ids: HashMap<Sort, c_uint>,
    /// Next available sort ID (monotonically increasing, starting at 1).
    pub(crate) next_sort_id: c_uint,
}

/// Free all non-null raw pointers in a Vec arena.
///
/// # Safety
/// Every pointer in `arena` must have been created via `Box::into_raw` and must
/// not have been freed elsewhere. Each pointer is consumed exactly once by
/// `Box::from_raw`, so double-free is impossible as long as the arena is the
/// sole owner.
unsafe fn drain_arena<T>(arena: &mut Vec<*mut T>) {
    for ptr in arena.drain(..) {
        if !ptr.is_null() {
            unsafe {
                let _ = Box::from_raw(ptr);
            }
        }
    }
}

impl Drop for Z3Context {
    fn drop(&mut self) {
        // Free all handle arenas (#5498, #5528).
        unsafe {
            drain_arena(&mut self.symbol_cache);
            drain_arena(&mut self.sort_cache);
            drain_arena(&mut self.func_decl_cache);
            drain_arena(&mut self.solver_handle_cache);
            drain_arena(&mut self.model_cache);
            drain_arena(&mut self.params_cache);
            drain_arena(&mut self.ast_vector_cache);
            drain_arena(&mut self.pattern_cache);
        }
    }
}

/// Configuration parameters recognized when creating a context.
pub struct Z3Config {
    pub(crate) params: Vec<(String, String)>,
}

pub struct SortHandle {
    pub(crate) sort: Sort,
    /// Stable semantic sort ID assigned per-context (#6580).
    pub(crate) sort_id: c_uint,
}

pub struct FuncDeclHandle {
    pub(crate) decl: FuncDecl,
    /// Indexed operator parameters (e.g., [7, 4] for extract[7:4]) (#6580 F2).
    pub(crate) params: Vec<c_int>,
}

pub struct Z3SolverHandle {
    /// Back-pointer to the parent context (kept for future multi-solver support)
    pub(crate) _ctx: Z3_context,
}

pub struct ModelHandle {
    pub(crate) model: Model,
    /// Context for evaluating model values (kept for future model_eval)
    pub(crate) _ctx: Z3_context,
}

pub struct SymbolHandle {
    pub(crate) name: String,
}

pub struct ParamsHandle {
    /// Stored until solver params are applied; only supported keys take effect.
    pub(crate) params: Vec<(String, String)>,
}

pub struct AstVectorHandle {
    pub(crate) asts: Vec<Z3_ast>,
}

// ============================================================================
// Helpers
// ============================================================================

/// Convert Z3_ast (u64) to Z4 Term.
/// Z3_ast uses 1-based encoding so that 0 can serve as the null/error sentinel.
/// Panics in debug mode on null AST; returns Term(0) defensively in release. (#5519)
#[inline]
pub(crate) fn ast_to_term(ast: Z3_ast) -> Term {
    debug_assert!(ast != 0, "BUG: null Z3_ast (0) passed to ast_to_term");
    if ast == 0 {
        // Defensive fallback: map null sentinel to Term(0) rather than
        // underflowing to u32::MAX which causes silent data corruption.
        return Term::from_raw(0);
    }
    Term::from_raw((ast - 1) as u32)
}

/// Convert Z4 Term to Z3_ast (u64).
/// Adds 1 so that TermId 0 maps to Z3_ast 1, reserving 0 as null.
#[inline]
pub(crate) fn term_to_ast(term: Term) -> Z3_ast {
    u64::from(term.to_raw()) + 1
}

/// Apply the subset of configuration/solver params that Z4 actually honors.
///
/// At the moment, only `timeout` is supported.
pub(crate) fn apply_supported_params(solver: &mut Solver, params: &[(String, String)]) {
    for (key, value) in params {
        if key == "timeout" {
            if let Ok(ms) = value.parse::<u64>() {
                solver.set_timeout(Some(Duration::from_millis(ms)));
            }
        }
    }
}

/// Null-safe context dereference. Returns None if null.
///
/// # Safety
/// - Caller must ensure `c` is valid and non-aliased if non-null.
/// - The returned reference's lifetime is caller-chosen; caller must not
///   hold it past the context's deallocation (`Z3_del_context`).
pub(crate) unsafe fn ctx_ref<'a>(c: Z3_context) -> Option<&'a mut Z3Context> {
    unsafe { c.as_mut() }
}

/// Store a string in context cache and return a pointer valid for context lifetime.
/// Z3 convention: returned strings are owned by the context.
pub(crate) fn cache_string(ctx: &mut Z3Context, s: String) -> *const c_char {
    match CString::new(s) {
        Ok(cs) => {
            let ptr = cs.as_ptr();
            ctx.string_cache.push(cs);
            ptr
        }
        Err(_) => ptr::null(),
    }
}

/// Store a symbol handle in context cache and return a pointer valid for context lifetime.
/// Prevents symbol handle leaks (#5528).
pub(crate) fn cache_symbol(ctx: &mut Z3Context, name: String) -> Z3_symbol {
    let handle = Box::into_raw(Box::new(SymbolHandle { name }));
    ctx.symbol_cache.push(handle);
    handle
}

/// Record the sort for an AST handle
pub(crate) fn record_ast_sort(ctx: &mut Z3Context, ast: Z3_ast, sort: Sort) {
    let idx = ast as usize;
    if idx >= ctx.ast_sorts.len() {
        ctx.ast_sorts.resize(idx + 1, None);
    }
    ctx.ast_sorts[idx] = Some(sort);
}

/// Look up sort for an AST handle
pub(crate) fn lookup_ast_sort(ctx: &Z3Context, ast: Z3_ast) -> Option<&Sort> {
    let idx = ast as usize;
    ctx.ast_sorts.get(idx).and_then(|s| s.as_ref())
}

/// Allocate a sort handle and register it in the context arena (#5498).
/// Assigns a stable semantic sort ID: same `Sort` value → same ID within
/// this context (#6580).
pub(crate) fn alloc_sort(ctx: &mut Z3Context, sort: Sort) -> Z3_sort {
    let sort_id = if let Some(&id) = ctx.sort_ids.get(&sort) {
        id
    } else {
        let id = ctx.next_sort_id;
        ctx.next_sort_id += 1;
        ctx.sort_ids.insert(sort.clone(), id);
        id
    };
    let handle = Box::into_raw(Box::new(SortHandle { sort, sort_id }));
    ctx.sort_cache.push(handle);
    handle
}

/// Allocate a func_decl handle and register it in the context arena (#5498).
pub(crate) fn cache_func_decl(ctx: &mut Z3Context, decl: FuncDecl) -> Z3_func_decl {
    cache_func_decl_with_params(ctx, decl, Vec::new())
}

/// Allocate a func_decl handle with indexed operator parameters (#6580 F2).
pub(crate) fn cache_func_decl_with_params(
    ctx: &mut Z3Context,
    decl: FuncDecl,
    params: Vec<c_int>,
) -> Z3_func_decl {
    let handle = Box::into_raw(Box::new(FuncDeclHandle { decl, params }));
    ctx.func_decl_cache.push(handle);
    handle
}

/// Parse an indexed symbol name like `"(_ extract 7 4)"` into base name and indices.
/// Returns `(base_name, indices)`. Non-indexed names return `(name, [])`.
pub(crate) fn parse_indexed_name(name: &str) -> (String, Vec<c_int>) {
    if let Some(inner) = name.strip_prefix("(_ ").and_then(|s| s.strip_suffix(')')) {
        let parts: Vec<&str> = inner.split_whitespace().collect();
        if parts.len() >= 2 {
            let base = parts[0].to_string();
            let indices: Vec<c_int> = parts[1..].iter().filter_map(|s| s.parse().ok()).collect();
            return (base, indices);
        }
    }
    (name.to_string(), Vec::new())
}

/// Allocate an AST vector handle and register it in the context arena (#5498).
pub(crate) fn cache_ast_vector(ctx: &mut Z3Context, asts: Vec<Z3_ast>) -> Z3_ast_vector {
    let handle = Box::into_raw(Box::new(AstVectorHandle { asts }));
    ctx.ast_vector_cache.push(handle);
    handle
}
