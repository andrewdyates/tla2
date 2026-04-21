// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![forbid(unsafe_code)]

//! Z4 Bindings - Typed builder API for Z4 SMT solver.
//!
//! This crate provides Rust types and serialization for Z4 solver integration.
//! It enables consumers to generate verification conditions in SMT-LIB2 format
//! for bounded model checking, k-induction, and CHC-based unbounded verification.
//!
//! ## Overview
//!
//! The crate provides:
//!
//! - **[`Sort`]** - SMT sorts (types): Bool, BitVec, Int, Real, Array, FP, Seq, String, Datatype
//! - **[`Expr`]** - SMT expressions: constants, variables, operations
//! - **[`Constraint`]** - SMT commands: assert, check-sat, push/pop
//! - **[`Z4Program`]** - Complete verification programs
//!
//! ## Example
//!
//! ```rust
//! use z4_bindings::{Z4Program, Sort, Expr};
//!
//! // Create a verification problem: x + 1 == 2
//! let mut program = Z4Program::qf_bv();
//! program.produce_models();
//!
//! // Declare symbolic variable
//! let x = program.declare_const("x", Sort::bv32());
//!
//! // Build constraint: x + 1 == 2
//! let one = Expr::bitvec_const(1i32, 32);
//! let two = Expr::bitvec_const(2i32, 32);
//! let sum = x.bvadd(one);
//! program.assert(sum.eq(two));
//!
//! // Check satisfiability
//! program.check_sat();
//! program.get_model();
//!
//! // Serialize to SMT-LIB2
//! let smt2 = program.to_string();
//! assert!(smt2.contains("(check-sat)"));
//! ```
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                          z4_bindings                                │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │                                                                     │
//! │   sort.rs          - Sort enum (Bool, BitVec, Int, Real, Array,   │
//! │                      FP, Seq, String, Datatype)                    │
//! │   expr/            - Z4Expr AST (symbolic expressions)             │
//! │     mod.rs         - Expr and ExprValue core types                 │
//! │     bool.rs        - Boolean operations                            │
//! │     bv.rs          - Bitvector operations                          │
//! │     int.rs         - Integer operations                            │
//! │     real.rs        - Real arithmetic operations                    │
//! │     fp.rs          - Floating-point operations                     │
//! │     arrays.rs      - Array operations                              │
//! │     seq.rs         - Sequence operations                           │
//! │     string.rs      - String operations                             │
//! │     dt.rs          - Datatype operations                           │
//! │     overflow.rs    - Overflow detection operations                 │
//! │     fold.rs        - Expression folding                            │
//! │     macros.rs      - Shared expression constructor macros          │
//! │     display.rs     - SMT-LIB2 Display implementation               │
//! │     tests.rs       - Expr module regression tests                  │
//! │   constraint/      - Z4Constraint (assert, check-sat, etc.)        │
//! │   program/         - Z4Program (context + constraints)             │
//! │                                                                     │
//! │   All types implement Display for SMT-LIB2 serialization.          │
//! │                                                                     │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Verification Modes
//!
//! This crate supports three verification approaches:
//!
//! ### Bounded Model Checking (BMC)
//!
//! For bounded verification of finite executions:
//! - Use `Z4Program::for_bmc()` preset
//! - Logic: QF_BV (quantifier-free bitvectors)
//! - Unroll loops to fixed depth
//! - Check: UNSAT means property holds within bound
//!
//! ### K-Induction
//!
//! For unbounded verification via induction:
//! - Use quantifiers for induction hypotheses
//! - Logic: BV or AUFBV (with quantifiers)
//! - Base case + inductive step
//!
//! ### CHC (Constrained Horn Clauses)
//!
//! For automatic invariant synthesis:
//! - Use `Z4Program::horn()` preset
//! - Logic: HORN
//! - Let solver discover inductive invariants
//!
//! ## SMT-LIB2 Compliance
//!
//! All types serialize to standard SMT-LIB2 format, compatible with:
//! - Z3
//! - CVC5
//! - Z4 (our target solver)
//! - Other SMT-LIB2 compliant solvers

/// Non-panicking replacement for `eprintln!`. Avoids SIGABRT on broken stderr pipe.
#[allow(unused_macros)]
macro_rules! safe_eprintln {
    ($($arg:tt)*) => {{
        use std::io::Write;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

pub mod constraint;
pub mod error;
pub mod expr;
pub mod memory;
mod memory_ops;
pub mod program;
pub mod sort;
mod sort_constructors;

// Test fixtures module - only available in test builds
#[cfg(test)]
pub mod test_fixtures;

// Direct execution module (requires z4-dpll)
#[cfg(feature = "direct")]
pub mod execute_direct;

// Re-export main types at crate root
pub use constraint::{logic, Constraint};
pub use error::SortError;
pub use expr::fold::{fold_expr, rebuild_with_children, ExprFold};
pub use expr::{Expr, ExprValue, RoundingMode};
pub use memory::MemoryModel;
pub use program::{ProgramBuilder, Z4Program};
pub use sort::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort, SortInner,
};
// Re-export panic utility so consumers don't duplicate it (#5344, #3880)
pub use z4_core::panic_payload_to_string;

/// Format a symbol for SMT-LIB2 output.
///
/// Delegates to [`z4_core::quote_symbol`] — the single source of truth for
/// SMT-LIB symbol quoting, reserved word handling, and `|`/`\` sanitization.
///
/// # Examples
///
/// ```
/// use z4_bindings::format_symbol;
///
/// assert_eq!(format_symbol("x"), "x");
/// assert_eq!(format_symbol("let"), "|let|");
/// assert_eq!(format_symbol("true"), "|true|");
/// assert_eq!(format_symbol("foo::bar"), "|foo::bar|");
/// assert_eq!(format_symbol("a|b"), "|a_b|");
/// ```
#[must_use]
pub fn format_symbol(name: &str) -> String {
    z4_core::quote_symbol(name)
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
