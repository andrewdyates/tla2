// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compile-time gated debug logging for SAT solver internals.
//!
//! Parity with CaDiCaL's `LOG` macro (`reference/cadical/src/logging.hpp:76-91`).
//!
//! ## Usage
//!
//! Enable at compile time via custom cfg:
//! ```bash
//! RUSTFLAGS='--cfg z4_logging' cargo test -p z4-sat
//! ```
//!
//! At runtime, set `Z4_LOG=1` to activate output (the compile-time gate must
//! also be active). Without `Z4_LOG=1`, the runtime check is a single branch.
//!
//! ## Zero-cost guarantee
//!
//! When `z4_logging` is not set (the default), the macro expands to nothing:
//! no branches, no function calls, no string formatting. Equivalent to
//! CaDiCaL's `#ifndef LOGGING` path.

/// CaDiCaL-style debug logging macro.
///
/// When `z4_logging` cfg is active AND `log_enabled` is true at runtime,
/// prints a prefixed line to stderr with solver state context.
///
/// When `z4_logging` cfg is NOT active, expands to zero instructions.
#[cfg(z4_logging)]
macro_rules! solver_log {
    ($solver:expr, $($arg:tt)*) => {
        if $solver.log_enabled {
            eprintln!("[SAT d{}c{}] {}", $solver.decision_level, $solver.num_conflicts, format_args!($($arg)*));
        }
    };
}

/// No-op version when `z4_logging` cfg is not active.
#[cfg(not(z4_logging))]
macro_rules! solver_log {
    ($solver:expr, $($arg:tt)*) => {};
}

/// Make the macro available throughout the crate.
pub(crate) use solver_log;
