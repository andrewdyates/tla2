// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! No-op replacement for the `log` crate.
//!
//! This vendored stub provides the same macro and type API as the real `log`
//! crate but compiles to nothing. Cranelift, regalloc2, and other vendored
//! crates that depend on `log` get zero-cost no-ops instead of pulling in the
//! full logging infrastructure that TLA2 never uses.

#[doc(hidden)]
#[macro_use]
mod macros;

/// Log level.
///
/// Only the variants used by vendored consumers are required. The ordering
/// matches the real `log` crate: Error (1) > Warn > Info > Debug > Trace (5).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Level {
    /// Error level.
    Error = 1,
    /// Warn level.
    Warn,
    /// Info level.
    Info,
    /// Debug level.
    Debug,
    /// Trace level.
    Trace,
}

/// Level filter — mirrors `log::LevelFilter`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LevelFilter {
    /// Disables all logging.
    Off,
    /// Enables error logging.
    Error,
    /// Enables warn and above.
    Warn,
    /// Enables info and above.
    Info,
    /// Enables debug and above.
    Debug,
    /// Enables all logging.
    Trace,
}

impl LevelFilter {
    fn to_u8(self) -> u8 {
        match self {
            LevelFilter::Off => 0,
            LevelFilter::Error => 1,
            LevelFilter::Warn => 2,
            LevelFilter::Info => 3,
            LevelFilter::Debug => 4,
            LevelFilter::Trace => 5,
        }
    }
}

impl Level {
    fn to_u8(self) -> u8 {
        self as u8
    }
}

// Comparison: Level <= LevelFilter (used by the original log macros).
impl PartialEq<LevelFilter> for Level {
    fn eq(&self, other: &LevelFilter) -> bool {
        self.to_u8() == other.to_u8()
    }
}

impl PartialOrd<LevelFilter> for Level {
    fn partial_cmp(&self, other: &LevelFilter) -> Option<core::cmp::Ordering> {
        Some(self.to_u8().cmp(&other.to_u8()))
    }
}

impl PartialOrd for Level {
    fn partial_cmp(&self, other: &Level) -> Option<core::cmp::Ordering> {
        Some(self.to_u8().cmp(&other.to_u8()))
    }
}

impl Ord for Level {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_u8().cmp(&other.to_u8())
    }
}

/// All logging is statically disabled.
pub const STATIC_MAX_LEVEL: LevelFilter = LevelFilter::Off;

/// Returns `LevelFilter::Off` — no logging is ever enabled.
#[inline(always)]
pub fn max_level() -> LevelFilter {
    LevelFilter::Off
}

/// Private API module referenced by the macro expansions in the original `log`
/// crate. Only the symbols actually used by vendored consumers are provided.
#[doc(hidden)]
pub mod __private_api {
    pub use core::{format_args, module_path, stringify};

    /// Placeholder global logger (never called because all macros are no-ops).
    #[derive(Debug)]
    pub struct GlobalLogger;
}
