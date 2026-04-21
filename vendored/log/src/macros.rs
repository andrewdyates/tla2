// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! No-op logging macros.
//!
//! Every macro accepts any token tree and expands to nothing. The compiler
//! will optimise away the arguments entirely when they have no side effects.

/// No-op `log!` macro.
///
/// Expands to `()` (unit expression) so it works in expression position,
/// e.g. as a closure body: `|e, level| log::log!(level, "{e}")`.
/// Fix for naga 24.0.0 compilation (Part of #3956).
#[macro_export]
macro_rules! log {
    ($($tt:tt)*) => { () };
}

/// No-op `error!` macro.
#[macro_export]
macro_rules! error {
    ($($tt:tt)*) => { () };
}

/// No-op `warn!` macro.
#[macro_export]
macro_rules! warn {
    ($($tt:tt)*) => { () };
}

/// No-op `info!` macro.
#[macro_export]
macro_rules! info {
    ($($tt:tt)*) => { () };
}

/// No-op `debug!` macro.
#[macro_export]
macro_rules! debug {
    ($($tt:tt)*) => { () };
}

/// No-op `trace!` macro.
#[macro_export]
macro_rules! trace {
    ($($tt:tt)*) => { () };
}

/// No-op `log_enabled!` macro — always evaluates to `false`.
#[macro_export]
macro_rules! log_enabled {
    ($($tt:tt)*) => { false };
}
