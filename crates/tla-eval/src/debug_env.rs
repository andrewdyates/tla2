// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Debug environment flag utilities for tla-eval.
//!
//! Helper functions are consolidated in `tla_core::debug_env` (Part of #2384).
//! `debug_flag!` implementation is centralized in `tla_core`; local macros
//! remain for `debug_eprintln!` and `debug_block!`.

macro_rules! debug_eprintln {
    ($flag:expr, $($arg:tt)*) => {
        #[cfg(debug_assertions)]
        if $flag {
            eprintln!($($arg)*);
        }
    };
}

macro_rules! debug_block {
    ($flag:expr, $block:block) => {
        #[cfg(debug_assertions)]
        if $flag $block
    };
}

macro_rules! debug_flag {
    ($($arg:tt)*) => {
        tla_core::tla_debug_flag!($($arg)*);
    };
}

macro_rules! feature_flag {
    ($vis:vis $name:ident, $env:literal) => {
        $vis fn $name() -> bool {
            static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            tla_core::env_flag_is_set(&FLAG, $env)
        }
    };
}
