// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Debug environment flag utilities for tla-value.
//!
//! Helper functions are consolidated in `tla_core::debug_env` (Part of #2384).
//! Macro implementation is centralized in `tla_core`; this module keeps
//! local `debug_flag!` for compatibility.

/// Define a boolean debug flag backed by an environment variable.
macro_rules! debug_flag {
    ($($arg:tt)*) => {
        tla_core::tla_debug_flag!($($arg)*);
    };
}
