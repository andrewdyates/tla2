// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LET binding lazy evaluation semantics tests: TLC parity for unused LET
//! bindings, error deferral, LET shadowing, and `is_let_lazy_safe_error` guard.

use super::*;

mod choose_and_disabled;
mod shadow_and_classifier;
mod unused_error_variants;
