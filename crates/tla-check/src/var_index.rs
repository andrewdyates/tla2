// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variable indexing — re-exported from tla-core.
//!
//! The canonical implementation now lives in `tla_core::var_index`.
//! This module re-exports everything so existing `use crate::var_index::*`
//! imports within tla-check continue to work without modification.

pub use tla_core::{VarIndex, VarRegistry};
