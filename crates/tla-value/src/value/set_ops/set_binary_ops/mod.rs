// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy binary set operations: union (`SetCupValue`), intersection (`SetCapValue`),
//! and difference (`SetDiffValue`).
//!
//! Extracted from `set_ops.rs` as part of #2747 decomposition.
//! Split into per-operator modules as part of #3444.

mod cap;
mod cup;
mod diff;
mod helpers;

pub use cap::SetCapValue;
pub use cup::SetCupValue;
pub use diff::SetDiffValue;
pub(crate) use helpers::all_in_set;
