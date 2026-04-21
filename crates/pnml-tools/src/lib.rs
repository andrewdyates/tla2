// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compatibility facade for the legacy `pnml-tools` crate name.
//!
//! The canonical Petri/MCC implementation now lives in `tla-petri` and is
//! exposed in the unified `tla2` CLI via `tla2 petri` and `tla2 mcc`.
//! This crate remains as a thin re-export layer so existing code and scripts
//! using the `pnml-tools` package name continue to compile against the same
//! underlying implementation.

pub use tla_petri::*;
