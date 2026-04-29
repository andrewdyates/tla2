// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Alias binary: `tla` delegates to the same entry point as `tla2`.
//!
//! This exists as a separate file to avoid Cargo's "file found in multiple
//! build targets" warning when two `[[bin]]` entries share one source file.
include!("../main.rs");
