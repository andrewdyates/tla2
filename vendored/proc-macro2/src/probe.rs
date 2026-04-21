#![allow(dead_code)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0


#[cfg(proc_macro_span)]
pub(crate) mod proc_macro_span;

#[cfg(proc_macro_span_file)]
pub(crate) mod proc_macro_span_file;

#[cfg(proc_macro_span_location)]
pub(crate) mod proc_macro_span_location;
