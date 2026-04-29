// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable facade for string interning, TLC token ordering, and UTF-16 helpers.

mod intern;
mod tokens;
mod utf16;

#[cfg(test)]
mod tests;

pub use intern::{clear_string_intern_table, intern_string};
pub use tokens::{clear_tlc_string_tokens, tlc_string_token};
pub use utf16::{tlc_string_len, tlc_string_subseq_utf16_offsets};

pub(super) use intern::snapshot_string_intern_table;
pub(super) use tokens::{snapshot_tlc_string_tokens, tlc_string_token_counter_value};
