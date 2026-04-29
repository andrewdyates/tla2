// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{tlc_string_len, tlc_string_subseq_utf16_offsets};
use std::borrow::Cow;

#[test]
fn tlc_string_len_counts_utf16_code_units() {
    assert_eq!(tlc_string_len("abc"), 3);
    assert_eq!(tlc_string_len("a\u{1F600}b"), 4);
}

#[test]
fn tlc_string_subseq_utf16_offsets_borrows_bmp_ranges() {
    let subseq = tlc_string_subseq_utf16_offsets("abcd", 1..3);
    assert!(matches!(subseq, Cow::Borrowed("bc")));
}

#[test]
fn tlc_string_subseq_utf16_offsets_falls_back_for_surrogate_boundaries() {
    let subseq = tlc_string_subseq_utf16_offsets("a\u{1F600}b", 1..2);
    assert!(matches!(subseq, Cow::Owned(_)));
    assert_eq!(subseq.as_ref(), "\u{FFFD}");
}

#[test]
fn tlc_string_subseq_utf16_offsets_handles_empty_end_range() {
    let subseq = tlc_string_subseq_utf16_offsets("abc", 3..3);
    assert!(matches!(subseq, Cow::Borrowed("")));
}
