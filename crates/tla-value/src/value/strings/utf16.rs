// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;
use std::ops::Range;

/// TLC-compatible length for strings: number of UTF-16 code units.
#[inline]
pub fn tlc_string_len(s: &str) -> usize {
    s.encode_utf16().count()
}

fn tlc_string_utf16_offsets_to_byte_range(s: &str, offsets: Range<usize>) -> Option<Range<usize>> {
    let Range { start, end } = offsets;
    if start > end {
        return None;
    }
    if start == 0 && end == 0 {
        return Some(0..0);
    }

    let mut utf16_off: usize = 0;
    let mut byte_start: Option<usize> = if start == 0 { Some(0) } else { None };
    let mut byte_end: Option<usize> = if end == 0 { Some(0) } else { None };

    for (byte_idx, ch) in s.char_indices() {
        if byte_start.is_none() && utf16_off == start {
            byte_start = Some(byte_idx);
        }

        utf16_off = utf16_off.saturating_add(ch.len_utf16());
        let byte_after = byte_idx + ch.len_utf8();

        if byte_end.is_none() && utf16_off == end {
            byte_end = Some(byte_after);
        }

        // If either offset falls inside a multi-unit character, it can't map to a UTF-8 boundary.
        if byte_start.is_none() && utf16_off > start {
            return None;
        }
        if byte_end.is_none() && utf16_off > end {
            return None;
        }

        if let (Some(bs), Some(be)) = (byte_start, byte_end) {
            return Some(bs..be);
        }
    }

    // Offset at the end of the string (byte boundary).
    if utf16_off == start && byte_start.is_none() {
        byte_start = Some(s.len());
    }
    if utf16_off == end && byte_end.is_none() {
        byte_end = Some(s.len());
    }

    match (byte_start, byte_end) {
        (Some(bs), Some(be)) => Some(bs..be),
        _ => None,
    }
}

/// TLC-compatible substring by UTF-16 *offsets* (0-indexed, end-exclusive).
///
/// Returns a borrowed slice when the offsets align to UTF-8 boundaries.
/// If an offset falls inside a surrogate pair (non-BMP char), falls back to
/// a lossy UTF-16 decode (producing U+FFFD for invalid surrogate halves).
pub fn tlc_string_subseq_utf16_offsets(s: &str, offsets: Range<usize>) -> Cow<'_, str> {
    if let Some(byte_range) = tlc_string_utf16_offsets_to_byte_range(s, offsets.clone()) {
        return Cow::Borrowed(&s[byte_range]);
    }

    let utf16: Vec<u16> = s.encode_utf16().collect();
    Cow::Owned(String::from_utf16_lossy(&utf16[offsets]))
}
