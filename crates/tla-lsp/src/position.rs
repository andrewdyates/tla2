// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::Span;
use tower_lsp::lsp_types::{Position, Range};

/// Convert a byte offset to LSP Position
pub(crate) fn offset_to_position(source: &str, offset: u32) -> Position {
    let offset = offset as usize;
    let mut line = 0u32;
    let mut col = 0u32;
    for (i, c) in source.char_indices() {
        if i >= offset {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }
    Position::new(line, col)
}

/// Convert LSP Position to byte offset
pub(crate) fn position_to_offset(source: &str, pos: Position) -> u32 {
    let mut current_line = 0u32;
    let mut offset = 0usize;
    for c in source.chars() {
        if current_line == pos.line {
            break;
        }
        if c == '\n' {
            current_line += 1;
        }
        offset += c.len_utf8();
    }
    // Add column offset
    for (col, c) in source[offset..].chars().enumerate() {
        if col as u32 >= pos.character {
            break;
        }
        offset += c.len_utf8();
    }
    offset as u32
}

/// Convert Span to LSP Range
pub(crate) fn span_to_range(source: &str, span: Span) -> Range {
    Range::new(
        offset_to_position(source, span.start),
        offset_to_position(source, span.end),
    )
}
