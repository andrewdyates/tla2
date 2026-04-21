// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::token::Token;

/// Callback to lex block comments (* ... *)
/// Returns the end position of the comment relative to the start of `(*`
pub(super) fn lex_block_comment(lexer: &mut logos::Lexer<Token>) -> bool {
    let remainder = lexer.remainder();
    let mut depth = 1; // Already saw opening (*
    let mut i = 0;
    let bytes = remainder.as_bytes();

    while i < bytes.len() && depth > 0 {
        if i + 1 < bytes.len() {
            if bytes[i] == b'*' && bytes[i + 1] == b')' {
                depth -= 1;
                if depth == 0 {
                    lexer.bump(i + 2); // Include the closing *)
                    return true;
                }
                i += 2;
                continue;
            }
            if bytes[i] == b'(' && bytes[i + 1] == b'*' {
                depth += 1;
                i += 2;
                continue;
            }
        }
        i += 1;
    }

    // Unclosed comment - consume rest of input as error
    false
}
