// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use logos::Logos;

use super::block_comment::lex_block_comment;

include!("token_groups/keywords.rs");
include!("token_groups/operators.rs");
include!("token_groups/surface.rs");

macro_rules! emit_token_enum {
    ([$($variants:tt)*]) => {
        /// TLA+ tokens
        #[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
        pub(crate) enum Token {
            // === Trivia (whitespace and comments) ===
            /// Whitespace (spaces, tabs, newlines) - needed for rowan's span calculation
            #[regex(r"[ \t\r\n]+")]
            Whitespace,

            $($variants)*
        }
    };
}

push_keyword_tokens!(emit_token_enum);

impl Token {
    /// Returns true if this token is trivia (whitespace/comments)
    pub fn is_trivia(&self) -> bool {
        matches!(
            self,
            Token::Whitespace | Token::LineComment | Token::BlockComment
        )
    }
}
