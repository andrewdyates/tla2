// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rowan adapter layer: trivia classification, rowan type conversions, and type aliases.

use super::syntax_kind::SyntaxKind;

impl SyntaxKind {
    /// Check if this is a trivia kind (whitespace or comment)
    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            SyntaxKind::Whitespace | SyntaxKind::LineComment | SyntaxKind::BlockComment
        )
    }
}

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

/// The language type for rowan
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TlaLanguage {}

impl rowan::Language for TlaLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        assert!(raw.0 < SyntaxKind::__Last as u16);
        // SAFETY: we check the range above
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

/// Type alias for rowan SyntaxNode with TLA+ language
pub type SyntaxNode = rowan::SyntaxNode<TlaLanguage>;
/// Type alias for rowan SyntaxToken with TLA+ language
pub type SyntaxToken = rowan::SyntaxToken<TlaLanguage>;
/// Type alias for rowan SyntaxElement with TLA+ language
pub type SyntaxElement = rowan::SyntaxElement<TlaLanguage>;
