// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure operator mapping tables: token-kind → operator name lookups.
//!
//! These are zero-dependency functions used by both the core dispatch hub
//! and sibling expression-lowering modules.

use crate::ast::Expr;
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::SyntaxKind;

pub(super) fn operator_token_to_name(kind: SyntaxKind) -> Option<&'static str> {
    Some(match kind {
        // Arithmetic
        SyntaxKind::PlusOp => "+",
        SyntaxKind::MinusOp => "-",
        SyntaxKind::StarOp => "*",
        SyntaxKind::SlashOp => "/",
        SyntaxKind::DivOp => "\\div",
        SyntaxKind::PercentOp => "%",
        SyntaxKind::CaretOp => "^",
        // Multi-character user-definable operators
        SyntaxKind::PlusPlusOp => "++",
        SyntaxKind::MinusMinusOp => "--",
        SyntaxKind::StarStarOp => "**",
        SyntaxKind::SlashSlashOp => "//",
        SyntaxKind::CaretCaretOp => "^^",
        SyntaxKind::PercentPercentOp => "%%",
        SyntaxKind::AmpAmpOp => "&&",
        // Circled operators (user-definable)
        SyntaxKind::OplusOp => "\\oplus",
        SyntaxKind::OminusOp => "\\ominus",
        SyntaxKind::OtimesOp => "\\otimes",
        SyntaxKind::OslashOp => "\\oslash",
        SyntaxKind::OdotOp => "\\odot",
        SyntaxKind::UplusOp => "\\uplus",
        SyntaxKind::SqcapOp => "\\sqcap",
        SyntaxKind::SqcupOp => "\\sqcup",
        // Logic
        SyntaxKind::AndOp => "/\\",
        SyntaxKind::OrOp => "\\/",
        SyntaxKind::ImpliesOp => "=>",
        SyntaxKind::EquivOp => "<=>",
        // Comparison
        SyntaxKind::EqOp => "=",
        SyntaxKind::NeqOp => "/=",
        SyntaxKind::LtOp => "<",
        SyntaxKind::GtOp => ">",
        SyntaxKind::LeqOp => "<=",
        SyntaxKind::GeqOp => ">=",
        // Ordering relations (user-definable)
        SyntaxKind::PrecOp => "\\prec",
        SyntaxKind::PreceqOp => "\\preceq",
        SyntaxKind::SuccOp => "\\succ",
        SyntaxKind::SucceqOp => "\\succeq",
        SyntaxKind::LlOp => "\\ll",
        SyntaxKind::GgOp => "\\gg",
        SyntaxKind::SimOp => "\\sim",
        SyntaxKind::SimeqOp => "\\simeq",
        SyntaxKind::AsympOp => "\\asymp",
        SyntaxKind::ApproxOp => "\\approx",
        SyntaxKind::CongOp => "\\cong",
        SyntaxKind::DoteqOp => "\\doteq",
        SyntaxKind::ProptoOp => "\\propto",
        // Sets
        SyntaxKind::InOp => "\\in",
        SyntaxKind::NotInOp => "\\notin",
        SyntaxKind::SubseteqOp => "\\subseteq",
        SyntaxKind::SubsetOp => "\\subset",
        SyntaxKind::SupseteqOp => "\\supseteq",
        SyntaxKind::SupsetOp => "\\supset",
        SyntaxKind::UnionOp => "\\cup",
        SyntaxKind::IntersectOp => "\\cap",
        SyntaxKind::SetMinusOp => "\\",
        SyntaxKind::SqsubseteqOp => "\\sqsubseteq",
        SyntaxKind::SqsupseteqOp => "\\sqsupseteq",
        // Sequences/functions
        SyntaxKind::ConcatOp => "\\o",
        // Action composition
        SyntaxKind::CdotOp => "\\cdot",
        // User-definable infix operators
        SyntaxKind::Pipe => "|",
        SyntaxKind::Amp => "&",
        // TLC module operators that use infix syntax
        SyntaxKind::ColonGt => ":>",
        SyntaxKind::AtAt => "@@",
        // BNF
        SyntaxKind::ColonColonEqOp => "::=",
        // Apalache assignment operator
        SyntaxKind::ColonEqOp => ":=",
        // Apalache type annotation operator
        SyntaxKind::LtColonOp => "<:",
        _ => return None,
    })
}

/// Convert stdlib keyword token to operator name
pub(super) fn stdlib_keyword_to_name(kind: SyntaxKind) -> Option<String> {
    match kind {
        SyntaxKind::LenKw => Some("Len".to_string()),
        SyntaxKind::HeadKw => Some("Head".to_string()),
        SyntaxKind::TailKw => Some("Tail".to_string()),
        SyntaxKind::AppendKw => Some("Append".to_string()),
        SyntaxKind::SubSeqKw => Some("SubSeq".to_string()),
        SyntaxKind::SelectSeqKw => Some("SelectSeq".to_string()),
        SyntaxKind::SeqKw => Some("Seq".to_string()),
        // Note: Cardinality is parsed as an identifier, not a keyword
        _ => None,
    }
}

pub(super) fn make_apply_binary(op_name: &str, left: Spanned<Expr>, right: Spanned<Expr>) -> Expr {
    Expr::Apply(
        Box::new(Spanned::dummy(Expr::Ident(
            op_name.to_string(),
            NameId::INVALID,
        ))),
        vec![left, right],
    )
}
