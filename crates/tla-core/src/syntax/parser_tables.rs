// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Token classification tables and binding powers for the TLA+ parser.
//!
//! These are pure functions with no dependency on Parser state, extracted
//! from parser.rs for code-quality gate compliance (#1261).

use crate::syntax::lexer::Token;

pub(super) fn can_start_expr(token: Token) -> bool {
    matches!(
        token,
        Token::Not
            | Token::Minus
            | Token::Always
            | Token::Eventually
            | Token::Enabled
            | Token::Unchanged
            | Token::Powerset
            | Token::BigUnion
            | Token::Domain
            | Token::Forall
            | Token::Exists
            | Token::TemporalForall
            | Token::TemporalExists
            | Token::Choose
            | Token::If
            | Token::Case
            | Token::Let
            | Token::LParen
            | Token::LBrace
            | Token::LAngle
            | Token::LBracket
            | Token::Lambda
            | Token::True
            | Token::False
            | Token::Number
            | Token::String
            | Token::Ident
            | Token::Boolean
            | Token::At
            | Token::Len
            | Token::Seq
            | Token::SubSeq
            | Token::SelectSeq
            | Token::Head
            | Token::Tail
            | Token::Append
            | Token::WeakFair
            | Token::StrongFair
            | Token::And
            | Token::Or
            | Token::Instance
    )
}

/// Check if token is a proof step keyword (not including general expression starters).
/// Used to determine if an identifier after step level is a label name.
pub(super) fn is_proof_step_body_keyword(token: Token) -> bool {
    matches!(
        token,
        Token::Suffices
            | Token::Have
            | Token::Take
            | Token::Witness
            | Token::Pick
            | Token::Use
            | Token::Hide
            | Token::Define
            | Token::Qed
            | Token::Assume
            // Proof CASE step (not CASE expression)
            | Token::Case
    )
}

pub(super) fn is_proof_step_body_start(token: Token) -> bool {
    is_proof_step_body_keyword(token) || can_start_expr(token)
}

/// Check if a token can be a prefix operator symbol in prefix operator definitions
/// e.g., -. a == ... defines a prefix operator -.
pub(super) fn is_prefix_op_symbol(token: Token) -> bool {
    matches!(
        token,
        Token::Minus   // -.  (unary minus, as in -. a == 0 - a)
            | Token::Not   // ~   (logical not)
            | Token::Always   // []  (temporal always)
            | Token::Eventually // <>  (temporal eventually)
    )
}

/// Check if a token can be used as an operator symbol in infix operator definitions
/// e.g., a | b == ... defines an infix operator |
pub(super) fn is_infix_op_symbol(token: Token) -> bool {
    matches!(
        token,
        // User-definable operators
        Token::Plus
            | Token::Minus
            | Token::Star
            | Token::Slash
            | Token::Div
            | Token::Percent
            | Token::Caret
            | Token::Bang
            | Token::At
            | Token::AtAt
            | Token::Dollar
            | Token::DollarDollar
            | Token::Question
            | Token::Amp
            | Token::Concat
            | Token::ColonGt
            | Token::Turnstile
            | Token::Pipe
            // Multi-character user-definable operators
            | Token::PlusPlus
            | Token::MinusMinus
            | Token::StarStar
            | Token::SlashSlash
            | Token::CaretCaret
            | Token::PercentPercent
            | Token::AmpAmp
            // Circled operators
            | Token::Oplus
            | Token::Ominus
            | Token::Otimes
            | Token::Oslash
            | Token::Odot
            | Token::Uplus
            | Token::Sqcap
            | Token::Sqcup
            // Action composition
            | Token::Cdot
            // BNF production operator
            | Token::ColonColonEq
            // Apalache assignment operator
            | Token::ColonEq
            // Apalache type annotation operator
            | Token::LtColon
            // Relational (can be user-defined)
            | Token::Eq
            | Token::Neq
            | Token::Lt
            | Token::Gt
            | Token::Leq
            | Token::Geq
            // Ordering relations (user-definable)
            | Token::Prec
            | Token::Preceq
            | Token::Succ
            | Token::Succeq
            | Token::Ll
            | Token::Gg
            | Token::Sim
            | Token::Simeq
            | Token::Asymp
            | Token::Approx
            | Token::Cong
            | Token::Doteq
            | Token::Propto
            // Set operations (can be overloaded)
            | Token::Union
            | Token::Intersect
            | Token::SetMinus
            | Token::Times
            // Bag/multiset operations
            | Token::Sqsubseteq
            | Token::Sqsupseteq
            // Range operator (user-definable)
            | Token::DotDot
    )
}

/// Check if a token can appear after ! in a module reference
/// e.g., R!+(a, b) references the + operator from module R
pub(super) fn is_module_ref_operator(token: Token) -> bool {
    matches!(
        token,
        // Arithmetic operators
        Token::Plus
            | Token::Minus
            | Token::Star
            | Token::Slash
            | Token::Percent
            | Token::Caret
            // TLA+ operators
            | Token::Leq
            | Token::Geq
            | Token::Lt
            | Token::Gt
            | Token::Eq
            | Token::Neq
            // Set operations
            | Token::Union
            | Token::Intersect
            | Token::SetMinus
            | Token::Times
            | Token::In_
            | Token::NotIn
            | Token::Subseteq
            | Token::Subset
            | Token::Supseteq
            | Token::Supset
            // Logical operators
            | Token::And
            | Token::Or
            | Token::Not
            | Token::Implies
            | Token::Equiv
            // Ordering relations
            | Token::Prec
            | Token::Preceq
            | Token::Succ
            | Token::Succeq
            // Other user-definable operators
            | Token::Concat
            | Token::Pipe
            | Token::Dollar
            | Token::DollarDollar
            | Token::Question
            | Token::Amp
    )
}

/// Check if a keyword token can be used as a record field name after `.`
///
/// TLC/SANY allows all keywords as record field names. For example:
///   bar.RECURSIVE, bar.NEW, bar.BY, bar.LAMBDA, etc.
/// and in EXCEPT specs: `[bar EXCEPT !.RECURSIVE = 0]`
///
/// Reference: tlaplus/test208 — tests every keyword as a field name.
pub(super) fn is_keyword_as_field_name(token: Token) -> bool {
    matches!(
        token,
        // Module structure
        Token::Module
            | Token::Extends
            | Token::Instance
            | Token::With
            | Token::Local
            // Declarations
            | Token::Variable
            | Token::Constant
            | Token::Assume
            | Token::Theorem
            | Token::Lemma
            | Token::Proposition
            | Token::Corollary
            | Token::Axiom
            // Proof keywords
            | Token::Proof
            | Token::By
            | Token::Obvious
            | Token::Omitted
            | Token::Qed
            | Token::Suffices
            | Token::Have
            | Token::Take
            | Token::Witness
            | Token::Pick
            | Token::Use
            | Token::Hide
            | Token::Define
            | Token::Defs
            | Token::Def
            | Token::Only
            | Token::New
            // Logic
            | Token::True
            | Token::False
            | Token::Boolean
            | Token::If
            | Token::Then
            | Token::Else
            | Token::Case
            | Token::Other
            | Token::Let
            | Token::In
            | Token::Lambda
            // Quantifiers
            | Token::Recursive
            | Token::Choose
            // Temporal & state
            | Token::Enabled
            | Token::Unchanged
            | Token::WeakFair
            | Token::StrongFair
            // Set/function keywords
            | Token::Powerset
            | Token::BigUnion
            | Token::Domain
            | Token::Except
            // Stdlib names
            | Token::Seq
            | Token::Append
            | Token::Head
            | Token::Tail
            | Token::Len
            | Token::SubSeq
            | Token::SelectSeq
    )
}

/// Check if a token is a standard library function name that can be used as an operator name
/// These are tokenized as keywords but in standard modules they need to be defined as operators
pub(super) fn is_stdlib_operator_name(token: Token) -> bool {
    matches!(
        token,
        Token::Seq
            | Token::Append
            | Token::Head
            | Token::Tail
            | Token::Len
            | Token::SubSeq
            | Token::SelectSeq
            | Token::Concat
    )
}

/// Get binding power for infix operators
pub(super) fn infix_binding_power(op: Token) -> Option<(u8, u8)> {
    let bp = match op {
        // Lowest precedence: equivalence
        Token::Equiv => (1, 2),

        // Implication (right associative)
        Token::Implies => (3, 2),

        // Disjunction
        Token::Or => (5, 6),

        // Conjunction
        Token::And => (7, 8),

        // Comparison
        Token::Eq
        | Token::Neq
        | Token::Lt
        | Token::Gt
        | Token::Leq
        | Token::Geq
        | Token::ColonColonEq
        | Token::ColonEq
        // Apalache type annotation
        | Token::LtColon => (9, 10),

        // Ordering relations (user-definable, same precedence as comparison)
        Token::Prec
        | Token::Preceq
        | Token::Succ
        | Token::Succeq
        | Token::Ll
        | Token::Gg
        | Token::Sim
        | Token::Simeq
        | Token::Asymp
        | Token::Approx
        | Token::Cong
        | Token::Doteq
        | Token::Propto => (9, 10),

        // Set membership and subset/superset
        Token::In_
        | Token::NotIn
        | Token::Subseteq
        | Token::Subset
        | Token::Supseteq
        | Token::Supset => (11, 12),

        // Bag subset operators (same precedence as set subset)
        Token::Sqsubseteq | Token::Sqsupseteq => (11, 12),

        // Set operations
        Token::Union | Token::Intersect | Token::SetMinus => (13, 14),

        // Range
        Token::DotDot => (15, 16),

        // Additive (including multi-char variants)
        Token::Plus | Token::Minus | Token::PlusPlus | Token::MinusMinus => (17, 18),

        // Multiplicative (including multi-char variants)
        Token::Star
        | Token::Slash
        | Token::Div
        | Token::Percent
        | Token::StarStar
        | Token::SlashSlash
        | Token::PercentPercent => (19, 20),

        // Exponentiation (right associative, including multi-char variant)
        Token::Caret | Token::CaretCaret => (22, 21),

        // Circled operators (same precedence as multiplicative)
        Token::Oplus
        | Token::Ominus
        | Token::Otimes
        | Token::Oslash
        | Token::Odot
        | Token::Uplus
        | Token::Sqcap
        | Token::Sqcup => (19, 20),

        // Action composition (\cdot)
        Token::Cdot => (19, 20),

        // Temporal leads-to
        Token::LeadsTo => (4, 3),

        // Cartesian product
        Token::Times => (15, 16),

        // Function composition
        Token::Concat => (17, 18),

        // String concat, function combine
        // Note: @@ has lower precedence than :> so that 1:>2 @@ 2:>3 parses as (1:>2) @@ (2:>3)
        Token::AtAt => (13, 14),

        // User-defined infix operator (like a | b for divisibility)
        Token::Pipe => (11, 12),

        // Bitwise AND (user-defined, including double variant)
        Token::Amp | Token::AmpAmp => (19, 20),

        // Function mapping :> (from Sequences standard module)
        // Higher precedence than @@ so that 1:>2 @@ 2:>3 parses as (1:>2) @@ (2:>3)
        Token::ColonGt => (15, 16),

        _ => return None,
    };
    Some(bp)
}
