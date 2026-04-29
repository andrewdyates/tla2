// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use logos::Logos;

use super::Token;

/// Lex TLA+ source code into tokens (including whitespace).
/// Only used in lexer tests - the parser uses `Token::lexer()` directly.
fn lex_all(source: &str) -> impl Iterator<Item = (Token, &str)> {
    Token::lexer(source)
        .spanned()
        .filter_map(|(result, span)| result.ok().map(|token| (token, &source[span])))
}

/// Lex TLA+ source code into non-whitespace tokens only (for tests).
fn lex(source: &str) -> impl Iterator<Item = (Token, &str)> {
    lex_all(source).filter(|(token, _)| *token != Token::Whitespace)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_basic_tokens() {
    let source = "MODULE Test";
    let tokens: Vec<_> = lex(source).collect();
    assert_eq!(
        tokens,
        vec![(Token::Module, "MODULE"), (Token::Ident, "Test"),]
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_operators() {
    let source = "x == y /\\ z";
    let tokens: Vec<_> = lex(source).collect();
    assert_eq!(
        tokens,
        vec![
            (Token::Ident, "x"),
            (Token::DefEq, "=="),
            (Token::Ident, "y"),
            (Token::And, "/\\"),
            (Token::Ident, "z"),
        ]
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantifiers() {
    let source = "\\A x \\in S : P(x)";
    let tokens: Vec<_> = lex(source).collect();
    assert_eq!(
        tokens,
        vec![
            (Token::Forall, "\\A"),
            (Token::Ident, "x"),
            (Token::In_, "\\in"),
            (Token::Ident, "S"),
            (Token::Colon, ":"),
            (Token::Ident, "P"),
            (Token::LParen, "("),
            (Token::Ident, "x"),
            (Token::RParen, ")"),
        ]
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_numbers_and_strings() {
    let source = r#"x = 42 /\ y = "hello""#;
    let tokens: Vec<_> = lex(source).collect();
    assert_eq!(tokens[2], (Token::Number, "42"));
    assert_eq!(tokens[6], (Token::String, r#""hello""#));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_comments() {
    let source = "x \\* this is a comment\ny";
    let tokens: Vec<_> = lex(source).collect();
    assert_eq!(tokens.len(), 3);
    assert_eq!(tokens[1].0, Token::LineComment);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_block_comments() {
    // Simple block comment
    let source = "(* hello *)";
    let tokens: Vec<_> = lex(source).collect();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].0, Token::BlockComment);

    // Decorative comment (many asterisks)
    let source = "(********************)";
    let tokens: Vec<_> = lex(source).collect();
    assert_eq!(tokens.len(), 1, "Decorative comment should be one token");
    assert_eq!(tokens[0].0, Token::BlockComment);

    // Comment followed by code
    let source = "(****)\nx == 1";
    let tokens: Vec<_> = lex(source).collect();
    eprintln!("Tokens for comment+code: {tokens:?}");
    assert!(
        tokens.len() >= 4,
        "Should have comment + identifier + == + 1"
    );
    assert_eq!(tokens[0].0, Token::BlockComment);
    assert_eq!(tokens[1].0, Token::Ident);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_decorative_comments() {
    // Test various block comment patterns including decorative lines with many asterisks
    let patterns = [
        "(* x *)",
        "(***)",
        "(****)",
        "(*****)",
        "(******)",
        "(***************************************************************************)",
    ];

    for pattern in patterns {
        let tokens: Vec<_> = lex(pattern).collect();
        assert!(!tokens.is_empty(), "Pattern {pattern:?} should tokenize");
        assert_eq!(
            tokens[0].0,
            Token::BlockComment,
            "Pattern {pattern:?} should be BlockComment"
        );
    }

    // Block comment followed by code
    let source = "(*****)\nTypeOK == stuff";
    let tokens: Vec<_> = lex(source).collect();
    assert!(
        tokens.len() >= 4,
        "Should have comment + identifier + == + identifier"
    );
    assert_eq!(tokens[0].0, Token::BlockComment);
    assert_eq!(tokens[1].0, Token::Ident);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_subscript_tokenization() {
    // Test underscore-prefixed identifier tokenization
    // _vars is now a single Ident token (for Apalache compatibility)
    let src = "_vars";
    let tokens: Vec<_> = lex(src).collect();
    assert_eq!(tokens.len(), 1, "Expected 1 token for '_vars'");
    assert_eq!(tokens[0].0, Token::Ident);
    assert_eq!(tokens[0].1, "_vars");

    // Single underscore remains a separate token
    let src2 = "_";
    let tokens2: Vec<_> = lex(src2).collect();
    assert_eq!(tokens2.len(), 1, "Expected 1 token for '_'");
    assert_eq!(tokens2[0].0, Token::Underscore);

    // Double underscore followed by identifier is a single Ident
    let src3 = "__x";
    let tokens3: Vec<_> = lex(src3).collect();
    assert_eq!(tokens3.len(), 1, "Expected 1 token for '__x'");
    assert_eq!(tokens3[0].0, Token::Ident);
    assert_eq!(tokens3[0].1, "__x");

    // Part of #447: Underscore + digits: _123 is a valid identifier
    // (regex: _+[a-zA-Z0-9][a-zA-Z0-9_]* matches _ + 1 + 23)
    let src4 = "_123";
    let tokens4: Vec<_> = lex(src4).collect();
    assert_eq!(tokens4.len(), 1, "Expected 1 token for '_123'");
    assert_eq!(tokens4[0].0, Token::Ident);
    assert_eq!(tokens4[0].1, "_123");

    // Part of #447: Edge case: `__` alone (multiple underscores, no alphanumeric)
    // The regex `_+[a-zA-Z0-9]...` greedily consumes both underscores but fails
    // because no alphanumeric follows. This results in a lexer error (0 tokens).
    // This is edge case behavior - `__` alone is not valid TLA+ anyway.
    let src5 = "__";
    let tokens5: Vec<_> = lex(src5).collect();
    assert_eq!(
        tokens5.len(),
        0,
        "'__' alone produces lexer error (0 tokens)"
    );

    // Part of #447: Triple underscore followed by alphanumeric is still one Ident
    let src6 = "___foo";
    let tokens6: Vec<_> = lex(src6).collect();
    assert_eq!(tokens6.len(), 1, "Expected 1 token for '___foo'");
    assert_eq!(tokens6[0].0, Token::Ident);
    assert_eq!(tokens6[0].1, "___foo");

    // Part of #447: Multiple underscores followed by digit
    let src7 = "__1";
    let tokens7: Vec<_> = lex(src7).collect();
    assert_eq!(tokens7.len(), 1, "Expected 1 token for '__1'");
    assert_eq!(tokens7[0].0, Token::Ident);
    assert_eq!(tokens7[0].1, "__1");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_proof_step_tokens() {
    // Test tokenization of proof step labels
    let src = "<1>. QED";
    let tokens: Vec<_> = lex(src).collect();
    eprintln!("Tokens for '<1>. QED': {tokens:?}");
    assert_eq!(tokens[0].0, Token::Lt);
    assert_eq!(tokens[1].0, Token::Number);
    assert_eq!(tokens[2].0, Token::Gt);
    assert_eq!(tokens[3].0, Token::Dot);
    assert_eq!(tokens[4].0, Token::Qed);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_proof_step_with_label() {
    // Test tokenization of proof step labels with numeric suffix
    let src = "<1>2. Foo";
    let tokens: Vec<_> = lex(src).collect();
    eprintln!("Tokens for '<1>2. Foo': {tokens:?}");
    assert_eq!(tokens[0].0, Token::Lt);
    assert_eq!(tokens[1].0, Token::Number);
    assert_eq!(tokens[1].1, "1");
    assert_eq!(tokens[2].0, Token::Gt);
    assert_eq!(tokens[3].0, Token::Number);
    assert_eq!(tokens[3].1, "2");
    assert_eq!(tokens[4].0, Token::Dot);
    assert_eq!(tokens[5].0, Token::Ident);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_number_prefixed_identifiers() {
    // TLA+ allows number-prefixed identifiers like 1aMessage, 2avMessage
    // commonly used in consensus algorithm specs (Paxos, BFT, etc.)
    let src = "1aMessage 2avMessage 1bMessage 1cMessage";
    let tokens: Vec<_> = lex(src).collect();
    eprintln!("Tokens for number-prefixed identifiers: {tokens:?}");
    assert_eq!(tokens.len(), 4);
    assert_eq!(tokens[0], (Token::Ident, "1aMessage"));
    assert_eq!(tokens[1], (Token::Ident, "2avMessage"));
    assert_eq!(tokens[2], (Token::Ident, "1bMessage"));
    assert_eq!(tokens[3], (Token::Ident, "1cMessage"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_number_prefixed_in_definition() {
    // Test in context of operator definition
    let src = "1aMessage == [type : {\"1a\"}, bal : Ballot]";
    let tokens: Vec<_> = lex(src).collect();
    assert_eq!(tokens[0], (Token::Ident, "1aMessage"));
    assert_eq!(tokens[1], (Token::DefEq, "=="));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_number_prefixed_complex() {
    // Test various number-prefixed identifier patterns
    let src = "1bOr2bMsgs";
    let tokens: Vec<_> = lex(src).collect();
    eprintln!("Tokens for '1bOr2bMsgs': {tokens:?}");
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0], (Token::Ident, "1bOr2bMsgs"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_wf_sf_tokenization() {
    // WF_xxx and SF_xxx are tokenized as single identifiers due to lexer "maximal munch".
    // This is correct behavior - the lowering phase (lower.rs) handles converting
    // WF_xxx/SF_xxx identifiers to proper WeakFair/StrongFair AST nodes.
    let src = "WF_vars";
    let tokens: Vec<_> = lex(src).collect();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0], (Token::Ident, "WF_vars"));

    let src2 = "SF_cvars";
    let tokens2: Vec<_> = lex(src2).collect();
    assert_eq!(tokens2.len(), 1);
    assert_eq!(tokens2[0], (Token::Ident, "SF_cvars"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_colon_eq_tokenization() {
    // Regression test for #446: ColonEqOp added but untested
    // The := operator is used by Apalache for assignment

    // Test standalone :=
    let src = ":=";
    let tokens: Vec<_> = lex(src).collect();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0], (Token::ColonEq, ":="));

    // Test := in context (x := 1)
    let src2 = "x := 1";
    let tokens2: Vec<_> = lex(src2).collect();
    assert_eq!(tokens2.len(), 3);
    assert_eq!(tokens2[0], (Token::Ident, "x"));
    assert_eq!(tokens2[1], (Token::ColonEq, ":="));
    assert_eq!(tokens2[2], (Token::Number, "1"));

    // Ensure := is distinct from ::= (BNF operator)
    let src3 = "::=";
    let tokens3: Vec<_> = lex(src3).collect();
    assert_eq!(tokens3.len(), 1);
    assert_eq!(tokens3[0], (Token::ColonColonEq, "::="));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lt_colon_tokenization() {
    // Apalache <: type annotation operator (Gap 13, #3761)

    // Test standalone <:
    let src = "<:";
    let tokens: Vec<_> = lex(src).collect();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0], (Token::LtColon, "<:"));

    // Test <: in context (a <: b)
    let src2 = "a <: b";
    let tokens2: Vec<_> = lex(src2).collect();
    assert_eq!(tokens2.len(), 3);
    assert_eq!(tokens2[0], (Token::Ident, "a"));
    assert_eq!(tokens2[1], (Token::LtColon, "<:"));
    assert_eq!(tokens2[2], (Token::Ident, "b"));

    // Ensure < alone still works
    let src3 = "a < b";
    let tokens3: Vec<_> = lex(src3).collect();
    assert_eq!(tokens3.len(), 3);
    assert_eq!(tokens3[0], (Token::Ident, "a"));
    assert_eq!(tokens3[1], (Token::Lt, "<"));
    assert_eq!(tokens3[2], (Token::Ident, "b"));

    // Ensure <: is distinct from <- (left arrow)
    let src4 = "<-";
    let tokens4: Vec<_> = lex(src4).collect();
    assert_eq!(tokens4.len(), 1);
    assert_eq!(tokens4[0], (Token::LArrow, "<-"));
}
