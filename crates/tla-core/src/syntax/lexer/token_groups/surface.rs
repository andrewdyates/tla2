// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

macro_rules! push_surface_tokens {
    ($callback:ident, [$($acc:tt)*]) => {
        $callback!([
            $($acc)*
            // === Delimiters ===
            #[token("(")]
            LParen,

            #[token(")")]
            RParen,

            #[token("[")]
            LBracket,

            #[token("]")]
            RBracket,

            #[token("{")]
            LBrace,

            #[token("}")]
            RBrace,

            #[token("<<")]
            LAngle,

            #[token(">>")]
            RAngle,

            #[token(",")]
            Comma,

            #[token("::=")]
            ColonColonEq,

            #[token(":=")]
            ColonEq,

            #[token("::")]
            ColonColon,

            #[token(":")]
            Colon,

            #[token(";")]
            Semi,

            #[token(".")]
            Dot,

            #[token("_", priority = 3)]
            Underscore,

            #[token("@")]
            At,

            #[token("!")]
            Bang,

            #[token("|->")]
            MapsTo,

            #[token("->")]
            Arrow,

            #[token("<-")]
            LArrow,

            // Apalache type annotation operator: a <: b
            #[token("<:")]
            LtColon,

            #[token("|-")]
            Turnstile,

            #[token("|")]
            Pipe,

            #[token(":>")]
            ColonGt,

            #[token("@@")]
            AtAt,

            #[token("$")]
            Dollar,

            #[token("$$")]
            DollarDollar,

            #[token("?")]
            Question,

            #[token("&")]
            Amp,

            #[token("\\X")]
            #[token("\\times")]
            Times,

            // === Function Operators ===
            #[token("DOMAIN")]
            Domain,

            #[token("EXCEPT")]
            Except,

            // === Sequence Operators ===
            #[token("Append")]
            Append,

            #[token("Head")]
            Head,

            #[token("Tail")]
            Tail,

            #[token("Len")]
            Len,

            #[token("Seq")]
            Seq,

            #[token("SubSeq")]
            SubSeq,

            #[token("SelectSeq")]
            SelectSeq,

            #[token("\\o")]
            #[token("\\circ")]
            Concat,

            // === Literals ===
            #[regex(r"[0-9]+")]
            Number,

            #[regex(r#""([^"\\]|\\.)*""#)]
            String,

            // === Identifiers ===
            // TLA+ identifiers start with a letter, followed by letters, digits, or underscores.
            // Underscore-prefixed identifiers like __x, _foo are supported for:
            // - Apalache module operators (__x := __e, Gen(__size), etc.)
            // - PlusCal-translated specs
            //
            // A single underscore `_` remains a separate Underscore token for action subscripts [A]_v.
            // But `_` followed by identifier characters becomes a single Ident token.
            // The regex `_+[a-zA-Z0-9][a-zA-Z0-9_]*` matches underscore-prefixed identifiers that have
            // at least one non-underscore character (to avoid matching a single `_`).
            //
            // Special case: TLA+ allows number-prefixed operator names like 1aMessage, 2avMessage
            // commonly used in consensus algorithm specs (e.g., Paxos). These must be tokenized
            // as identifiers, not as Number followed by Ident. The pattern matches:
            // - One or more digits followed by at least one letter, then letters/digits/underscores
            #[regex(r"[0-9]+[a-zA-Z][a-zA-Z0-9_]*")]
            #[regex(r"_+[a-zA-Z0-9][a-zA-Z0-9_]*")]
            #[regex(r"[a-zA-Z][a-zA-Z0-9_]*")]
            Ident,

            // === Comments ===
            #[regex(r"\\\*[^\n]*")]
            LineComment,

            // Block comments: (* ... *)
            // Use a callback to handle block comments with arbitrary asterisks
            #[token("(*", lex_block_comment)]
            BlockComment,
        ]);
    };
}
