// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

macro_rules! push_keyword_tokens {
    ($callback:ident) => {
        push_operator_tokens!(
            $callback,
            [
                // === Module Structure ===
                // Match 4 or more dashes (TLA+ allows variable length module headers)
                #[regex(r"-{4,}")]
                ModuleStart,
                // Match 4 or more equals signs (TLA+ allows variable length module footers)
                #[regex(r"={4,}")]
                ModuleEnd,
                #[token("MODULE")]
                Module,
                #[token("EXTENDS")]
                Extends,
                #[token("INSTANCE")]
                Instance,
                #[token("WITH")]
                With,
                #[token("LOCAL")]
                Local,
                // === Declarations ===
                #[token("VARIABLE")]
                #[token("VARIABLES")]
                Variable,
                #[token("CONSTANT")]
                #[token("CONSTANTS")]
                Constant,
                #[token("ASSUME")]
                #[token("ASSUMPTION")]
                Assume,
                #[token("THEOREM")]
                Theorem,
                #[token("LEMMA")]
                Lemma,
                #[token("PROPOSITION")]
                Proposition,
                #[token("COROLLARY")]
                Corollary,
                #[token("AXIOM")]
                Axiom,
                // === Proof Keywords ===
                #[token("PROOF")]
                Proof,
                #[token("BY")]
                By,
                #[token("OBVIOUS")]
                Obvious,
                #[token("OMITTED")]
                Omitted,
                #[token("QED")]
                Qed,
                #[token("SUFFICES")]
                Suffices,
                #[token("HAVE")]
                Have,
                #[token("TAKE")]
                Take,
                #[token("WITNESS")]
                Witness,
                #[token("PICK")]
                Pick,
                #[token("USE")]
                Use,
                #[token("HIDE")]
                Hide,
                #[token("DEFINE")]
                Define,
                #[token("DEFS")]
                Defs,
                #[token("DEF")]
                Def,
                #[token("ONLY")]
                Only,
                #[token("NEW")]
                New,
                // === Logic ===
                #[token("TRUE")]
                True,
                #[token("FALSE")]
                False,
                #[token("BOOLEAN")]
                Boolean,
                #[token("IF")]
                If,
                #[token("THEN")]
                Then,
                #[token("ELSE")]
                Else,
                #[token("CASE")]
                Case,
                #[token("OTHER")]
                Other,
                #[token("LET")]
                Let,
                #[token("IN")]
                In,
                #[token("LAMBDA")]
                Lambda,
                // === Quantifiers ===
                #[token("\\A")]
                #[token("\\forall")]
                Forall,
                #[token("\\E")]
                #[token("\\exists")]
                Exists,
                #[token("\\EE")]
                TemporalExists,
                #[token("\\AA")]
                TemporalForall,
                #[token("CHOOSE")]
                Choose,
                #[token("RECURSIVE")]
                Recursive,
            ]
        );
    };
}
