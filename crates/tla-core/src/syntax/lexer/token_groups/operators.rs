// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

macro_rules! push_operator_tokens {
    ($callback:ident, [$($acc:tt)*]) => {
        push_surface_tokens!(
            $callback,
            [
                $($acc)*
                // === Set Operators ===
                #[token("\\in")]
                In_,

                #[token("\\notin")]
                NotIn,

                #[token("\\cup")]
                #[token("\\union")]
                Union,

                #[token("\\cap")]
                #[token("\\intersect")]
                Intersect,

                #[token("\\")]
                #[token("\\setminus")]
                SetMinus,

                #[token("\\subseteq")]
                Subseteq,

                #[token("\\subset")]
                Subset,

                #[token("\\supseteq")]
                Supseteq,

                #[token("\\supset")]
                Supset,

                #[token("\\sqsubseteq")]
                Sqsubseteq,

                #[token("\\sqsupseteq")]
                Sqsupseteq,

                #[token("SUBSET")]
                Powerset,

                #[token("UNION")]
                BigUnion,

                #[token("INTER")]
                BigIntersect,

                // === Temporal Operators ===
                #[token("[]")]
                Always,

                #[token("<>")]
                Eventually,

                #[token("~>")]
                LeadsTo,

                #[token("ENABLED")]
                Enabled,

                #[token("UNCHANGED")]
                Unchanged,

                #[token("WF_", priority = 10)]
                WeakFair,

                #[token("SF_", priority = 10)]
                StrongFair,

                // === Logical Operators ===
                #[token("/\\")]
                #[token("\\land")]
                And,

                #[token("\\/")]
                #[token("\\lor")]
                Or,

                #[token("~")]
                #[token("\\lnot")]
                #[token("\\neg")]
                Not,

                #[token("=>")]
                Implies,

                #[token("<=>")]
                #[token("\\equiv")]
                Equiv,

                // === Comparison ===
                #[token("=")]
                Eq,

                #[token("#")]
                #[token("/=")]
                #[token("\\neq")]
                Neq,

                #[token("<")]
                Lt,

                #[token(">")]
                Gt,

                #[token("<=")]
                #[token("=<")]
                #[token("\\leq")]
                Leq,

                #[token(">=")]
                #[token("\\geq")]
                Geq,

                // === Ordering Relations (user-definable) ===
                #[token("\\prec")]
                Prec,

                #[token("\\preceq")]
                Preceq,

                #[token("\\succ")]
                Succ,

                #[token("\\succeq")]
                Succeq,

                #[token("\\ll")]
                Ll,

                #[token("\\gg")]
                Gg,

                #[token("\\sim")]
                Sim,

                #[token("\\simeq")]
                Simeq,

                #[token("\\asymp")]
                Asymp,

                #[token("\\approx")]
                Approx,

                #[token("\\cong")]
                Cong,

                #[token("\\doteq")]
                Doteq,

                #[token("\\propto")]
                Propto,

                // Action composition
                #[token("\\cdot")]
                Cdot,

                // === Arithmetic ===
                #[token("+")]
                Plus,

                #[token("-")]
                Minus,

                #[token("*")]
                Star,

                #[token("/")]
                Slash,

                #[token("^")]
                Caret,

                #[token("%")]
                Percent,

                #[token("\\div")]
                Div,

                #[token("..")]
                DotDot,

                // === Multi-character user-definable operators ===
                #[token("++")]
                PlusPlus,

                #[token("--")]
                MinusMinus,

                #[token("**")]
                StarStar,

                #[token("//")]
                SlashSlash,

                #[token("^^")]
                CaretCaret,

                #[token("%%")]
                PercentPercent,

                #[token("&&")]
                AmpAmp,

                // Circled operators (user-definable)
                #[token("\\oplus")]
                Oplus,

                #[token("\\ominus")]
                Ominus,

                #[token("\\otimes")]
                Otimes,

                #[token("\\oslash")]
                Oslash,

                #[token("\\odot")]
                Odot,

                #[token("\\uplus")]
                Uplus,

                #[token("\\sqcap")]
                Sqcap,

                #[token("\\sqcup")]
                Sqcup,

                // === Definition and Assignment ===
                #[token("==")]
                DefEq,

                #[token("'")]
                Prime,

                #[token("\\triangleq")]
                TriangleEq,
            ]
        );
    };
}
