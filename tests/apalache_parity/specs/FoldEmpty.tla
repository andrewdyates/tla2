---- MODULE FoldEmpty ----
\* Edge cases for fold: empty set, empty sequence, single-element inputs (Part of #3828).
\* Tests ApaFoldSet and ApaFoldSeqLeft with degenerate inputs.
\* Expected: model check passes with all invariants holding.
EXTENDS Apalache, Naturals, Sequences

VARIABLE x

Add(a, b) == a + b

Init == x = 0
Next == IF x < 1 THEN x' = x + 1 ELSE UNCHANGED x

\* Empty set fold returns initial value
EmptySetFold == ApaFoldSet(Add, 42, {}) = 42

\* Empty sequence fold returns initial value
EmptySeqFold == ApaFoldSeqLeft(Add, 99, <<>>) = 99

\* Single element set fold
SingleSetFold == ApaFoldSet(Add, 0, {7}) = 7

\* Single element sequence fold
SingleSeqFold == ApaFoldSeqLeft(Add, 0, <<7>>) = 7

\* Fold with string concatenation-like pattern (using arithmetic)
Max(a, b) == IF a >= b THEN a ELSE b
MaxOfSet == ApaFoldSet(Max, 0, {3, 7, 2, 9, 1}) = 9
====
