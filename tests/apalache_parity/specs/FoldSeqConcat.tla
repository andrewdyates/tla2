---- MODULE FoldSeqConcat ----
\* Apalache fold operator: ApaFoldSeqLeft sums a sequence.
\* Expected: model check passes, sum invariant holds.
EXTENDS Apalache, Naturals, Sequences
VARIABLE result
Acc(a, b) == a + b
Init == result = ApaFoldSeqLeft(Acc, 0, <<10, 20, 30>>)
Next == UNCHANGED result
Correct == result = 60
====
