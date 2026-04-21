---- MODULE FoldSetSum ----
\* Apalache fold operator: ApaFoldSet computes set sum.
\* Expected: model check passes, sum invariant holds.
EXTENDS Apalache, Naturals
VARIABLE total
Add(a, b) == a + b
Init == total = ApaFoldSet(Add, 0, {1, 2, 3})
Next == UNCHANGED total
Correct == total = 6
====
