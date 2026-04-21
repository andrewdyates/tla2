---- MODULE LambdaFold ----
\* Apalache fold with LAMBDA (anonymous operator).
\* Expected: model check passes.
EXTENDS Apalache, Naturals
VARIABLE total
Init == total = ApaFoldSet(LAMBDA a, b: a + b, 0, {10, 20, 30})
Next == UNCHANGED total
Correct == total = 60
====
