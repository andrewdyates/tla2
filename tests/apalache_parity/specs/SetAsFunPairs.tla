---- MODULE SetAsFunPairs ----
\* Apalache SetAsFun operator: set of pairs to function.
\* Expected: model check passes, function domain/range correct.
EXTENDS Apalache, Naturals
VARIABLE f
Init == f = SetAsFun({<<1, 10>>, <<2, 20>>})
Next == UNCHANGED f
Correct == f[1] = 10 /\ f[2] = 20
====
