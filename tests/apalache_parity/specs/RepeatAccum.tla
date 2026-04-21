---- MODULE RepeatAccum ----
\* Apalache Repeat operator: iterated application.
\* Repeat(F, 3, 0) where F(x,i) = x+i => 0+1=1, 1+2=3, 3+3=6.
\* Expected: model check passes, result invariant holds.
EXTENDS Apalache, Naturals
VARIABLE val
F(x, i) == x + i
Init == val = Repeat(F, 3, 0)
Next == UNCHANGED val
Correct == val = 6
====
