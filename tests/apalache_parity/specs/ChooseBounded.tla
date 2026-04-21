---- MODULE ChooseBounded ----
\* CHOOSE: bounded CHOOSE from finite set.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals
VARIABLE picked

S == {10, 20, 30}

Init == picked = CHOOSE v \in S : v >= 20
Next == UNCHANGED picked

InSetOK == picked \in S
GeOK == picked >= 20
MinChoose == LET m == CHOOSE v \in {1, 2, 3} : \A w \in {1, 2, 3} : v <= w
             IN m = 1
====
