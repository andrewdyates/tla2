---- MODULE test_let_cache_next ----
\* Minimal reproduction for #378: LET caching bug in RECURSIVE functions
\*
\* Expected: No deadlock, 1 state found
\* Bug: Deadlock because LET exp == 2^n returns cached values from Init in Next context
\*
\* Related issues: #378, #376
EXTENDS Naturals, TLC

RECURSIVE And(_,_,_,_)
LOCAL And(x,y,n,m) == LET exp == 2^n
                IN IF m = 0
                   THEN 0
                   ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2)
                        + And(x,y,n+1,m \div 2)

x & y == And(x, y, 0, x)

VARIABLE v

Init == v = 31
     /\ PrintT(<<"Init: 31 & 1 =", 31 & 1>>)
     /\ PrintT(<<"Init: 31 & 2 =", 31 & 2>>)
     /\ PrintT(<<"Init: 31 & 4 =", 31 & 4>>)

\* If the bug is fixed, all three conditions should be TRUE:
\* 31 & 1 = 1, 31 & 2 = 2, 31 & 4 = 4
\* With the bug, we get wrong values (5, 0, 0) causing deadlock
Next == \E d \in {1, 2, 4}:
            /\ PrintT(<<"Next: v & d =", v & d, "d =", d>>)
            /\ v & d = d
            /\ v' = v

====
