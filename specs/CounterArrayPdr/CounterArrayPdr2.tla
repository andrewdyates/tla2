--------------------------- MODULE CounterArrayPdr2 --------------------------
\* Small variant of CounterArrayPdr with 2 counters for BFS verification.
\* BFS state space: 101^2 = 10,201 states (feasible).
\* Used to verify correctness of the spec before scaling to 10 counters.
\*
\* Part of #3957.

EXTENDS Integers

VARIABLE c

Init == c = [c1 |-> 0, c2 |-> 0]

Next == \/ c' = [c EXCEPT !.c1 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c2 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ UNCHANGED c

Safety == /\ c.c1 >= 0 /\ c.c1 <= 100
          /\ c.c2 >= 0 /\ c.c2 <= 100

=============================================================================
