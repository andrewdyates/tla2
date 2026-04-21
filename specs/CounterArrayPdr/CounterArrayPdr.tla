--------------------------- MODULE CounterArrayPdr ---------------------------
\* CDEMC demo spec: BFS-impossible state space where PDR proves safety in seconds.
\*
\* 10 independent bounded counters stored in a record.
\* Each counter increments from 0 to 100, then saturates.
\*
\* BFS state space: 101^10 ~ 10^20 states (infeasible for explicit enumeration).
\* PDR: each counter is independent; the per-field bound invariant is trivially
\* inductive. PDR should prove safety in seconds by finding the per-field
\* inductive invariant 0 <= c_i <= 100.
\*
\* Part of #3957.

EXTENDS Integers

VARIABLE c

Init == c = [c1 |-> 0, c2 |-> 0, c3 |-> 0, c4 |-> 0, c5 |-> 0,
             c6 |-> 0, c7 |-> 0, c8 |-> 0, c9 |-> 0, c10 |-> 0]

Next == \/ c' = [c EXCEPT !.c1 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c2 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c3 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c4 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c5 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c6 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c7 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c8 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c9 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c10 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ UNCHANGED c

Safety == /\ c.c1 >= 0 /\ c.c1 <= 100
          /\ c.c2 >= 0 /\ c.c2 <= 100
          /\ c.c3 >= 0 /\ c.c3 <= 100
          /\ c.c4 >= 0 /\ c.c4 <= 100
          /\ c.c5 >= 0 /\ c.c5 <= 100
          /\ c.c6 >= 0 /\ c.c6 <= 100
          /\ c.c7 >= 0 /\ c.c7 <= 100
          /\ c.c8 >= 0 /\ c.c8 <= 100
          /\ c.c9 >= 0 /\ c.c9 <= 100
          /\ c.c10 >= 0 /\ c.c10 <= 100

=============================================================================
