---- MODULE DisjunctiveActions ----
\* Multi-action Next with disjunctive sub-actions and UNCHANGED.
\* Exercises the common pattern of named actions combined with \/.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals

VARIABLES counter, phase

Init == counter = 0 /\ phase = "A"

Increment ==
  /\ phase \in {"A", "B"}
  /\ counter < 3
  /\ counter' = counter + 1
  /\ phase' = IF phase = "A" THEN "B" ELSE "A"

Reset ==
  /\ counter > 0
  /\ counter' = 0
  /\ phase' = "A"

Hold ==
  /\ counter = 3
  /\ UNCHANGED <<counter, phase>>

Next == Increment \/ Reset \/ Hold

TypeOK == counter \in 0..3 /\ phase \in {"A", "B"}
CounterBound == counter <= 3
PhaseConsistent == (counter = 0) => (phase = "A")
====
