---- MODULE Counter ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
InRange == x >= 0 /\ x <= 5
====
