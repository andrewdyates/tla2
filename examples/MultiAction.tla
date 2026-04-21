---- MODULE MultiAction ----
EXTENDS Naturals
VARIABLE x, y

Init == x = 0 /\ y = 0

IncrementX == x < 5 /\ x' = x + 1 /\ UNCHANGED y
IncrementY == y < 3 /\ y' = y + 1 /\ UNCHANGED x
Reset == x > 3 /\ x' = 0 /\ y' = 0

Next == IncrementX \/ IncrementY \/ Reset

Bounds == x <= 5 /\ y <= 3
====
