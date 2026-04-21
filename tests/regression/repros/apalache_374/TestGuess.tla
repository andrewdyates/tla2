---- MODULE TestGuess ----
EXTENDS Apalache

VARIABLE x

Init == x = Guess({1, 2, 3})
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

====
