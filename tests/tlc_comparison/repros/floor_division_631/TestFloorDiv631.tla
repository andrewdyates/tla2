----------------------------- MODULE TestFloorDiv631 -----------------------------
\* Author: Andrew Yates <andrewyates.name@gmail.com>
EXTENDS Integers

VARIABLES q, r

Init ==
    /\ q = (((-3)) \div 2)
    /\ r = (((-3)) % 2)

Next ==
    UNCHANGED <<q, r>>

Inv ==
    /\ q = -2
    /\ r = 1
    /\ -3 = 2 * q + r

================================================================================
