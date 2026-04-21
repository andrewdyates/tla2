---- MODULE IntegerArithmetic ----
\* Integer operations: arithmetic, comparison, division, modulo.
\* Expected: model check passes, all invariants hold.
EXTENDS Integers
VARIABLE x

Init == x = 0
Next == x' = IF x < 10 THEN x + 1 ELSE x

AddOK == 3 + 4 = 7
SubOK == 10 - 3 = 7
MulOK == 6 * 7 = 42
DivOK == 7 \div 2 = 3
ModOK == 7 % 2 = 1
NegOK == -5 + 5 = 0
CompareOK == /\ 3 < 5
             /\ 5 > 3
             /\ 3 <= 3
             /\ 3 >= 3
RangeOK == x \in 0..10
====
