---- MODULE test_409_renamed ----
\* Same as test_409 but with state variable renamed to avoid conflict
\* with the & operator's parameter 'x'

EXTENDS Integers

\* Define bitwise AND inline (simplified from Bits.tla)
RECURSIVE And(_, _, _, _)
And(x, y, n, m) ==
    LET exp == 2^n
    IN IF m = 0 THEN 0
       ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2)
            + And(x, y, n+1, m \div 2)

x & y == And(x, y, 0, x)

\* This operator contains bitwise ops
HasBit(val, bit) == (val & bit) = bit

\* RENAMED from 'x' to 'state' to avoid conflict with & parameter
VARIABLE state

Init == state = 0

\* Should work now with renamed variable
Next == \E v \in {1, 2, 3}:
          /\ HasBit(7, v)
          /\ state' = v

====
