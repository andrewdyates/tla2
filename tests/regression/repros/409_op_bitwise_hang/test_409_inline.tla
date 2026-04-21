---- MODULE test_409_inline ----
\* Same as test_409 but with bitwise expression inlined (should work)

EXTENDS Integers

\* Define bitwise AND inline (simplified from Bits.tla)
RECURSIVE And(_, _, _, _)
And(x, y, n, m) ==
    LET exp == 2^n
    IN IF m = 0 THEN 0
       ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2)
            + And(x, y, n+1, m \div 2)

x & y == And(x, y, 0, x)

VARIABLE x

Init == x = 0

\* WORKS: bitwise expression inlined directly
Next == \E v \in {1, 2, 3}:
          /\ (7 & v) = v  \* <-- inline expression works
          /\ x' = v

====
