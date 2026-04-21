---- MODULE test_409 ----
\* Minimal reproducer for #409: Hang when calling operator with bitwise ops
\* from predicate context.
\*
\* The hang occurs when:
\* 1. An operator contains bitwise ops (x & y)
\* 2. That operator is called from inside \E ... : guard
\*
\* Inlining the same expression works fine.

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

VARIABLE x

Init == x = 0

\* HANGS: calling operator with bitwise from predicate
Next == \E v \in {1, 2, 3}:
          /\ HasBit(7, v)  \* <-- operator call hangs
          /\ x' = v

====
