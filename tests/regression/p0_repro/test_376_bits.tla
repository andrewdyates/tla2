\* Author: Andrew Yates <andrewyates.name@gmail.com>
---- MODULE test_376_bits ----
\* Reproduction of #376 with Bits.tla-style And operator
EXTENDS Naturals, TLC

\* Port of And from Bits.tla community module
\* And(x,y,n,m) == LET exp == 2^n
\*                 IN IF m = 0 THEN 0
\*                    ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2) + And(x,y,n+1,m \div 2)

RECURSIVE And(_, _, _, _)
And(x, y, n, m) ==
    LET exp == 2^n
    IN IF m = 0 THEN 0
       ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2) + And(x, y, n+1, m \div 2)

\* x & y == And(x, y, 0, x)
BitwiseAnd(x, y) == And(x, y, 0, x)

\* PowerOfTwo: x is a power of two iff x & (x-1) = 0
PowerOfTwo(i) == BitwiseAnd(i, i-1) = 0

\* SetOfPowerOfTwo(n) filters 1..(2^n-1) to only powers of two
SetOfPowerOfTwo(n) == {x \in 1..(2^n-1): PowerOfTwo(x)}

VARIABLE v

Init == v = 0 /\ PrintT(<<"Init: SetOfPowerOfTwo(3) =", SetOfPowerOfTwo(3)>>)
Next == \E d \in SetOfPowerOfTwo(3): v' = d /\ PrintT(<<"Next: d =", d>>)
Spec == Init /\ [][Next]_v

====
