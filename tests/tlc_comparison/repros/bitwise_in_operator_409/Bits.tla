\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Minimal Bits module used to reproduce #376.
---- MODULE Bits ----
EXTENDS Integers

RECURSIVE And(_, _, _, _)

And(x, y, n, m) ==
    LET exp == 2^n
    IN IF m = 0 THEN 0
       ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2)
            + And(x, y, n+1, m \div 2)

x & y == And(x, y, 0, x)

====

