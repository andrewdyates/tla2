\* Author: Andrew Yates <andrewyates.name@gmail.com>
---- MODULE test_bitand2 ----
EXTENDS TLC, Integers, Bits

VARIABLE x

FilteredSet == {p \in 1..3: (p & 1) = 0}

Init == x = 1

Next == \E d \in FilteredSet: x' = d

====

