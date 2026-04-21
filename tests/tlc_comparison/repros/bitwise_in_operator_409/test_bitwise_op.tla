\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Reproducer for #409: Calling operator with bitwise ops from predicate hangs
---- MODULE test_bitwise_op ----
EXTENDS TLC, Integers, Bits

CONSTANT D, N

PowerOfTwo(i) == i & (i-1) = 0
SetOfPowerOfTwo(n) == {x \in 1..(2^n-1): PowerOfTwo(x)}

VARIABLES towers

Init == towers = [i \in 1..N |-> 7]

\* Operator containing bitwise op - calling this from predicate hangs TLA2
IsOnTower(tower, disk) == tower & disk = disk

\* Next uses IsOnTower in predicate context - causes hang
Next == \E d \in SetOfPowerOfTwo(D): \E idx \in DOMAIN towers:
            /\ IsOnTower(towers[idx], d)
            /\ towers' = [towers EXCEPT ![idx] = towers[idx] - d]

\* Expected: TLC finds 512 distinct states, TLA2 should match (but hangs)
====
