---- MODULE Quantifiers ----
\* Quantifiers: \A, \E with bounded sets.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals
VARIABLE x

S == {1, 2, 3, 4, 5}

Init == x \in S
Next == x' = IF x < 5 THEN x + 1 ELSE 1

ForAllOK == \A i \in S : i >= 1
ExistsOK == \E i \in S : i = x
BoundedForAll == \A i \in {1, 2} : \A j \in {3, 4} : i < j
NestedExists == \E i \in S : \E j \in S : i + j = 6
InRangeOK == x \in S
====
