---- MODULE SetOperations ----
\* Set operations: Union, Intersect, SetMinus in BFS context.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals, FiniteSets
VARIABLE s

A == {1, 2, 3}
B == {2, 3, 4}

Init == s = A \union B
Next == UNCHANGED s

UnionOK == s = {1, 2, 3, 4}
IntersectOK == A \intersect B = {2, 3}
DiffOK == A \ B = {1}
SubsetOK == {2, 3} \subseteq A
CardOK == Cardinality(s) = 4
====
