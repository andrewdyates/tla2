---- MODULE SkolemIdentity ----
\* Apalache annotation operators: Skolem, Expand, ConstCardinality.
\* These are identity ops in BFS mode (hints for symbolic engine).
\* Expected: model check passes.
EXTENDS Apalache, Naturals, FiniteSets
VARIABLE x
Init == x \in {1, 2, 3}
Next == UNCHANGED x
SkolemOK == Skolem(\E y \in {1, 2, 3} : y = x)
ExpandOK == x \in Expand({1, 2, 3})
CardOK == ConstCardinality(Cardinality({1, 2, 3})) = 3
====
