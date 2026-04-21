---- MODULE AssignOp ----
\* Apalache := assignment operator (Part of #3760).
\* In BFS mode, x' := e is equivalent to x' = e.
\* Expected: model check passes.
EXTENDS Apalache, Naturals
VARIABLE x
Init == x := 0
Next == IF x < 3 THEN x' := x + 1 ELSE UNCHANGED x
Bounded == x \in 0..3
====
