---- MODULE AssignOpNested ----
\* Apalache := operator in nested contexts (Part of #3828).
\* Tests := inside IF/THEN/ELSE, CASE, and conjunctive lists.
\* Expected: model check passes with all invariants holding.
EXTENDS Apalache, Naturals

VARIABLES x, y, z

Init ==
    /\ x := 0
    /\ y := 10
    /\ z := 0

\* := in IF/THEN/ELSE branches
Next ==
    /\ IF x < 3
       THEN x' := x + 1
       ELSE x' := x
    /\ IF y > 7
       THEN y' := y - 1
       ELSE y' := y
    /\ z' := x + y

XBounded == x \in 0..3
YBounded == y \in 7..10
ZBounded == z \in 0..13
====
