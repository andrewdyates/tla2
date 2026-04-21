---- MODULE CaseExpressions ----
\* CASE expressions: with arms, with OTHER, and nested.
\* Exercises CASE ... [] ... [] OTHER syntax.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals

VARIABLE x

Init == x \in {0, 1, 2, 3}

Next == x' = CASE x = 0 -> 1
               [] x = 1 -> 2
               [] x = 2 -> 3
               [] x = 3 -> 0

\* CASE with OTHER clause
CaseOther(v) == CASE v = 0 -> "zero"
                  [] v = 1 -> "one"
                  [] OTHER -> "many"

CaseOtherOK == CaseOther(0) = "zero"
               /\ CaseOther(1) = "one"
               /\ CaseOther(2) = "many"

\* Nested CASE
NestedCase(v) == CASE v < 2 ->
                        CASE v = 0 -> "a"
                          [] OTHER  -> "b"
                   [] OTHER -> "c"

NestedOK == NestedCase(0) = "a"
            /\ NestedCase(1) = "b"
            /\ NestedCase(5) = "c"

InRange == x \in {0, 1, 2, 3}
====
