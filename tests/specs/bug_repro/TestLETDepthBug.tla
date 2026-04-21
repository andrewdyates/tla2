---- MODULE TestLETDepthBug ----
\* Bug #304: LET binding depth bug in compiled guards
\* LET bindings that capture quantifier-bound variables fail inside nested quantifiers
\* because the depth-based LocalVar lookup gets the wrong variable.
EXTENDS Integers

VARIABLES x

Init == x = 0
Next == x < 3 /\ x' = x + 1

\* This works: no LET binding
TestNoLET ==
    \A i \in {1, 2}:
        \A j \in {3, 4}:
            i < j

\* This should also work but had a bug: k should equal i, not j
TestWithLET ==
    \A i \in {1, 2}:
        LET k == i
        IN \A j \in {3, 4}:
            k < j  \* Bug: k evaluated to j instead of i

\* Test with expression in LET, not just simple variable reference
TestWithLETExpr ==
    \A i \in {1, 2}:
        LET k == i + 10
        IN \A j \in {3, 4}:
            k > j  \* k should be 11 or 12, both > 3 or 4

\* Test double nesting
TestDoubleNest ==
    \A i \in {1, 2}:
        LET k == i
        IN \A j \in {3, 4}:
            \A m \in {5, 6}:
                k < j /\ j < m

\* Test with record access
TestWithRecord ==
    LET rec == [a |-> 1, b |-> 2]
    IN \A i \in {0, 1}:
        rec.a <= rec.b

\* Test nested LET
TestNestedLET ==
    \A i \in {1, 2}:
        LET k == i
        IN \A j \in {3, 4}:
            LET m == j
            IN k < m

====
