---- MODULE TestNatUnion ----
\* Bug #303: x \in Nat \union {-1} returns FALSE when x = -1
EXTENDS Integers

VARIABLE x

Init == x = -1
Next == UNCHANGED x

\* BUG: This should pass but fails
TestNatUnionBug == -1 \in Nat \union {-1}

\* These work correctly
TestNegOneSet == -1 \in {-1}
TestNegOneExplicit == -1 \in {-1, 0, 1}
TestUnionExplicit == -1 \in {0, 1, 2} \union {-1}

====
