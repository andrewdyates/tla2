---- MODULE negative_test ----
\* Bug #303: Exact reproduction from issue report
EXTENDS Integers, TLC

VARIABLE x

\* BUG: This evaluates to FALSE when x = -1
TestBug == -1 \in Nat \union {-1}

\* OK: These work correctly
TestNegOneSet == -1 \in {-1}
TestNegOneExplicit == -1 \in {-1, 0, 1}

Init == x = -1
Next == UNCHANGED x
Spec == Init /\ [][Next]_x
====
