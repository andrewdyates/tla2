---- MODULE AgentApproval_minimal ----
\* Minimal reproduction for #320 - ModelValue union membership bug
EXTENDS Integers

VARIABLE x

TypeInvariant == x \in Nat \union {-1}

Init == x = -1

Next == x' = x

Spec == Init /\ [][Next]_x
====
