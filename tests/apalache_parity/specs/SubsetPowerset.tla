---- MODULE SubsetPowerset ----
\* SUBSET (powerset) enumeration and filtering.
\* Exercises SUBSET S, filtering subsets by cardinality, nested SUBSET.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals, FiniteSets

VARIABLE chosen

S == {1, 2, 3}

Init == \E X \in SUBSET S : Cardinality(X) = 2 /\ chosen = X

Next == \E X \in SUBSET S :
          /\ Cardinality(X) >= 1
          /\ X # chosen
          /\ chosen' = X

PowersetSize == Cardinality(SUBSET S) = 8
ChosenSubset == chosen \subseteq S
ChosenNonempty == chosen # {}
AllSubsets == \A X \in SUBSET S : Cardinality(X) <= 3
====
