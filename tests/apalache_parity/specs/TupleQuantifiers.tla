---- MODULE TupleQuantifiers ----
\* Quantifiers over Cartesian products using tuple indexing.
\* Exercises \E t \in S \X T : t[1] and \A t \in S \X T : t[2] patterns.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals

VARIABLES x, y

S == {1, 2}
T == {3, 4}

Init == \E t \in S \X T : x = t[1] /\ y = t[2]

Next == \E t \in S \X T :
            /\ t[1] >= x
            /\ t[2] >= y
            /\ x' = t[1]
            /\ y' = t[2]

ExistsTupleOK == \E t \in S \X T : t[1] + t[2] >= 4
ForAllTupleOK == \A t \in S \X T : t[1] < t[2]
InRange == x \in S /\ y \in T
====
