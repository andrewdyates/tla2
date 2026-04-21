---- MODULE ConstantsAndSymmetry ----
\* CONSTANT declarations with config substitution (Part of #3828).
\* Tests CONSTANT with specific values assigned in config.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals, FiniteSets

CONSTANT N, Vals

VARIABLE state

Init == state = [i \in 1..N |-> CHOOSE v \in Vals : TRUE]

Next ==
    \E i \in 1..N, v \in Vals :
        state' = [state EXCEPT ![i] = v]

\* Invariants
DomainOK == DOMAIN state = 1..N
ValsOK == \A i \in 1..N : state[i] \in Vals
CardOK == Cardinality(Vals) >= 1
====
