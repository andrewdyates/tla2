---- MODULE ExceptDoubleEq ----
\* Apalache EXCEPT == syntax with multiple field updates (Part of #3828).
\* Tests [f EXCEPT ![k] == v] and mixed = / == in EXCEPT.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals

VARIABLE counters

Init == counters = [i \in {1, 2, 3} |-> 0]

\* Use EXCEPT == (Apalache extension) for updates, bounded transitions
Next ==
    \/ /\ counters[1] < 2
       /\ counters' = [counters EXCEPT ![1] == counters[1] + 1]
    \/ /\ counters[2] < 2 /\ counters[3] < 2
       /\ counters' = [counters EXCEPT ![2] == counters[2] + 1,
                                       ![3] == counters[3] + 1]
    \/ UNCHANGED counters

DomainOK == DOMAIN counters = {1, 2, 3}
NonNeg == \A i \in {1, 2, 3} : counters[i] >= 0
Bounded == \A i \in {1, 2, 3} : counters[i] <= 2
====
