---- MODULE ConsumedTest ----
\* Exact pattern from Disruptor_MPMC
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Readers

VARIABLE consumed, pc

Init ==
    /\ consumed = [r \in Readers |-> <<>>]
    /\ pc = "init"

Next ==
    /\ pc' = "done"
    /\ UNCHANGED consumed

\* This is the exact invariant that's failing
InvConsumed == consumed \in [Readers -> Seq(Nat)]

vars == <<consumed, pc>>

====
