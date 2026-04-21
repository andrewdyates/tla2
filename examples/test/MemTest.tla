---- MODULE MemTest ----
\* Minimal test for function set membership
EXTENDS Integers, Sequences

CONSTANTS Readers

VARIABLES consumed

Init ==
    consumed = [r \in Readers |-> <<>>]

Next ==
    UNCHANGED consumed

\* This should always be TRUE
InvConsumed == consumed \in [Readers -> Seq(Nat)]

====
