---- MODULE InvCheckTest ----
\* Test invariant checking on init states - no transitions
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Readers, Writers, Size, NULL

VARIABLES consumed, pc, ringbuffer, next_sequence, claimed_sequence, published, read

LastIndex == Size - 1

Init ==
    /\ consumed = [r \in Readers |-> <<>>]
    /\ pc = [a \in Readers \cup Writers |-> "Advance"]
    /\ ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        readers |-> [i \in 0..LastIndex |-> {}],
        writers |-> [i \in 0..LastIndex |-> {}]
       ]
    /\ next_sequence = 0
    /\ claimed_sequence = [w \in Writers |-> -1]
    /\ published = [i \in 0..LastIndex |-> FALSE]
    /\ read = [r \in Readers |-> -1]

\* No actual next actions - just self-loop
Next == UNCHANGED <<consumed, pc, ringbuffer, next_sequence, claimed_sequence, published, read>>

InvConsumed == consumed \in [Readers -> Seq(Nat)]

vars == <<consumed, pc, ringbuffer, next_sequence, claimed_sequence, published, read>>

====
