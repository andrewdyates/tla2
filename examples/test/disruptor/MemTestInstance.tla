---- MODULE MemTestInstance ----
\* Test for function set membership with INSTANCE
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Readers, Writers, Size, NULL

VARIABLES consumed, ringbuffer, next_sequence, pc, claimed_sequence, published, read

Buffer == INSTANCE RingBufferDebug WITH Values <- Int

Init ==
    /\ consumed = [r \in Readers |-> <<>>]
    /\ Buffer!Init
    /\ next_sequence = 0
    /\ pc = [a \in Writers \cup Readers |-> "Advance"]
    /\ claimed_sequence = [w \in Writers |-> -1]
    /\ published = [i \in 0..Buffer!LastIndex |-> FALSE]
    /\ read = [r \in Readers |-> -1]

Next ==
    UNCHANGED <<consumed, ringbuffer, next_sequence, pc, claimed_sequence, published, read>>

\* This should always be TRUE
InvConsumed == consumed \in [Readers -> Seq(Nat)]

====
