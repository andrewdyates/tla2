---- MODULE ActionInvTestNoRead ----
\* Test without BeginRead action
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Readers, Writers, Size, NULL

VARIABLES consumed, pc, ringbuffer, next_sequence

LastIndex == Size - 1

MinReadSequence == -1

Init ==
    /\ consumed = [r \in Readers |-> <<>>]
    /\ pc = [a \in Readers \cup Writers |-> "Advance"]
    /\ ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        writers |-> [i \in 0..LastIndex |-> {}]
       ]
    /\ next_sequence = 0

BeginWrite(writer) ==
    LET seq == next_sequence
        index == seq % Size
        min_read == MinReadSequence
    IN
        /\ min_read >= seq - Size
        /\ next_sequence' = seq + 1
        /\ ringbuffer' = [ringbuffer EXCEPT
            !.slots[index] = seq,
            !.writers[index] = @ \cup {writer}]
        /\ pc' = [pc EXCEPT ![writer] = "Access"]
        /\ UNCHANGED consumed

\* No BeginRead action - removed

Next == \E w \in Writers: BeginWrite(w)

InvConsumed == consumed \in [Readers -> Seq(Nat)]

vars == <<consumed, pc, ringbuffer, next_sequence>>

====
