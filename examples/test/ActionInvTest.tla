---- MODULE ActionInvTest ----
\* Test invariant checking with action - minimal example
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Readers, Writers, Size, NULL

VARIABLES consumed, pc, ringbuffer, next_sequence

LastIndex == Size - 1

Range(f) == {f[x] : x \in DOMAIN f}

MinReadSequence ==
    CHOOSE min \in {-1} :
        TRUE

Init ==
    /\ consumed = [r \in Readers |-> <<>>]
    /\ pc = [a \in Readers \cup Writers |-> "Advance"]
    /\ ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        writers |-> [i \in 0..LastIndex |-> {}]
       ]
    /\ next_sequence = 0

\* Simplified BeginWrite - close to the original
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

\* Read - appending to consumed
BeginRead(reader) ==
    /\ pc[reader] = "Advance"
    /\ consumed' = [consumed EXCEPT ![reader] = Append(@, ringbuffer.slots[0])]
    /\ pc' = [pc EXCEPT ![reader] = "Access"]
    /\ UNCHANGED <<ringbuffer, next_sequence>>

Next ==
    \/ \E w \in Writers: BeginWrite(w)
    \/ \E r \in Readers: BeginRead(r)

InvConsumed == consumed \in [Readers -> Seq(Nat)]

vars == <<consumed, pc, ringbuffer, next_sequence>>

====
