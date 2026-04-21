---- MODULE MemTestSimpleAction ----
\* Minimal test - just add an action that modifies consumed
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Readers, Writers, Size, NULL

VARIABLES consumed, ringbuffer, next_sequence, pc, claimed_sequence, published, read

Buffer == INSTANCE RingBufferDebug WITH Values <- Int

Access  == "Access"
Advance == "Advance"

Transition(t, from, to) ==
    /\ pc[t] = from
    /\ pc' = [pc EXCEPT ![t] = to]

Range(f) == {f[x] : x \in DOMAIN f}

MinReadSequence ==
    CHOOSE min \in Range(read) :
        \A r \in Readers : min <= read[r]

Init ==
    /\ consumed = [r \in Readers |-> <<>>]
    /\ Buffer!Init
    /\ next_sequence = 0
    /\ pc = [a \in Writers \cup Readers |-> Advance]
    /\ claimed_sequence = [w \in Writers |-> -1]
    /\ published = [i \in 0..Buffer!LastIndex |-> FALSE]
    /\ read = [r \in Readers |-> -1]

BeginWrite(writer) ==
    LET seq == next_sequence
        index == Buffer!IndexOf(seq)
        min_read == MinReadSequence
    IN
        /\ min_read >= seq - Size
        /\ claimed_sequence' = [claimed_sequence EXCEPT ![writer] = seq]
        /\ next_sequence' = seq + 1
        /\ Transition(writer, Advance, Access)
        /\ Buffer!Write(index, writer, seq)
        /\ UNCHANGED <<consumed, published, read>>

\* Very simple action that just appends to consumed
SimpleRead(reader) ==
    /\ consumed' = [consumed EXCEPT ![reader] = Append(@, 42)]
    /\ UNCHANGED <<ringbuffer, next_sequence, pc, claimed_sequence, published, read>>

Next ==
    \/ \E w \in Writers: BeginWrite(w)
    \/ \E r \in Readers: SimpleRead(r)

InvConsumed == consumed \in [Readers -> Seq(Nat)]

====
