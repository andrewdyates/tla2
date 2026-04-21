---- MODULE MemTestActions ----
\* Test for function set membership with actions
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

MinClaimedSequence ==
    CHOOSE min \in Range(claimed_sequence) :
        \A w \in Writers : min <= claimed_sequence[w]

IsPublished(sequence) ==
    LET
        index == Buffer!IndexOf(sequence)
        round == sequence \div Size
        is_even == round % 2 = 0
    IN
        published[index] = is_even

Xor(A, B) == A = ~B

Publish(sequence) ==
    LET index == Buffer!IndexOf(sequence)
    IN published' = [published EXCEPT ![index] = Xor(TRUE, @)]

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

EndWrite(writer) ==
    LET seq == claimed_sequence[writer]
        index == Buffer!IndexOf(seq)
    IN
        /\ Transition(writer, Access, Advance)
        /\ Buffer!EndWrite(index, writer)
        /\ Publish(seq)
        /\ UNCHANGED <<claimed_sequence, next_sequence, consumed, read>>

BeginRead(reader) ==
    LET next == read[reader] + 1
        index == Buffer!IndexOf(next)
    IN
        /\ IsPublished(next)
        /\ Transition(reader, Advance, Access)
        /\ Buffer!BeginRead(index, reader)
        /\ consumed' = [consumed EXCEPT ![reader] = Append(@, Buffer!Read(index))]
        /\ UNCHANGED <<claimed_sequence, next_sequence, published, read>>

EndRead(reader) ==
    LET next == read[reader] + 1
        index == Buffer!IndexOf(next)
    IN
        /\ Transition(reader, Access, Advance)
        /\ Buffer!EndRead(index, reader)
        /\ read' = [read EXCEPT ![reader] = next]
        /\ UNCHANGED <<claimed_sequence, next_sequence, consumed, published>>

Next ==
    \/ \E w \in Writers: BeginWrite(w)
    \/ \E w \in Writers: EndWrite(w)
    \/ \E r \in Readers: BeginRead(r)
    \/ \E r \in Readers: EndRead(r)

InvConsumed == consumed \in [Readers -> Seq(Nat)]

====
