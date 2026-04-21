---- MODULE DisruptorDebug ----
\* Debug version of Disruptor_MPMC
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    MaxPublished, Writers, Readers, Size, NULL

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

VARIABLES
    ringbuffer, next_sequence, claimed_sequence,
    published, read, pc, consumed

vars == <<ringbuffer, next_sequence, claimed_sequence,
          published, read, consumed, pc>>

Access  == "Access"
Advance == "Advance"

Transition(t, from, to) ==
    /\ pc[t] = from
    /\ pc' = [pc EXCEPT ![t] = to]

Buffer == INSTANCE RingBufferDebug WITH Values <- Int

Range(f) == {f[x] : x \in DOMAIN f}

MinReadSequence ==
    CHOOSE min \in Range(read) :
        \A r \in Readers : min <= read[r]

MinClaimedSequence ==
    CHOOSE min \in Range(claimed_sequence) :
        \A w \in Writers : min <= claimed_sequence[w]

Init ==
    /\ Buffer!Init
    /\ next_sequence = 0
    /\ claimed_sequence = [w \in Writers |-> -1]
    /\ published = [i \in 0..Buffer!LastIndex |-> FALSE]
    /\ read = [r \in Readers |-> -1]
    /\ consumed = [r \in Readers |-> <<>>]
    /\ pc = [a \in Writers \cup Readers |-> Advance]

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
        /\ published' = [published EXCEPT ![index] = ~@]
        /\ UNCHANGED <<claimed_sequence, next_sequence, consumed, read>>

Next ==
    \/ \E w \in Writers: BeginWrite(w)
    \/ \E w \in Writers: EndWrite(w)

\* Debug invariants - split up TypeOk
InvBuffer == Buffer!TypeOk
InvSlots == Buffer!TypeOk_Slots
InvSlotsD == Buffer!TypeOk_Slots_Direct
InvReaders == Buffer!TypeOk_Readers
InvReadersD == Buffer!TypeOk_Readers_Direct
InvWriters == Buffer!TypeOk_Writers
InvWritersD == Buffer!TypeOk_Writers_Direct
InvNextSeq == next_sequence \in Nat
InvClaimed == claimed_sequence \in [Writers -> Int]
InvPublished == published \in [0..Buffer!LastIndex -> {TRUE, FALSE}]
InvRead == read \in [Readers -> Int]
InvConsumed == consumed \in [Readers -> Seq(Nat)]
InvPc == pc \in [Writers \cup Readers -> {Access, Advance}]

====
