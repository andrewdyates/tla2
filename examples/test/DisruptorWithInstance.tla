---- MODULE DisruptorWithInstance ----
\* Minimal Disruptor using actual INSTANCE of RingBuffer
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Writers, Readers, Size, MaxPublished, NULL

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

\* Use INSTANCE with Values <- Int just like the original
Buffer == INSTANCE DisruptorRingBuffer WITH Values <- Int

Range(f) == {f[x] : x \in DOMAIN f}

MinReadSequence ==
    CHOOSE min \in Range(read) :
        \A r \in Readers : min <= read[r]

Init ==
    /\ Buffer!Init
    /\ next_sequence = 0
    /\ claimed_sequence = [w \in Writers |-> -1]
    /\ published = [i \in 0..Buffer!LastIndex |-> FALSE]
    /\ read = [r \in Readers |-> -1]
    /\ pc = [t \in Writers \cup Readers |-> Advance]
    /\ consumed = [r \in Readers |-> <<>>]

ClaimSlot(w) ==
    /\ pc[w] = Advance
    /\ claimed_sequence[w] = -1
    /\ next_sequence - MinReadSequence < Size
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = next_sequence]
    /\ next_sequence' = next_sequence + 1
    /\ Buffer!Write(Buffer!IndexOf(next_sequence), w, next_sequence)
    /\ pc' = [pc EXCEPT ![w] = Access]
    /\ UNCHANGED <<published, read, consumed>>

ReleaseSlot(w) ==
    /\ pc[w] = Access
    /\ claimed_sequence[w] >= 0
    /\ Buffer!EndWrite(Buffer!IndexOf(claimed_sequence[w]), w)
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = -1]
    /\ pc' = [pc EXCEPT ![w] = Advance]
    /\ UNCHANGED <<next_sequence, published, read, consumed>>

Next ==
    \/ \E w \in Writers: ClaimSlot(w)
    \/ \E w \in Writers: ReleaseSlot(w)

\* TypeOk using Buffer!TypeOk
TypeOk ==
    /\ Buffer!TypeOk
    /\ next_sequence \in Nat
    /\ claimed_sequence \in [Writers -> Int]
    /\ published \in [0..Buffer!LastIndex -> {TRUE, FALSE}]
    /\ read \in [Readers -> Int]
    /\ consumed \in [Readers -> Seq(Nat)]
    /\ pc \in [Writers \cup Readers -> {Access, Advance}]

====
