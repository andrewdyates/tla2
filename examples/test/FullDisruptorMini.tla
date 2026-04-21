---- MODULE FullDisruptorMini ----
\* Minimal Disruptor with all variables including pc
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

LastIndex == Size - 1

\* INSTANCE RingBuffer WITH Values <- Int
\* Inline the Buffer module for now

Range(f) == {f[x] : x \in DOMAIN f}

MinReadSequence ==
    CHOOSE min \in Range(read) :
        \A r \in Readers : min <= read[r]

Init ==
    /\ ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        readers |-> [i \in 0..LastIndex |-> {}],
        writers |-> [i \in 0..LastIndex |-> {}]
       ]
    /\ next_sequence = 0
    /\ claimed_sequence = [w \in Writers |-> -1]
    /\ published = [i \in 0..LastIndex |-> FALSE]
    /\ read = [r \in Readers |-> -1]
    /\ pc = [t \in Writers \cup Readers |-> Advance]
    /\ consumed = [r \in Readers |-> <<>>]

ClaimSlot(w) ==
    /\ pc[w] = Advance
    /\ claimed_sequence[w] = -1
    /\ next_sequence - MinReadSequence < Size
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = next_sequence]
    /\ next_sequence' = next_sequence + 1
    /\ ringbuffer' = [ringbuffer EXCEPT
        !.writers[next_sequence % Size] = @ \cup {w},
        !.slots[next_sequence % Size] = next_sequence]
    /\ pc' = [pc EXCEPT ![w] = Access]
    /\ UNCHANGED <<published, read, consumed>>

ReleaseSlot(w) ==
    /\ pc[w] = Access
    /\ claimed_sequence[w] >= 0
    /\ ringbuffer' = [ringbuffer EXCEPT
        !.writers[claimed_sequence[w] % Size] = @ \ {w}]
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = -1]
    /\ pc' = [pc EXCEPT ![w] = Advance]
    /\ UNCHANGED <<next_sequence, published, read, consumed>>

Next ==
    \/ \E w \in Writers: ClaimSlot(w)
    \/ \E w \in Writers: ReleaseSlot(w)

\* Full TypeOk from Disruptor_MPMC (with inlined Buffer!TypeOk)
BufferTypeOk ==
    ringbuffer \in [
        slots:   UNION {[0..LastIndex -> Int \cup {NULL}]},
        readers: UNION {[0..LastIndex -> SUBSET Readers]},
        writers: UNION {[0..LastIndex -> SUBSET Writers]}
    ]

TypeOk ==
    /\ BufferTypeOk
    /\ next_sequence \in Nat
    /\ claimed_sequence \in [Writers -> Int]
    /\ published \in [0..LastIndex -> {TRUE, FALSE}]
    /\ read \in [Readers -> Int]
    /\ consumed \in [Readers -> Seq(Nat)]
    /\ pc \in [Writers \cup Readers -> {Access, Advance}]

====
