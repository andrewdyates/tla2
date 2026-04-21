---- MODULE ChooseGuard ----
\* Test CHOOSE in action guard - pattern from Disruptor_MPMC
EXTENDS Integers, FiniteSets

CONSTANTS Writers, Readers, Size, NULL

VARIABLES
    ringbuffer, next_sequence, claimed_sequence, read

vars == <<ringbuffer, next_sequence, claimed_sequence, read>>

LastIndex == Size - 1

Range(f) == {f[x] : x \in DOMAIN f}

MinReadSequence ==
    CHOOSE min \in Range(read) :
        \A r \in Readers : min <= read[r]

Init ==
    /\ ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        writers |-> [i \in 0..LastIndex |-> {}]
       ]
    /\ next_sequence = 0
    /\ claimed_sequence = [w \in Writers |-> -1]
    /\ read = [r \in Readers |-> -1]

ClaimSlot(w) ==
    /\ claimed_sequence[w] = -1
    \* This guard uses MinReadSequence with CHOOSE
    /\ next_sequence - MinReadSequence < Size
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = next_sequence]
    /\ next_sequence' = next_sequence + 1
    /\ ringbuffer' = [ringbuffer EXCEPT
        !.writers[next_sequence % Size] = @ \cup {w},
        !.slots[next_sequence % Size] = next_sequence]
    /\ UNCHANGED read

ReleaseSlot(w) ==
    /\ claimed_sequence[w] >= 0
    /\ ringbuffer' = [ringbuffer EXCEPT
        !.writers[claimed_sequence[w] % Size] = @ \ {w}]
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = -1]
    /\ UNCHANGED <<next_sequence, read>>

Next ==
    \/ \E w \in Writers: ClaimSlot(w)
    \/ \E w \in Writers: ReleaseSlot(w)

\* Direct TypeOk (no INSTANCE)
TypeOk ==
    /\ ringbuffer \in [
        slots:   UNION {[0..LastIndex -> Int \cup {NULL}]},
        writers: UNION {[0..LastIndex -> SUBSET Writers]}
       ]
    /\ next_sequence \in Nat
    /\ claimed_sequence \in [Writers -> Int]
    /\ read \in [Readers -> Int]

====
