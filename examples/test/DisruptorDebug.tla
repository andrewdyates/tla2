---- MODULE DisruptorDebug ----
\* Debug version of Disruptor_MPMC to isolate false positive
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

\* Inline RingBuffer (no INSTANCE to eliminate that variable)
LastIndex == Size - 1

RBInit ==
  ringbuffer = [
    slots   |-> [i \in 0..LastIndex |-> NULL],
    readers |-> [i \in 0..LastIndex |-> {}],
    writers |-> [i \in 0..LastIndex |-> {}]
  ]

RBTypeOk ==
  ringbuffer \in [
    slots:   UNION { [0..LastIndex -> Int \cup {NULL}] },
    readers: UNION { [0..LastIndex -> SUBSET(Readers)] },
    writers: UNION { [0..LastIndex -> SUBSET(Writers)] }
  ]

IndexOf(sequence) == sequence % Size

Write(index, writer, value) ==
  ringbuffer' = [
    ringbuffer EXCEPT
      !.writers[index] = @ \union {writer},
      !.slots[index] = value
  ]

EndWrite(index, writer) ==
  ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \ {writer}]

Range(f) == {f[x] : x \in DOMAIN(f)}

MinReadSequence ==
  CHOOSE min \in Range(read) :
    \A r \in Readers : min <= read[r]

MinClaimedSequence ==
  CHOOSE min \in Range(claimed_sequence) :
    \A w \in Writers : min <= claimed_sequence[w]

Init ==
  /\ RBInit
  /\ next_sequence = 0
  /\ claimed_sequence = [w \in Writers |-> -1]
  /\ published = [i \in 0..LastIndex |-> FALSE]
  /\ read = [r \in Readers |-> -1]
  /\ pc = [t \in Writers \cup Readers |-> Advance]
  /\ consumed = [r \in Readers |-> <<>>]

\* Simplified Next - just writer claiming
ClaimSlot(w) ==
  /\ pc[w] = Advance
  /\ claimed_sequence[w] = -1
  /\ next_sequence - MinReadSequence < Size
  /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = next_sequence]
  /\ next_sequence' = next_sequence + 1
  /\ Write(IndexOf(next_sequence), w, next_sequence)
  /\ pc' = [pc EXCEPT ![w] = Access]
  /\ UNCHANGED <<published, read, consumed>>

ReleaseSlot(w) ==
  /\ pc[w] = Access
  /\ claimed_sequence[w] >= 0
  /\ EndWrite(IndexOf(claimed_sequence[w]), w)
  /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = -1]
  /\ pc' = [pc EXCEPT ![w] = Advance]
  /\ UNCHANGED <<next_sequence, published, read, consumed>>

Next ==
  \/ \E w \in Writers : ClaimSlot(w)
  \/ \E w \in Writers : ReleaseSlot(w)

\* Split TypeOk into components for debugging
TypeOk_Buffer == RBTypeOk
TypeOk_NextSeq == next_sequence \in Nat
TypeOk_Claimed == claimed_sequence \in [Writers -> Int]
TypeOk_Published == published \in [0..LastIndex -> {TRUE, FALSE}]
TypeOk_Read == read \in [Readers -> Int]
TypeOk_Consumed == consumed \in [Readers -> Seq(Nat)]

TypeOk ==
  /\ TypeOk_Buffer
  /\ TypeOk_NextSeq
  /\ TypeOk_Claimed
  /\ TypeOk_Published
  /\ TypeOk_Read
  /\ TypeOk_Consumed

====
