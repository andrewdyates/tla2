---- MODULE RecordTypeCheck ----
\* Minimal test for RingBuffer-style TypeOk pattern
EXTENDS Integers

CONSTANTS Size, Writers, NULL

LastIndex == Size - 1

VARIABLE ringbuffer

Init ==
    ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        writers |-> [i \in 0..LastIndex |-> {}]
    ]

\* Simplified RingBuffer TypeOk pattern
\* This is what fails in Disruptor_MPMC
TypeOk ==
    ringbuffer \in [
        slots:   UNION { [0..LastIndex -> Int \cup {NULL}] },
        writers: UNION { [0..LastIndex -> SUBSET Writers] }
    ]

\* Alternative formulation - does this also fail?
TypeOkAlt ==
    /\ ringbuffer.slots \in [0..LastIndex -> Int \cup {NULL}]
    /\ ringbuffer.writers \in [0..LastIndex -> SUBSET Writers]

Write(idx, w, val) ==
    /\ idx \in 0..LastIndex
    /\ w \in Writers
    /\ ringbuffer' = [ringbuffer EXCEPT
        !.writers[idx] = @ \cup {w},
        !.slots[idx] = val]

EndWrite(idx, w) ==
    /\ idx \in 0..LastIndex
    /\ w \in ringbuffer.writers[idx]
    /\ ringbuffer' = [ringbuffer EXCEPT !.writers[idx] = @ \ {w}]

Next ==
    \/ \E idx \in 0..LastIndex, w \in Writers, val \in 0..10: Write(idx, w, val)
    \/ \E idx \in 0..LastIndex, w \in Writers: EndWrite(idx, w)

====
