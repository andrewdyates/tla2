---- MODULE InstanceSubstitutionInner ----
\* Inner module - Values is a CONSTANT that will be substituted
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANTS Size, Writers, Values, NULL

ASSUME NULL \notin Values

VARIABLE ringbuffer

LastIndex == Size - 1

Init ==
    ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        writers |-> [i \in 0..LastIndex |-> {}]
    ]

\* This uses the exact same UNION pattern from RingBuffer.tla
TypeOk ==
    ringbuffer \in [
        slots:   UNION { [0..LastIndex -> Values \union {NULL}] },
        writers: UNION { [0..LastIndex -> SUBSET Writers] }
    ]

====
