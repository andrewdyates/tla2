---- MODULE ConsumedWithActions ----
\* Pattern from Disruptor_MPMC with actions
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Readers, Writers, Size, NULL

VARIABLES consumed, pc, ringbuffer

LastIndex == Size - 1

Init ==
    /\ consumed = [r \in Readers |-> <<>>]
    /\ pc = [a \in Readers \cup Writers |-> "Advance"]
    /\ ringbuffer = [
        slots   |-> [i \in 0..LastIndex |-> NULL],
        readers |-> [i \in 0..LastIndex |-> {}],
        writers |-> [i \in 0..LastIndex |-> {}]
       ]

\* Simplified write action
BeginWrite(w) ==
    /\ pc[w] = "Advance"
    /\ ringbuffer' = [ringbuffer EXCEPT
        !.slots[0] = 0,
        !.writers[0] = @ \cup {w}]
    /\ pc' = [pc EXCEPT ![w] = "Access"]
    /\ UNCHANGED consumed

\* Simplified read action
BeginRead(r) ==
    /\ pc[r] = "Advance"
    /\ ringbuffer' = [ringbuffer EXCEPT !.readers[0] = @ \cup {r}]
    \* This appends ringbuffer.slots[0] to consumed[r]
    /\ consumed' = [consumed EXCEPT ![r] = Append(@, ringbuffer.slots[0])]
    /\ pc' = [pc EXCEPT ![r] = "Access"]

Next ==
    \/ \E w \in Writers: BeginWrite(w)
    \/ \E r \in Readers: BeginRead(r)

InvConsumed == consumed \in [Readers -> Seq(Nat)]

vars == <<consumed, pc, ringbuffer>>

====
