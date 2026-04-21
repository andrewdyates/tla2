---- MODULE InstanceTypeCheck ----
\* Test INSTANCE with type check (like Disruptor_MPMC)
EXTENDS Integers

CONSTANTS Size, Writers, Readers, NULL

VARIABLE ringbuffer

\* This matches RingBuffer.tla exactly
Buffer == INSTANCE InstanceTypeCheckBuffer WITH Values <- Int

Init == Buffer!Init

Write(idx, w, val) == Buffer!Write(idx, w, val)
EndWrite(idx, w) == Buffer!EndWrite(idx, w)

Next ==
    \/ \E idx \in 0..Buffer!LastIndex, w \in Writers, val \in 0..5: Write(idx, w, val)
    \/ \E idx \in 0..Buffer!LastIndex, w \in Writers: EndWrite(idx, w)

\* Check invariant through INSTANCE
TypeOk == Buffer!TypeOk

====
