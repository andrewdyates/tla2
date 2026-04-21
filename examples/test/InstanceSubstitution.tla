---- MODULE InstanceSubstitution ----
\* Minimal test for INSTANCE parameter substitution bug
EXTENDS Integers

CONSTANTS Writers, NULL

VARIABLE ringbuffer

\* This line is the key - substituting Values <- Int
Buffer == INSTANCE InstanceSubstitutionInner WITH Values <- Int, Size <- 2

Init == Buffer!Init

Write(idx, w, val) ==
    /\ idx \in 0..Buffer!LastIndex
    /\ w \in Writers
    /\ ringbuffer' = [ringbuffer EXCEPT
        !.writers[idx] = @ \cup {w},
        !.slots[idx] = val]

Next == \E idx \in 0..Buffer!LastIndex, w \in Writers, val \in 0..3: Write(idx, w, val)

\* This calls Buffer!TypeOk which uses the substituted Values
TypeOk == Buffer!TypeOk

====
