---- MODULE TraceInvViolation ----
\* Trace invariant violation: x increases but trace inv requires decrease.
\* Expected: trace invariant violation detected.
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
DecreasingTrace(hist) ==
    \A i \in 1..(Len(hist) - 1) :
        hist[i + 1].x < hist[i].x
====
