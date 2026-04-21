---- MODULE TraceInvMonotonic ----
\* Trace invariant (Apalache Gap 4): checks property over execution history.
\* Expected: trace invariant passes (x is monotonically increasing).
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
MonotonicTrace(hist) ==
    \A i \in 1..(Len(hist) - 1) :
        hist[i + 1].x >= hist[i].x
====
