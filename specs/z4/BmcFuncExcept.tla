---- MODULE BmcFuncExcept ----
\* BMC test spec: Function EXCEPT updates a counter.
\*
\* f maps {1, 2} to integers. Each step increments f[1] via EXCEPT.
\* Safety: f[1] <= 5 — violated at depth 6.
\*
\* Expected BMC result: Violation at depth 6.

VARIABLE f

Init == f = [k \in {1, 2} |-> 0]

Next == f' = [f EXCEPT ![1] = f[1] + 1]

Safety == f[1] <= 5

====
