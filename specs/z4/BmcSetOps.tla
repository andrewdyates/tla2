---- MODULE BmcSetOps ----
\* BMC test spec: Set union membership tracking.
\*
\* S starts as {1, 2}, accumulates via union with {3} each step.
\* Safety: x must remain in S (S grows, x stays 1 => always safe).
\*
\* Expected BMC result: BoundReached (safety always holds).

VARIABLE S, x

Init == S = {1, 2} /\ x = 1

Next == S' = S \union {3} /\ UNCHANGED x

Safety == x \in S

====
