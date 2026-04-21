---- MODULE BmcSetSubset ----
\* BMC test spec: Subset relationship maintained across steps.
\*
\* A starts as {1}, B starts as {1, 2, 3}.
\* Each step adds an element to A. Safety: A \subseteq B.
\* When A gets {4}, the subset relationship breaks.
\*
\* Expected BMC result: Violation when A accumulates an element not in B.

VARIABLES A, B

Init == A = {1} /\ B = {1, 2, 3}

Next == A' = A \union {2} /\ UNCHANGED B

Safety == A \subseteq B

====
