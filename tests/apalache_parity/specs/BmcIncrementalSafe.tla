---- MODULE BmcIncrementalSafe ----
\* BMC incremental solving: reuses solver state across depths.
\* Expected: no bug found up to depth 10, incremental mode.
VARIABLE y
Init == y \in {0, 1}
Next == y' = 1 - y
Safety == y \in {0, 1}
====
