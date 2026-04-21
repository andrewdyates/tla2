---- MODULE BmcUnsafeCounter ----
\* BMC mode: safety property violated at depth 4.
\* Expected: BMC reports VIOLATION at depth 4.
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 2
====
