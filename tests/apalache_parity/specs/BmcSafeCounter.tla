---- MODULE BmcSafeCounter ----
\* BMC mode: safety property holds within bounded depth.
\* Expected: BMC reports no bug found up to depth 5.
VARIABLE x
Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE x
Safety == x >= 0 /\ x <= 3
====
