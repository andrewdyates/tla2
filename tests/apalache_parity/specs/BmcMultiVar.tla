---- MODULE BmcMultiVar ----
\* BMC with multiple state variables and boolean+integer types.
\* Expected: safety holds within depth 5.
VARIABLES x, flag
Init == x = 0 /\ flag = FALSE
Next == /\ x' = IF x < 5 THEN x + 1 ELSE x
        /\ flag' = (x' >= 3)
Safety == (flag = TRUE) => (x >= 3)
====
