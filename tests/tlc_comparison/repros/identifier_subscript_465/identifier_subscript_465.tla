---- MODULE IdentifierSubscript_465 ----
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Regression repro for #465: identifier-style subscripts (`_vars`)
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
====
