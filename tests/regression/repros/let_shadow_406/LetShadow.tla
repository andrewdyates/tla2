\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Regression test for #406: Sequential LET shadowing in state_var pass
\*
\* This spec tests that later LET definitions can reference earlier LET
\* definitions when both collide with a state variable name.
\*
\* Expected behavior (matching TLC/SANY):
\* - In LET x == 1, y == x IN y = 1, the `y == x` references the LET-defined `x`
\* - NOT the state variable x
\* - So Inv should be TRUE (y equals 1, not 0)
---- MODULE LetShadow ----
VARIABLE x

Init == x = 0
Next == x' = x

Spec == Init /\ [][Next]_x

\* This invariant tests sequential LET scoping:
\* - LET x == 1 shadows the state variable x
\* - LET y == x should reference the LET-defined x (value 1), not state var x (value 0)
Inv ==
  LET x == 1
      y == x
  IN y = 1

====
