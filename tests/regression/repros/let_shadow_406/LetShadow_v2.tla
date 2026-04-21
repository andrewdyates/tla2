\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Regression test for #406: Sequential LET shadowing in state_var pass
\*
\* This spec tests that later LET definitions can reference earlier LET
\* definitions. This is a valid test case (no name collision with state vars).
\*
\* Expected behavior:
\* - In LET a == 1, b == a + 1 IN b = 2, the `b == a + 1` references LET-defined `a`
\* - So Inv should be TRUE (b equals 2)
---- MODULE LetShadow_v2 ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == x' = x

Spec == Init /\ [][Next]_x

\* This invariant tests sequential LET scoping without shadowing state vars:
\* - LET a == 1 defines a local constant
\* - LET b == a + 1 should reference the LET-defined a (value 1)
\* - Result: b = 2
Inv ==
  LET a == 1
      b == a + 1
  IN b = 2

====
