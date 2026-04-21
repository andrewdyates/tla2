\* Copyright 2026 Andrew Yates.
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Licensed under the Apache License, Version 2.0

---- MODULE SetPredCapture ----
EXTENDS TLC

\*
\* Reproducer for #418: SetPredValue must capture `state_env` at definition time.
\*
\* This spec stores a set filter over STRING in a state variable. The filter depends on `x`
\* at the time it is created (when x=0), and `s` is then held constant while `x` changes.
\*
\* Correct semantics: `s` stays {"a"} (since x=0 at definition time).
\* If the set predicate is evaluated under the *caller* state instead, "a" membership fails
\* once x becomes 1.
\*

VARIABLES x, s

Vars == <<x, s>>

Init ==
  /\ x = 0
  /\ s = {}

Next ==
  \/ /\ x = 0
     /\ x' = 1
     /\ s' = {t \in STRING : IF x = 0 THEN t = "a" ELSE t = "b"}
  \/ /\ x = 1
     /\ x' = 2
     /\ s' = s
  \/ /\ x = 2
     /\ x' = 2
     /\ s' = s

Inv == (x = 0) \/ ("a" \in s)

Spec == Init /\ [][Next]_Vars

====

