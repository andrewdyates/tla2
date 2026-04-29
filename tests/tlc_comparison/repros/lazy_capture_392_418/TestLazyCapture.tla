\* Copyright 2026 Dropbox.
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Licensed under the Apache License, Version 2.0

---- MODULE TestLazyCapture ----

VARIABLES x, f, s

Vars == <<x, f, s>>

Init ==
  /\ x = 0
  /\ f = [t \in {1} |-> x]
  /\ s = {t \in {0, 1} : t = x}

Next ==
  /\ x' = IF x = 0 THEN 1 ELSE 0
  /\ f' = f
  /\ s' = s

Inv ==
  /\ f[1] = 0
  /\ s = {0}

Spec == Init /\ [][Next]_Vars

====
