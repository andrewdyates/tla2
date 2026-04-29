\* Copyright 2026 Dropbox.
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Licensed under the Apache License, Version 2.0

---- MODULE ChooseWitness993 ----
EXTENDS FiniteSets, TLC

\* CHOOSE witness should match Java TLC exactly, including model values.
\*
\* This repro focuses on:
\*  - CHOOSE over a set containing multiple model values
\*  - CHOOSE over SUBSET {model values} with a cardinality predicate
\*
\* Witness parity is checked by comparing TLC PrintT output with TLA2 output.

CONSTANTS A, B, C
VARIABLES mv, subset2

Init ==
  LET mv_ == CHOOSE x \in {A, B, C} : TRUE
      subset2_ == CHOOSE s \in SUBSET {A, B, C} : Cardinality(s) = 2
  IN
    /\ mv = mv_
    /\ subset2 = subset2_
    /\ PrintT(<<"MV_CHOOSE", mv_>>)
    /\ PrintT(<<"MV_SUBSET2_CHOOSE", subset2_>>)

Next == UNCHANGED <<mv, subset2>>

vars == <<mv, subset2>>
Spec == Init /\ [][Next]_vars

====

