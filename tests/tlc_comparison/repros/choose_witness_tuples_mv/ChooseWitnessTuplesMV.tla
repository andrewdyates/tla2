\* Copyright 2026 Dropbox.
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Licensed under the Apache License, Version 2.0

---- MODULE ChooseWitnessTuplesMV ----
EXTENDS FiniteSets, TLC

\* Repro for #1004 (Init enumeration swallowing evaluation errors as "no solutions"):
\*
\* Java TLC computes 1 initial state and prints the CHOOSE witnesses.
\* TLA2 currently computes 0 initial states.
\*
\* This spec exercises bounded CHOOSE over SUBSET where the base set contains
\* tuples with model values.

CONSTANTS A, B, C
VARIABLES mv_tuple, subset2_pairs, subset2_tuples

Init ==
  LET pairs ==
        {<<A, B>>, <<A, C>>, <<B, C>>}
      tuples ==
        {<<A, 1>>, <<A, 2>>, <<B, 1>>, <<B, 2>>, <<C, 1>>, <<C, 2>>}
      mv_tuple_ == CHOOSE t \in tuples : TRUE
      subset2_pairs_ == CHOOSE s \in SUBSET pairs : Cardinality(s) = 2
      subset2_tuples_ == CHOOSE s \in SUBSET tuples : Cardinality(s) = 2
  IN
    /\ mv_tuple = mv_tuple_
    /\ subset2_pairs = subset2_pairs_
    /\ subset2_tuples = subset2_tuples_
    /\ PrintT(<<"MV_TUPLE_CHOOSE", mv_tuple_>>)
    /\ PrintT(<<"MV_SUBSET2_PAIRS_CHOOSE", subset2_pairs_>>)
    /\ PrintT(<<"MV_SUBSET2_TUPLES_CHOOSE", subset2_tuples_>>)

Next == UNCHANGED <<mv_tuple, subset2_pairs, subset2_tuples>>

vars == <<mv_tuple, subset2_pairs, subset2_tuples>>
Spec == Init /\ [][Next]_vars

====

