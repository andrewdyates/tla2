---------------------------- MODULE TestDefOverride ----------------------------
(* Test whether config file can override a defined operator (not a CONSTANT).
   Ballot is defined as Nat but should be overridden by config. *)
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* This is a DEFINITION, not a CONSTANT
Ballot == Nat

VARIABLE counter

Init == counter = 0

Next == \E b \in Ballot : counter' = b

\* If Ballot is correctly overridden to {0, 1, 2}, we get 3 states
\* If Ballot is still Nat, this will loop forever or fail
BallotFinite == IsFiniteSet(Ballot)
BallotSize == Cardinality(Ballot) = 3

Spec == Init /\ [][Next]_counter
=============================================================================
