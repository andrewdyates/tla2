---------------------------- MODULE TestConfigParse ----------------------------
(* Test that config file = {v1, v2} syntax is parsed correctly for
   both flat sets and nested sets (Quorum). *)
EXTENDS Integers, FiniteSets

CONSTANTS Value, Actor, Quorum

VARIABLE dummy

Init == dummy = 0

Next == dummy' = dummy

\* If Value has 2 elements, check passes
ValueSize == Cardinality(Value) = 2
ActorSize == Cardinality(Actor) = 3
QuorumSize == Cardinality(Quorum) = 4

\* Check quorum structure: each quorum is a subset of Actor
QuorumStructure == \A Q \in Quorum : Q \subseteq Actor

Spec == Init /\ [][Next]_dummy
=============================================================================
