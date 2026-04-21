---- MODULE MCHashModule ----
(*
 * INSTANCE-based repro for #804
 * This mimics MCNano's structure with INSTANCE and module-scoped overrides
 *)

EXTENDS Naturals

CONSTANTS Hash, NoBlockVal

VARIABLES hashFunction, lastHash, data

vars == <<hashFunction, lastHash, data>>

(* Override NoBlock to be the model value *)
NoBlock == NoBlockVal

H == INSTANCE HashModule

Init ==
    /\ H!Init
    /\ data = [h \in Hash |-> NoBlockVal]

(* Key pattern: use lastHash' (constrained by H!CalculateHash) in EXCEPT *)
CreateData(v) ==
    /\ H!CalculateHash(v, lastHash, lastHash')
    /\ data' = [data EXCEPT ![lastHash'] = v]

Next ==
    IF H!UndefinedHashesExist
    THEN \E v \in {1, 2} : CreateData(v)
    ELSE UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ H!TypeInvariant
    /\ data \in [Hash -> {NoBlockVal} \union {1, 2}]

====
