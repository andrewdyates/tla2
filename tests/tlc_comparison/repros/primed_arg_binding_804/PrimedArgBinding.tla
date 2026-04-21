---- MODULE PrimedArgBinding ----
(*
 * Minimal reproduction for issue #804 - primed variable binding through operator arguments
 *
 * This spec mimics the CalculateHashImpl pattern from NanoBlockchain:
 * - An operator takes a primed variable as argument
 * - The operator body constrains that argument via equality
 * - The primed value is then used elsewhere (in EXCEPT key, function arg, etc.)
 *)

EXTENDS Naturals

CONSTANT Hash, NoHashVal

VARIABLE hashFunction, lastHash, data

vars == <<hashFunction, lastHash, data>>

NoHash == NoHashVal

(* Helper: check if any unused hash exists *)
UndefinedHashesExist == \E h \in Hash : hashFunction[h] = 0

(* Helper: select first unused hash - only call when UndefinedHashesExist is true *)
UnusedHash == CHOOSE h \in Hash : hashFunction[h] = 0

(* This mimics CalculateHashImpl - binds newHash (which is lastHash') via argument *)
AssignHash(value, oldHash, newHash) ==
    LET h == UnusedHash IN
    /\ newHash = h                      \* Constrains lastHash' to h
    /\ hashFunction' = [hashFunction EXCEPT ![h] = value]

(* Action that creates data and uses the assigned hash *)
CreateData(v) ==
    /\ AssignHash(v, lastHash, lastHash')
    /\ data' = [data EXCEPT ![lastHash'] = v]  \* Uses lastHash' as key

Init ==
    /\ hashFunction = [h \in Hash |-> 0]
    /\ lastHash = NoHash
    /\ data = [h \in Hash |-> 0]

Next ==
    IF UndefinedHashesExist
    THEN \E v \in {1, 2} : CreateData(v)
    ELSE UNCHANGED vars  \* Stutter when no more hashes

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ hashFunction \in [Hash -> 0..2]
    /\ data \in [Hash -> 0..2]

====
