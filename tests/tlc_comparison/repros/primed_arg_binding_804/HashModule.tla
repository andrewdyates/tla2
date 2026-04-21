---- MODULE HashModule ----
(*
 * Sub-module for INSTANCE repro - mimics Nano's structure
 * NoBlock is a DEFINED operator (like in Nano.tla), not a CONSTANT
 *)

EXTENDS Naturals

CONSTANT Hash

VARIABLE hashFunction, lastHash

(* Defined operator - will be overridden via module-scoped config *)
NoBlock == CHOOSE b : b \notin {1, 2}

(* This is the key pattern: CalculateHash takes primed var as argument *)
CalculateHash(block, oldHash, newHash) ==
    LET h == CHOOSE h \in Hash : hashFunction[h] = NoBlock IN
    /\ newHash = h
    /\ hashFunction' = [hashFunction EXCEPT ![h] = block]

(* Check if unused hashes exist *)
UndefinedHashesExist == \E h \in Hash : hashFunction[h] = NoBlock

Init ==
    /\ hashFunction = [h \in Hash |-> NoBlock]
    /\ lastHash = NoBlock

(* Simple Next that creates a block *)
Next ==
    \E v \in {1, 2} :
        /\ CalculateHash(v, lastHash, lastHash')

TypeInvariant ==
    /\ hashFunction \in [Hash -> {NoBlock} \union {1, 2}]

====
