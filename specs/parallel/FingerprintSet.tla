-------------------------------- MODULE FingerprintSet --------------------------------
(***************************************************************************)
(* TLA+ Specification: Concurrent Fingerprint Set                          *)
(*                                                                          *)
(* Models the FingerprintSet used in TLA2's parallel model checker for     *)
(* deduplication. Multiple workers concurrently insert and query           *)
(* fingerprints to avoid exploring duplicate states.                       *)
(*                                                                          *)
(* Key Operations:                                                          *)
(*   - Insert(worker, fp): Try to insert fingerprint, return if new        *)
(*   - Contains(worker, fp): Check if fingerprint exists                   *)
(*                                                                          *)
(* Properties:                                                              *)
(*   - NoLostInserts: All inserted fingerprints remain queryable           *)
(*   - NoDuplicateExploration: Each fingerprint explored exactly once      *)
(*                                                                          *)
(* Author: Andrew Yates                                                     *)
(* Copyright 2026 Dropbox. | License: Apache 2.0                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Workers,      \* Set of worker IDs (e.g., {1, 2, 3, 4})
    Fingerprints  \* Set of possible fingerprints (e.g., {1, 2, 3})

VARIABLES
    set,          \* The fingerprint set (set of fingerprints)
    inserted,     \* Per-worker: fingerprints this worker has successfully inserted
    explored,     \* Per-worker: fingerprints this worker has explored
    pc            \* Per-worker: program counter (phase of operation)

vars == <<set, inserted, explored, pc>>

TypeOK ==
    /\ set \subseteq Fingerprints
    /\ inserted \in [Workers -> SUBSET Fingerprints]
    /\ explored \in [Workers -> SUBSET Fingerprints]
    /\ pc \in [Workers -> {"idle", "checking", "inserting", "exploring"}]

Init ==
    /\ set = {}
    /\ inserted = [w \in Workers |-> {}]
    /\ explored = [w \in Workers |-> {}]
    /\ pc = [w \in Workers |-> "idle"]

-----------------------------------------------------------------------------
(* Worker Operations *)

(* Worker w starts checking if fingerprint fp is in the set *)
StartCheck(w, fp) ==
    /\ pc[w] = "idle"
    /\ fp \notin explored[w]  \* Only check fingerprints we haven't explored
    /\ pc' = [pc EXCEPT ![w] = "checking"]
    /\ UNCHANGED <<set, inserted, explored>>

(* Worker w tries to insert fp using CAS semantics.
   In practice this is atomic - the spec models the linearization point. *)
TryInsert(w, fp) ==
    /\ pc[w] = "checking"
    /\ IF fp \in set THEN
         (* Already in set - another worker inserted it *)
         /\ pc' = [pc EXCEPT ![w] = "idle"]
         /\ UNCHANGED <<set, inserted, explored>>
       ELSE
         (* Not in set - we insert it (CAS success) and will explore *)
         /\ set' = set \union {fp}
         /\ inserted' = [inserted EXCEPT ![w] = @ \union {fp}]
         /\ pc' = [pc EXCEPT ![w] = "exploring"]
         /\ UNCHANGED explored

(* Worker w explores the state after successfully inserting fp *)
FinishExplore(w, fp) ==
    /\ pc[w] = "exploring"
    /\ fp \in inserted[w]
    /\ explored' = [explored EXCEPT ![w] = @ \union {fp}]
    /\ pc' = [pc EXCEPT ![w] = "idle"]
    /\ UNCHANGED <<set, inserted>>

(* Worker w gives up without exploring (fp was already in set) *)
SkipExplore(w) ==
    /\ pc[w] = "idle"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \E w \in Workers, fp \in Fingerprints :
        \/ StartCheck(w, fp)
        \/ TryInsert(w, fp)
        \/ FinishExplore(w, fp)
        \/ SkipExplore(w)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

(* All inserted fingerprints remain in the set *)
NoLostInserts ==
    \A w \in Workers : inserted[w] \subseteq set

(* Each fingerprint is explored by at most one worker *)
NoDuplicateExploration ==
    \A w1, w2 \in Workers :
        w1 # w2 => explored[w1] \cap explored[w2] = {}

(* Every fingerprint in set was inserted by exactly one worker *)
UniqueInsertion ==
    \A fp \in set :
        Cardinality({w \in Workers : fp \in inserted[w]}) = 1

(* A fingerprint can only be explored if it was inserted *)
ExploredImpliesInserted ==
    \A w \in Workers : explored[w] \subseteq inserted[w]

(* All safety properties combined *)
Safety ==
    /\ TypeOK
    /\ NoLostInserts
    /\ NoDuplicateExploration
    /\ UniqueInsertion
    /\ ExploredImpliesInserted

-----------------------------------------------------------------------------
(* Liveness Properties (with fairness) *)

(* Eventually all fingerprints are explored *)
EventuallyAllExplored ==
    <>(UNION {explored[w] : w \in Workers} = Fingerprints)

(* Weak fairness for progress *)
Fairness ==
    \A w \in Workers :
        WF_vars(\E fp \in Fingerprints :
            \/ TryInsert(w, fp)
            \/ FinishExplore(w, fp))

LiveSpec == Spec /\ Fairness

=============================================================================
