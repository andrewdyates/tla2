------------------------------ MODULE TerminationDetection ------------------------------
(***************************************************************************)
(* TLA+ Specification: Work-Stealing Termination Detection                 *)
(*                                                                          *)
(* Models the termination detection protocol in TLA2's parallel checker.   *)
(* This spec demonstrates the race condition identified in #293.           *)
(*                                                                          *)
(* The bug: There's a window between a worker popping work and marking     *)
(* itself as active. Another worker can see active_workers=0 and terminate *)
(* prematurely.                                                             *)
(*                                                                          *)
(* Author: Andrew Yates                                                     *)
(* Copyright 2026 Andrew Yates. | License: Apache 2.0                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Workers,      \* Set of worker IDs (e.g., {1, 2, 3})
    InitialWork   \* Initial work items (e.g., {1, 2, 3})

VARIABLES
    queues,         \* Per-worker local queues [Workers -> Seq(Work)]
    active_workers, \* Count of workers currently processing
    work_remaining, \* Count of work items in all queues
    pc,             \* Per-worker program counter
    current_work,   \* Per-worker current work item (or None)
    terminated,     \* Set of workers that have terminated
    processed       \* Set of work items that have been processed

vars == <<queues, active_workers, work_remaining, pc, current_work, terminated, processed>>

None == 0  \* Sentinel value not in InitialWork

TypeOK ==
    /\ queues \in [Workers -> Seq(InitialWork)]
    /\ active_workers \in 0..Cardinality(Workers)
    /\ work_remaining \in 0..(Cardinality(InitialWork) * 10)  \* Work can grow
    /\ pc \in [Workers -> {"idle", "popping", "active", "processing", "done"}]
    /\ current_work \in [Workers -> InitialWork \union {None}]
    /\ terminated \subseteq Workers
    /\ processed \subseteq InitialWork

-----------------------------------------------------------------------------
(* Helper: Range of sequence *)
Range(s) == {s[i] : i \in 1..Len(s)}

(* Helper: Total queue size *)
TotalQueueSize == work_remaining

-----------------------------------------------------------------------------
(* Initial State: All work in first worker's queue *)

Init ==
    /\ queues = [w \in Workers |-> IF w = 1 THEN <<1, 2, 3>> ELSE <<>>]
    /\ active_workers = 0
    /\ work_remaining = Cardinality(InitialWork)
    /\ pc = [w \in Workers |-> "idle"]
    /\ current_work = [w \in Workers |-> None]
    /\ terminated = {}
    /\ processed = {}

-----------------------------------------------------------------------------
(* Worker Actions - Models the BUGGY protocol *)

(* Worker starts looking for work *)
StartLooking(w) ==
    /\ pc[w] = "idle"
    /\ w \notin terminated
    /\ pc' = [pc EXCEPT ![w] = "popping"]
    /\ UNCHANGED <<queues, active_workers, work_remaining, current_work, terminated, processed>>

(* Worker successfully pops work from own queue - BUG: active not incremented yet *)
PopLocal(w) ==
    /\ pc[w] = "popping"
    /\ Len(queues[w]) > 0
    /\ current_work' = [current_work EXCEPT ![w] = Head(queues[w])]
    /\ queues' = [queues EXCEPT ![w] = Tail(@)]
    \* NOTE: active_workers NOT incremented here - this is the bug!
    /\ pc' = [pc EXCEPT ![w] = "active"]
    /\ UNCHANGED <<active_workers, work_remaining, terminated, processed>>

(* Worker successfully steals from another worker *)
Steal(w, v) ==
    /\ pc[w] = "popping"
    /\ w # v
    /\ Len(queues[w]) = 0
    /\ Len(queues[v]) > 0
    /\ current_work' = [current_work EXCEPT ![w] = Head(queues[v])]
    /\ queues' = [queues EXCEPT ![v] = Tail(@)]
    /\ pc' = [pc EXCEPT ![w] = "active"]
    \* NOTE: active_workers NOT incremented here - this is the bug!
    /\ UNCHANGED <<active_workers, work_remaining, terminated, processed>>

(* Worker marks itself as active (separate step - the race window) *)
MarkActive(w) ==
    /\ pc[w] = "active"
    /\ current_work[w] # None
    /\ active_workers' = active_workers + 1
    /\ pc' = [pc EXCEPT ![w] = "processing"]
    /\ UNCHANGED <<queues, work_remaining, current_work, terminated, processed>>

(* Worker finishes processing (marks done and generates successor) *)
FinishProcessing(w) ==
    /\ pc[w] = "processing"
    /\ current_work[w] # None
    \* Decrement work_remaining and possibly push new work
    /\ work_remaining' = work_remaining - 1
    /\ active_workers' = active_workers - 1
    /\ processed' = processed \union {current_work[w]}
    /\ current_work' = [current_work EXCEPT ![w] = None]
    /\ pc' = [pc EXCEPT ![w] = "idle"]
    /\ UNCHANGED <<queues, terminated>>

(* Worker finds no work and checks termination - CAN TERMINATE INCORRECTLY *)
CheckTermination(w) ==
    /\ pc[w] = "popping"
    /\ Len(queues[w]) = 0
    /\ \A v \in Workers : Len(queues[v]) = 0  \* No visible work
    /\ work_remaining = 0
    /\ active_workers = 0  \* BUG: Another worker may have work but hasn't marked active!
    /\ pc' = [pc EXCEPT ![w] = "done"]
    /\ terminated' = terminated \union {w}
    /\ UNCHANGED <<queues, active_workers, work_remaining, current_work, processed>>

(* Worker goes back to idle if no work but not ready to terminate *)
BackToIdle(w) ==
    /\ pc[w] = "popping"
    /\ Len(queues[w]) = 0
    /\ \A v \in Workers : Len(queues[v]) = 0
    /\ (work_remaining > 0 \/ active_workers > 0)  \* Not ready to terminate
    /\ pc' = [pc EXCEPT ![w] = "idle"]
    /\ UNCHANGED <<queues, active_workers, work_remaining, current_work, terminated, processed>>

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \E w \in Workers :
        \/ StartLooking(w)
        \/ PopLocal(w)
        \/ \E v \in Workers : Steal(w, v)
        \/ MarkActive(w)
        \/ FinishProcessing(w)
        \/ CheckTermination(w)
        \/ BackToIdle(w)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

(* THE BUG: This should hold but doesn't in buggy protocol! *)
(* If a worker terminates, all work should be processed *)
AllWorkProcessedOnTermination ==
    (terminated # {}) => (
        \/ processed = InitialWork
        \/ \E w \in Workers : current_work[w] # None  \* Someone has unprocessed work
    )

(* No premature termination: if work exists, not all workers should terminate *)
NoPrematureTermination ==
    LET workExists == \/ work_remaining > 0
                      \/ \E w \in Workers : current_work[w] # None
                      \/ \E w \in Workers : Len(queues[w]) > 0
    IN workExists => terminated # Workers

(* Stronger: If any worker terminates, either all work is done or someone is active *)
SafeTermination ==
    (terminated # {}) =>
        (\/ processed = InitialWork
         \/ active_workers > 0
         \/ \E w \in Workers : pc[w] \in {"active", "processing"})

(* THE BUG: Can a worker terminate while another has work but hasn't marked active? *)
(* This captures the race: pc="active" means "has work" but active_workers not incremented *)
NoPrematureTerminationWithHeldWork ==
    \A w \in terminated : \A v \in Workers :
        (v \notin terminated /\ pc[v] = "active") => FALSE

=============================================================================
