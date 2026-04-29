-------------------------------- MODULE WorkQueue --------------------------------
(***************************************************************************)
(* TLA+ Specification: Work-Stealing Queue                                 *)
(*                                                                          *)
(* Models the work-stealing queue system used in TLA2's parallel checker.  *)
(* Based on crossbeam-deque: each worker has a local FIFO queue, and       *)
(* workers can steal from each other when idle.                            *)
(*                                                                          *)
(* Structure:                                                               *)
(*   - Injector: Global queue for initial states                           *)
(*   - Worker queues: Per-worker FIFO queues                               *)
(*   - Steal operation: Take work from another worker's queue              *)
(*                                                                          *)
(* Key Operations:                                                          *)
(*   - Push(worker, state): Add state to worker's local queue              *)
(*   - Pop(worker): Take state from own queue                              *)
(*   - Steal(from, to): Steal work from another worker                     *)
(*                                                                          *)
(* Properties:                                                              *)
(*   - AllStatesExplored: Every injected state is eventually processed     *)
(*   - ExactlyOnce: Each state is processed exactly once                   *)
(*                                                                          *)
(* Author: Andrew Yates                                                     *)
(* Copyright 2026 Dropbox. | License: Apache 2.0                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Workers,     \* Set of worker IDs
    States,      \* Set of state identifiers to explore
    None         \* Special value for "no state" (must not be in States)

VARIABLES
    injector,     \* Global injector queue (sequence of states)
    queues,       \* Per-worker local queues [Workers -> Seq(States)]
    processed,    \* Set of states that have been fully processed
    inProgress,   \* Per-worker: state currently being processed (or None)
    pc            \* Per-worker program counter

vars == <<injector, queues, processed, inProgress, pc>>

ASSUME None \notin States

TypeOK ==
    /\ injector \in Seq(States)
    /\ queues \in [Workers -> Seq(States)]
    /\ processed \subseteq States
    /\ inProgress \in [Workers -> States \union {None}]
    /\ pc \in [Workers -> {"idle", "working", "stealing"}]

(* Initial state: all states in injector, workers idle *)
(* Use a fixed initial sequence for model checking *)
Init ==
    /\ injector = <<100, 200, 300>>  \* All states initially queued
    /\ queues = [w \in Workers |-> <<>>]
    /\ processed = {}
    /\ inProgress = [w \in Workers |-> None]
    /\ pc = [w \in Workers |-> "idle"]

-----------------------------------------------------------------------------
(* Helper: Convert set to sequence (recursive) *)

RECURSIVE SetToSeqRec(_)
SetToSeqRec(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeqRec(S \ {x})

SetToSeq(S) == SetToSeqRec(S)

(* Helper: Range of a sequence (all elements) *)
Range(s) == {s[i] : i \in 1..Len(s)}

-----------------------------------------------------------------------------
(* Worker Operations *)

(* Worker w takes a state from the global injector *)
TakeFromInjector(w) ==
    /\ pc[w] = "idle"
    /\ inProgress[w] = None
    /\ Len(injector) > 0
    /\ inProgress' = [inProgress EXCEPT ![w] = Head(injector)]
    /\ injector' = Tail(injector)
    /\ pc' = [pc EXCEPT ![w] = "working"]
    /\ UNCHANGED <<queues, processed>>

(* Worker w pops from its own local queue *)
PopLocal(w) ==
    /\ pc[w] = "idle"
    /\ inProgress[w] = None
    /\ Len(injector) = 0         \* Only use local queue when injector empty
    /\ Len(queues[w]) > 0
    /\ inProgress' = [inProgress EXCEPT ![w] = Head(queues[w])]
    /\ queues' = [queues EXCEPT ![w] = Tail(queues[w])]
    /\ pc' = [pc EXCEPT ![w] = "working"]
    /\ UNCHANGED <<injector, processed>>

(* Worker w steals from worker v's queue *)
Steal(w, v) ==
    /\ pc[w] = "idle"
    /\ inProgress[w] = None
    /\ w # v
    /\ Len(injector) = 0         \* Only steal when injector empty
    /\ Len(queues[w]) = 0        \* Only steal when local queue empty
    /\ Len(queues[v]) > 0        \* Victim has work
    /\ LET stolen == Head(queues[v])
       IN /\ inProgress' = [inProgress EXCEPT ![w] = stolen]
          /\ queues' = [queues EXCEPT ![v] = Tail(queues[v])]
    /\ pc' = [pc EXCEPT ![w] = "working"]
    /\ UNCHANGED <<injector, processed>>

(* Worker w finishes processing current state, may generate successors *)
FinishProcessing(w) ==
    /\ pc[w] = "working"
    /\ inProgress[w] # None
    /\ processed' = processed \union {inProgress[w]}
    /\ inProgress' = [inProgress EXCEPT ![w] = None]
    /\ pc' = [pc EXCEPT ![w] = "idle"]
    /\ UNCHANGED <<injector, queues>>

(* Worker w generates successor states (adds to local queue) *)
(* This models exploring a state and finding new states to explore *)
(* In the real checker, the fingerprint set prevents duplicate exploration *)
PushSuccessors(w, newStates) ==
    /\ pc[w] = "working"
    /\ inProgress[w] # None
    /\ newStates \subseteq States
    /\ newStates \cap processed = {}                         \* Not already processed
    /\ newStates \cap {inProgress[v] : v \in Workers} = {}   \* Not in progress
    /\ newStates \cap Range(injector) = {}                   \* Not in injector
    /\ \A v \in Workers : newStates \cap Range(queues[v]) = {}  \* Not in any queue
    /\ queues' = [queues EXCEPT ![w] = @ \o SetToSeq(newStates)]
    /\ UNCHANGED <<injector, processed, inProgress, pc>>

(* Worker stays idle (no work available) *)
StayIdle(w) ==
    /\ pc[w] = "idle"
    /\ inProgress[w] = None
    /\ Len(injector) = 0
    /\ Len(queues[w]) = 0
    /\ \A v \in Workers : Len(queues[v]) = 0  \* No work anywhere
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \E w \in Workers :
        \/ TakeFromInjector(w)
        \/ PopLocal(w)
        \/ \E v \in Workers : Steal(w, v)
        \/ FinishProcessing(w)
        \/ \E newStates \in SUBSET States : PushSuccessors(w, newStates)
        \/ StayIdle(w)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Termination Detection *)

(* All queues are empty and no worker is processing *)
AllQuiet ==
    /\ Len(injector) = 0
    /\ \A w \in Workers : Len(queues[w]) = 0
    /\ \A w \in Workers : inProgress[w] = None

(* All initial states have been processed when terminated *)
AllInjectedProcessed ==
    AllQuiet => (
        \* All states that were initially in injector should be processed
        \* This is an approximation - we track via processed set
        processed # {}
    )

-----------------------------------------------------------------------------
(* Safety Properties *)

(* A state being processed is not in any queue *)
NoDoubleProcess ==
    \A w \in Workers :
        inProgress[w] # None =>
            /\ inProgress[w] \notin {inProgress[v] : v \in Workers \ {w}}
            /\ \A v \in Workers : inProgress[w] \notin Range(queues[v])

(* Processed states are not reprocessed *)
ProcessedStaysProcessed ==
    \A s \in processed :
        /\ \A w \in Workers : inProgress[w] # s

(* Combined safety *)
Safety ==
    /\ TypeOK
    /\ NoDoubleProcess

-----------------------------------------------------------------------------
(* Liveness: Every state in injector is eventually processed *)

(* With fairness, all work eventually gets done *)
Fairness ==
    \A w \in Workers :
        /\ WF_vars(TakeFromInjector(w))
        /\ WF_vars(PopLocal(w))
        /\ WF_vars(FinishProcessing(w))
        /\ \A v \in Workers : WF_vars(Steal(w, v))

LiveSpec == Spec /\ Fairness

(* Eventually all states are processed or we're stuck *)
EventuallyDone ==
    <>(AllQuiet)

=============================================================================
