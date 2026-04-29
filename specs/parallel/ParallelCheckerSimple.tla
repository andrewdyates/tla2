--------------------------- MODULE ParallelCheckerSimple ---------------------------
(***************************************************************************)
(* TLA+ Specification: Simplified Parallel Model Checker                   *)
(*                                                                          *)
(* A simplified version of ParallelChecker with concrete state graph       *)
(* for model checking with both TLC and TLA2.                              *)
(*                                                                          *)
(* Author: Andrew Yates                                                     *)
(* Copyright 2026 Dropbox. | License: Apache 2.0                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Workers,          \* Set of worker IDs (e.g., {1, 2})
    CachingEnabled    \* TRUE to model caching behavior (can find #278 bug)

\* Concrete state space: simple 3-state graph
States == {100, 200, 300}
InitStates == {100}
None == 0

\* Successor function: 100 -> 200 -> 300 -> (done)
Successors(s) ==
    CASE s = 100 -> {200}
      [] s = 200 -> {300}
      [] s = 300 -> {}
      [] OTHER -> {}

\* Invariant function: all states pass (no true violations)
InvariantHolds(s) ==
    CASE s = 100 -> TRUE
      [] s = 200 -> TRUE
      [] s = 300 -> TRUE
      [] OTHER -> TRUE

VARIABLES
    seen,             \* Set of states that have been seen
    injector,         \* Global injector queue
    queues,           \* Per-worker local queues
    current,          \* Per-worker current state
    pc,               \* Per-worker program counter
    workRemaining,    \* States in queues + being processed
    activeWorkers,    \* Workers currently processing
    violationFound,   \* Has a violation been found?
    violatingState,   \* The violating state (or None)
    explored          \* Set of fully explored states

vars == <<seen, injector, queues, current, pc, workRemaining, activeWorkers,
          violationFound, violatingState, explored>>

TypeOK ==
    /\ seen \subseteq States
    /\ injector \in Seq(States)
    /\ queues \in [Workers -> Seq(States)]
    /\ current \in [Workers -> States \union {None}]
    /\ pc \in [Workers -> {"idle", "checking", "exploring", "done"}]
    /\ workRemaining \in Nat
    /\ activeWorkers \in 0..Cardinality(Workers)
    /\ violationFound \in BOOLEAN
    /\ violatingState \in States \union {None}
    /\ explored \subseteq States

-----------------------------------------------------------------------------
(* Helper: Convert set to sequence *)

RECURSIVE SetToSeqRec(_)
SetToSeqRec(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeqRec(S \ {x})

SetToSeq(S) == SetToSeqRec(S)

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ seen = InitStates
    /\ injector = SetToSeq(InitStates)
    /\ queues = [w \in Workers |-> <<>>]
    /\ current = [w \in Workers |-> None]
    /\ pc = [w \in Workers |-> "idle"]
    /\ workRemaining = Cardinality(InitStates)
    /\ activeWorkers = 0
    /\ violationFound = FALSE
    /\ violatingState = None
    /\ explored = {}

-----------------------------------------------------------------------------
(* Worker Operations *)

TakeFromInjector(w) ==
    /\ pc[w] = "idle"
    /\ ~violationFound
    /\ Len(injector) > 0
    /\ current' = [current EXCEPT ![w] = Head(injector)]
    /\ injector' = Tail(injector)
    /\ pc' = [pc EXCEPT ![w] = "checking"]
    /\ activeWorkers' = activeWorkers + 1
    /\ UNCHANGED <<seen, queues, workRemaining, violationFound, violatingState, explored>>

TakeFromLocal(w) ==
    /\ pc[w] = "idle"
    /\ ~violationFound
    /\ Len(injector) = 0
    /\ Len(queues[w]) > 0
    /\ current' = [current EXCEPT ![w] = Head(queues[w])]
    /\ queues' = [queues EXCEPT ![w] = Tail(@)]
    /\ pc' = [pc EXCEPT ![w] = "checking"]
    /\ activeWorkers' = activeWorkers + 1
    /\ UNCHANGED <<seen, injector, workRemaining, violationFound, violatingState, explored>>

StealFrom(w, v) ==
    /\ pc[w] = "idle"
    /\ ~violationFound
    /\ w # v
    /\ Len(injector) = 0
    /\ Len(queues[w]) = 0
    /\ Len(queues[v]) > 0
    /\ current' = [current EXCEPT ![w] = Head(queues[v])]
    /\ queues' = [queues EXCEPT ![v] = Tail(@)]
    /\ pc' = [pc EXCEPT ![w] = "checking"]
    /\ activeWorkers' = activeWorkers + 1
    /\ UNCHANGED <<seen, injector, workRemaining, violationFound, violatingState, explored>>

(* Check invariant - correct version (no caching bugs) *)
CheckInvariantCorrect(w) ==
    /\ pc[w] = "checking"
    /\ current[w] # None
    /\ ~CachingEnabled
    /\ IF ~InvariantHolds(current[w]) THEN
         /\ violationFound' = TRUE
         /\ violatingState' = current[w]
         /\ pc' = [pc EXCEPT ![w] = "done"]
         /\ explored' = explored \union {current[w]}
         /\ activeWorkers' = activeWorkers - 1
         /\ workRemaining' = workRemaining - 1
         /\ UNCHANGED <<seen, injector, queues, current>>
       ELSE
         /\ pc' = [pc EXCEPT ![w] = "exploring"]
         /\ UNCHANGED <<seen, injector, queues, current, workRemaining,
                       activeWorkers, violationFound, violatingState, explored>>

(* Check invariant - WITH caching bug (models #278) *)
CheckInvariantWithCache(w) ==
    /\ pc[w] = "checking"
    /\ current[w] # None
    /\ CachingEnabled
    /\ \E cacheCorrect \in BOOLEAN :
         IF cacheCorrect THEN
           IF ~InvariantHolds(current[w]) THEN
             /\ violationFound' = TRUE
             /\ violatingState' = current[w]
             /\ pc' = [pc EXCEPT ![w] = "done"]
             /\ explored' = explored \union {current[w]}
             /\ activeWorkers' = activeWorkers - 1
             /\ workRemaining' = workRemaining - 1
             /\ UNCHANGED <<seen, injector, queues, current>>
           ELSE
             /\ pc' = [pc EXCEPT ![w] = "exploring"]
             /\ UNCHANGED <<seen, injector, queues, current, workRemaining,
                           activeWorkers, violationFound, violatingState, explored>>
         ELSE
           \* CACHE BUG: Can cause false positive (like #278)
           \E spuriousViolation \in BOOLEAN :
             IF spuriousViolation THEN
               /\ violationFound' = TRUE
               /\ violatingState' = current[w]
               /\ pc' = [pc EXCEPT ![w] = "done"]
               /\ explored' = explored \union {current[w]}
               /\ activeWorkers' = activeWorkers - 1
               /\ workRemaining' = workRemaining - 1
               /\ UNCHANGED <<seen, injector, queues, current>>
             ELSE
               IF ~InvariantHolds(current[w]) THEN
                 /\ violationFound' = TRUE
                 /\ violatingState' = current[w]
                 /\ pc' = [pc EXCEPT ![w] = "done"]
                 /\ explored' = explored \union {current[w]}
                 /\ activeWorkers' = activeWorkers - 1
                 /\ workRemaining' = workRemaining - 1
                 /\ UNCHANGED <<seen, injector, queues, current>>
               ELSE
                 /\ pc' = [pc EXCEPT ![w] = "exploring"]
                 /\ UNCHANGED <<seen, injector, queues, current, workRemaining,
                               activeWorkers, violationFound, violatingState, explored>>

CheckInvariant(w) ==
    IF CachingEnabled THEN CheckInvariantWithCache(w)
    ELSE CheckInvariantCorrect(w)

ExploreSuccessors(w) ==
    /\ pc[w] = "exploring"
    /\ current[w] # None
    /\ LET state == current[w]
           succs == Successors(state)
           newSuccs == succs \ seen
       IN
         /\ seen' = seen \union newSuccs
         /\ queues' = [queues EXCEPT ![w] = @ \o SetToSeq(newSuccs)]
         /\ workRemaining' = workRemaining - 1 + Cardinality(newSuccs)
         /\ explored' = explored \union {state}
         /\ current' = [current EXCEPT ![w] = None]
         /\ pc' = [pc EXCEPT ![w] = "idle"]
         /\ activeWorkers' = activeWorkers - 1
         /\ UNCHANGED <<injector, violationFound, violatingState>>

StopOnViolation(w) ==
    /\ violationFound
    /\ pc[w] # "done"
    /\ pc' = [pc EXCEPT ![w] = "done"]
    /\ IF current[w] # None THEN
         /\ activeWorkers' = activeWorkers - 1
         /\ workRemaining' = workRemaining - 1
       ELSE
         UNCHANGED <<activeWorkers, workRemaining>>
    /\ current' = [current EXCEPT ![w] = None]
    /\ UNCHANGED <<seen, injector, queues, violationFound, violatingState, explored>>

GoIdle(w) ==
    /\ pc[w] = "idle"
    /\ ~violationFound
    /\ Len(injector) = 0
    /\ \A v \in Workers : Len(queues[v]) = 0
    /\ workRemaining = 0
    /\ pc' = [pc EXCEPT ![w] = "done"]
    /\ UNCHANGED <<seen, injector, queues, current, workRemaining, activeWorkers,
                  violationFound, violatingState, explored>>

(* Termination: allow stuttering when done *)
Terminated ==
    /\ \A w \in Workers : pc[w] = "done"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E w \in Workers :
        \/ TakeFromInjector(w)
        \/ TakeFromLocal(w)
        \/ \E v \in Workers : StealFrom(w, v)
        \/ CheckInvariant(w)
        \/ ExploreSuccessors(w)
        \/ StopOnViolation(w)
        \/ GoIdle(w)
    \/ Terminated

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

NoDoubleExploration ==
    \A w1, w2 \in Workers :
        (w1 # w2) =>
            ((current[w1] # None /\ current[w2] # None) =>
                (current[w1] # current[w2]))

NoFalsePositives ==
    violatingState # None => ~InvariantHolds(violatingState)

SafetyNoCaching ==
    ~CachingEnabled => NoFalsePositives

=============================================================================
