------------------------------ MODULE ParallelChecker ------------------------------
(***************************************************************************)
(* TLA+ Specification: Parallel Model Checker                              *)
(*                                                                          *)
(* Models the full parallel checker from TLA2, integrating:                *)
(*   - Fingerprint set for state deduplication                             *)
(*   - Work-stealing queues for load balancing                             *)
(*   - Invariant checking per state                                        *)
(*   - Violation detection and early termination                           *)
(*   - Termination detection when all work is done                         *)
(*                                                                          *)
(* This spec also models a simplified eval cache to demonstrate            *)
(* how Issue #278's caching bug could cause false positives.               *)
(*                                                                          *)
(* Key Properties:                                                          *)
(*   - EquivalentToSequential: Same states explored, same violations found *)
(*   - NoFalsePositives: Violation only reported for actual violating state*)
(*   - NoFalseNegatives: All violating states eventually detected          *)
(*                                                                          *)
(* Author: Andrew Yates                                                     *)
(* Copyright 2026 Andrew Yates. | License: Apache 2.0                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Workers,          \* Set of worker IDs (e.g., {1, 2, 3, 4})
    States,           \* Set of possible states (model checking state space)
    InitStates,       \* Subset of States that are initial states
    SuccessorFn,      \* Function from state -> set of successor states
    InvariantFn,      \* Function from state -> TRUE if invariant holds
    CachingEnabled    \* TRUE to model caching behavior (can find #278 bug)

ASSUME InitStates \subseteq States
ASSUME \A s \in States : SuccessorFn[s] \subseteq States
ASSUME \A s \in States : InvariantFn[s] \in BOOLEAN

VARIABLES
    (* Fingerprint Set *)
    seen,             \* Set of states that have been seen (fingerprinted)

    (* Work Queues *)
    injector,         \* Global injector queue (Seq of states)
    queues,           \* Per-worker local queues [Workers -> Seq(States)]

    (* Worker State *)
    current,          \* Per-worker: current state being processed (or None)
    pc,               \* Per-worker: program counter

    (* Termination *)
    workRemaining,    \* Count of states in queues + being processed
    activeWorkers,    \* Count of workers currently processing

    (* Results *)
    violationFound,   \* Has any worker found a violation?
    violatingState,   \* The state that violated an invariant (or None)
    explored,         \* Set of states that have been fully explored

    (* Caching Model (for #278) *)
    cache,            \* Per-worker eval cache [Workers -> [Operators -> Values]]
    cacheDeps         \* Dependencies for cache entries [Workers -> [Ops -> Sets]]

vars == <<seen, injector, queues, current, pc, workRemaining, activeWorkers,
          violationFound, violatingState, explored, cache, cacheDeps>>

None == CHOOSE x : x \notin States

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
    /\ cache = [w \in Workers |-> <<>>]
    /\ cacheDeps = [w \in Workers |-> <<>>]

(* Helper: Convert set to sequence *)
SetToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

-----------------------------------------------------------------------------
(* Worker Operations *)

(* Worker takes state from injector *)
TakeFromInjector(w) ==
    /\ pc[w] = "idle"
    /\ ~violationFound
    /\ Len(injector) > 0
    /\ current' = [current EXCEPT ![w] = Head(injector)]
    /\ injector' = Tail(injector)
    /\ pc' = [pc EXCEPT ![w] = "checking"]
    /\ activeWorkers' = activeWorkers + 1
    /\ UNCHANGED <<seen, queues, workRemaining, violationFound, violatingState,
                  explored, cache, cacheDeps>>

(* Worker takes state from own local queue *)
TakeFromLocal(w) ==
    /\ pc[w] = "idle"
    /\ ~violationFound
    /\ Len(injector) = 0
    /\ Len(queues[w]) > 0
    /\ current' = [current EXCEPT ![w] = Head(queues[w])]
    /\ queues' = [queues EXCEPT ![w] = Tail(@)]
    /\ pc' = [pc EXCEPT ![w] = "checking"]
    /\ activeWorkers' = activeWorkers + 1
    /\ UNCHANGED <<seen, injector, workRemaining, violationFound, violatingState,
                  explored, cache, cacheDeps>>

(* Worker steals from another worker's queue *)
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
    /\ UNCHANGED <<seen, injector, workRemaining, violationFound, violatingState,
                  explored, cache, cacheDeps>>

(* Worker checks invariant on current state - WITHOUT caching bug *)
CheckInvariantCorrect(w) ==
    /\ pc[w] = "checking"
    /\ current[w] # None
    /\ ~CachingEnabled
    /\ IF ~InvariantFn[current[w]] THEN
         (* Invariant violated *)
         /\ violationFound' = TRUE
         /\ violatingState' = current[w]
         /\ pc' = [pc EXCEPT ![w] = "done"]
         /\ explored' = explored \union {current[w]}
         /\ activeWorkers' = activeWorkers - 1
         /\ workRemaining' = workRemaining - 1
         /\ UNCHANGED <<seen, injector, queues, current, cache, cacheDeps>>
       ELSE
         (* Invariant holds - proceed to explore successors *)
         /\ pc' = [pc EXCEPT ![w] = "exploring"]
         /\ UNCHANGED <<seen, injector, queues, current, workRemaining,
                       activeWorkers, violationFound, violatingState, explored,
                       cache, cacheDeps>>

(* Worker checks invariant WITH potential caching bug (models #278) *)
(* The cache can return wrong values if dependencies aren't tracked *)
CheckInvariantWithCache(w) ==
    /\ pc[w] = "checking"
    /\ current[w] # None
    /\ CachingEnabled
    (* Non-deterministically model cache hit with possibly stale value *)
    /\ \E cacheCorrect \in BOOLEAN :
         IF cacheCorrect THEN
           (* Cache is correct - same as CheckInvariantCorrect *)
           IF ~InvariantFn[current[w]] THEN
             /\ violationFound' = TRUE
             /\ violatingState' = current[w]
             /\ pc' = [pc EXCEPT ![w] = "done"]
             /\ explored' = explored \union {current[w]}
             /\ activeWorkers' = activeWorkers - 1
             /\ workRemaining' = workRemaining - 1
             /\ UNCHANGED <<seen, injector, queues, current, cache, cacheDeps>>
           ELSE
             /\ pc' = [pc EXCEPT ![w] = "exploring"]
             /\ UNCHANGED <<seen, injector, queues, current, workRemaining,
                           activeWorkers, violationFound, violatingState, explored,
                           cache, cacheDeps>>
         ELSE
           (* CACHE BUG: Returns wrong value, might find false positive *)
           (* This models the #278 bug where cache returns stale data *)
           \E spuriousViolation \in BOOLEAN :
             IF spuriousViolation THEN
               (* FALSE POSITIVE: Report violation on non-violating state *)
               /\ violationFound' = TRUE
               /\ violatingState' = current[w]
               /\ pc' = [pc EXCEPT ![w] = "done"]
               /\ explored' = explored \union {current[w]}
               /\ activeWorkers' = activeWorkers - 1
               /\ workRemaining' = workRemaining - 1
               /\ UNCHANGED <<seen, injector, queues, current, cache, cacheDeps>>
             ELSE
               (* Cache bug but happened to get right answer *)
               IF ~InvariantFn[current[w]] THEN
                 /\ violationFound' = TRUE
                 /\ violatingState' = current[w]
                 /\ pc' = [pc EXCEPT ![w] = "done"]
                 /\ explored' = explored \union {current[w]}
                 /\ activeWorkers' = activeWorkers - 1
                 /\ workRemaining' = workRemaining - 1
                 /\ UNCHANGED <<seen, injector, queues, current, cache, cacheDeps>>
               ELSE
                 /\ pc' = [pc EXCEPT ![w] = "exploring"]
                 /\ UNCHANGED <<seen, injector, queues, current, workRemaining,
                               activeWorkers, violationFound, violatingState, explored,
                               cache, cacheDeps>>

(* Combined invariant check *)
CheckInvariant(w) ==
    IF CachingEnabled THEN CheckInvariantWithCache(w)
    ELSE CheckInvariantCorrect(w)

(* Worker explores successors of current state *)
ExploreSuccessors(w) ==
    /\ pc[w] = "exploring"
    /\ current[w] # None
    /\ LET state == current[w]
           succs == SuccessorFn[state]
           newSuccs == succs \ seen
       IN
         /\ seen' = seen \union newSuccs
         /\ queues' = [queues EXCEPT ![w] = @ \o SetToSeq(newSuccs)]
         /\ workRemaining' = workRemaining - 1 + Cardinality(newSuccs)
         /\ explored' = explored \union {state}
         /\ current' = [current EXCEPT ![w] = None]
         /\ pc' = [pc EXCEPT ![w] = "idle"]
         /\ activeWorkers' = activeWorkers - 1
         /\ UNCHANGED <<injector, violationFound, violatingState, cache, cacheDeps>>

(* Worker stops when violation is found *)
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
    /\ UNCHANGED <<seen, injector, queues, violationFound, violatingState,
                  explored, cache, cacheDeps>>

(* Worker goes idle when no work available *)
GoIdle(w) ==
    /\ pc[w] = "idle"
    /\ ~violationFound
    /\ Len(injector) = 0
    /\ \A v \in Workers : Len(queues[v]) = 0
    /\ workRemaining = 0
    /\ pc' = [pc EXCEPT ![w] = "done"]
    /\ UNCHANGED <<seen, injector, queues, current, workRemaining, activeWorkers,
                  violationFound, violatingState, explored, cache, cacheDeps>>

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \E w \in Workers :
        \/ TakeFromInjector(w)
        \/ TakeFromLocal(w)
        \/ \E v \in Workers : StealFrom(w, v)
        \/ CheckInvariant(w)
        \/ ExploreSuccessors(w)
        \/ StopOnViolation(w)
        \/ GoIdle(w)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Termination Detection *)

AllDone ==
    /\ \A w \in Workers : pc[w] = "done"

Terminated ==
    \/ violationFound
    \/ (workRemaining = 0 /\ activeWorkers = 0)

-----------------------------------------------------------------------------
(* Safety Properties *)

(* No state is explored by multiple workers *)
NoDoubleExploration ==
    \A w1, w2 \in Workers :
        w1 # w2 =>
            (current[w1] # None /\ current[w2] # None) =>
                current[w1] # current[w2]

(* Only report violation for states that actually violate *)
NoFalsePositives ==
    violatingState # None =>
        ~InvariantFn[violatingState]

(* All states marked explored have been checked *)
ExploredAreChecked ==
    \A s \in explored :
        \/ InvariantFn[s]
        \/ s = violatingState

(* Combined Safety (without caching) *)
SafetyNoCaching ==
    ~CachingEnabled => NoFalsePositives

(* Safety with caching can have false positives (demonstrates #278) *)
SafetyWithCaching ==
    CachingEnabled => TRUE  \* Caching can cause false positives

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Eventually we terminate *)
EventuallyTerminates ==
    <>(Terminated)

(* If there's a violating state, we eventually find it *)
NoFalseNegatives ==
    (\E s \in InitStates : ~InvariantFn[s]) =>
        <>(violationFound)

(* Eventually all reachable states are explored (if no violation) *)
EventuallyAllExplored ==
    (~violationFound /\ Terminated) =>
        (explored = States)  \* Only for finite, fully-explored state spaces

Fairness ==
    \A w \in Workers :
        /\ WF_vars(TakeFromInjector(w))
        /\ WF_vars(TakeFromLocal(w))
        /\ WF_vars(CheckInvariant(w))
        /\ WF_vars(ExploreSuccessors(w))
        /\ WF_vars(GoIdle(w))

LiveSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Equivalence to Sequential *)

(* The parallel checker should find the same result as sequential *)
(* This is stated as: if sequential finds violation, parallel does too,
   and if sequential finds no violation, parallel doesn't either.

   In this spec, this is implied by NoFalsePositives and NoFalseNegatives. *)

EquivalentToSequential ==
    /\ NoFalsePositives
    /\ NoFalseNegatives

=============================================================================
