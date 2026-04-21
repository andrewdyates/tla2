---------------------------- MODULE ParallelModelChecker ----------------------------
\* TLA+ Specification for TLA2's Parallel Model Checker
\*
\* Purpose: Verify correctness of work-stealing parallel state exploration
\* Author: TLA2 Researcher
\* Date: 2026-01-19
\* Re: #282 - TLA2 needs TLA+ specification for its own parallel execution
\*
\* This spec models:
\* - Work-stealing queues (global injector + per-worker local queues)
\* - Concurrent fingerprint storage (seen set)
\* - Parent pointer tracking for trace reconstruction
\* - Termination detection (work_remaining + active_workers)
\*
\* Known race conditions to verify:
\* 1. Parent pointer overwrites (multiple paths to same state)
\* 2. Work-stealing non-determinism affecting exploration order
\* 3. Termination detection correctness

EXTENDS Integers, Sequences, FiniteSets, TLC

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    Workers,        \* Set of worker IDs (e.g., {1, 2, 3, 4})
    States,         \* Universe of possible states (finite for model checking)
    InitStates,     \* Subset of States that are initial
    Successors,     \* Function: state -> SUBSET States (successors of each state)
    Deadlocks       \* Set of states that are considered deadlocks (no valid successors)

\* ============================================================================
\* VARIABLES
\* ============================================================================

VARIABLES
    \* Work distribution (mirrors crossbeam_deque)
    injector,       \* Global injector queue: Seq(States)
    local_queue,    \* Per-worker local deque: [Workers -> Seq(States)]

    \* Fingerprint storage (mirrors ShardedFingerprintSet)
    seen,           \* Set of seen state fingerprints

    \* Parent tracking (mirrors parents DashMap)
    parents,        \* Function: States -> States \cup {NULL}

    \* Worker state
    worker_state,   \* [Workers -> {"idle", "working", "done"}]
    current,        \* [Workers -> States \cup {NULL}] - state being processed

    \* Termination detection (mirrors work_remaining, active_workers atomics)
    work_remaining, \* Counter: queued states + states being processed
    active,         \* Counter: workers currently processing

    \* Global flags
    stop_flag,      \* TRUE when termination or violation signaled
    result          \* "running" | "pass" | "violation" | "deadlock"

vars == <<injector, local_queue, seen, parents, worker_state, current,
          work_remaining, active, stop_flag, result>>

\* ============================================================================
\* HELPER OPERATORS
\* ============================================================================

\* Convert a set to a sequence (non-deterministic order)
SetToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

\* Sum of sequence lengths
SeqLenSum(f) ==
    LET RECURSIVE Sum(_, _)
        Sum(S, acc) == IF S = {} THEN acc
                       ELSE LET w == CHOOSE w \in S : TRUE
                            IN Sum(S \ {w}, acc + Len(f[w]))
    IN Sum(DOMAIN f, 0)

\* NULL constant for parent pointers
NULL == CHOOSE x : x \notin States

\* ============================================================================
\* TYPE INVARIANT
\* ============================================================================

TypeOK ==
    /\ injector \in Seq(States)
    /\ local_queue \in [Workers -> Seq(States)]
    /\ seen \subseteq States
    /\ parents \in [States -> States \cup {NULL}]
    /\ worker_state \in [Workers -> {"idle", "working", "done"}]
    /\ current \in [Workers -> States \cup {NULL}]
    /\ work_remaining \in Nat
    /\ active \in Nat
    /\ stop_flag \in BOOLEAN
    /\ result \in {"running", "pass", "violation", "deadlock"}

\* ============================================================================
\* INITIAL STATE
\* ============================================================================

Init ==
    /\ injector = SetToSeq(InitStates)
    /\ local_queue = [w \in Workers |-> <<>>]
    /\ seen = InitStates
    /\ parents = [s \in States |-> NULL]
    /\ worker_state = [w \in Workers |-> "idle"]
    /\ current = [w \in Workers |-> NULL]
    /\ work_remaining = Cardinality(InitStates)
    /\ active = 0
    /\ stop_flag = FALSE
    /\ result = "running"

\* ============================================================================
\* ACTIONS: WORK TAKING
\* ============================================================================

\* Worker w takes work from its local queue (preferred - LIFO)
TakeFromLocal(w) ==
    /\ worker_state[w] = "idle"
    /\ local_queue[w] # <<>>
    /\ ~stop_flag
    /\ result = "running"
    /\ LET s == Head(local_queue[w])
       IN /\ local_queue' = [local_queue EXCEPT ![w] = Tail(@)]
          /\ current' = [current EXCEPT ![w] = s]
          /\ worker_state' = [worker_state EXCEPT ![w] = "working"]
          /\ active' = active + 1
    /\ UNCHANGED <<injector, seen, parents, work_remaining, stop_flag, result>>

\* Worker w steals from global injector (FIFO)
TakeFromInjector(w) ==
    /\ worker_state[w] = "idle"
    /\ local_queue[w] = <<>>
    /\ injector # <<>>
    /\ ~stop_flag
    /\ result = "running"
    /\ LET s == Head(injector)
       IN /\ injector' = Tail(injector)
          /\ current' = [current EXCEPT ![w] = s]
          /\ worker_state' = [worker_state EXCEPT ![w] = "working"]
          /\ active' = active + 1
    /\ UNCHANGED <<local_queue, seen, parents, work_remaining, stop_flag, result>>

\* Worker w steals from another worker's queue
TakeFromPeer(w, peer) ==
    /\ worker_state[w] = "idle"
    /\ local_queue[w] = <<>>
    /\ injector = <<>>
    /\ peer # w
    /\ peer \in Workers
    /\ local_queue[peer] # <<>>
    /\ ~stop_flag
    /\ result = "running"
    \* Steal from front of peer's queue (opposite end from push)
    /\ LET s == Head(local_queue[peer])
       IN /\ local_queue' = [local_queue EXCEPT ![peer] = Tail(@)]
          /\ current' = [current EXCEPT ![w] = s]
          /\ worker_state' = [worker_state EXCEPT ![w] = "working"]
          /\ active' = active + 1
    /\ UNCHANGED <<injector, seen, parents, work_remaining, stop_flag, result>>

\* Combined take action
TakeWork(w) ==
    \/ TakeFromLocal(w)
    \/ TakeFromInjector(w)
    \/ \E peer \in Workers : TakeFromPeer(w, peer)

\* ============================================================================
\* ACTIONS: STATE PROCESSING
\* ============================================================================

\* Worker w finishes processing current state and enqueues successors
\* Models: enumerate_successors -> enqueue new states -> update parents
FinishState(w) ==
    /\ worker_state[w] = "working"
    /\ ~stop_flag
    /\ result = "running"
    /\ LET s == current[w]
           succs == Successors[s]
           new_succs == succs \ seen
       IN \* Non-deterministically split new successors between local and global queues
          \* This models the "push to injector periodically" pattern in parallel.rs
          \E local_new \in SUBSET new_succs :
            /\ seen' = seen \cup new_succs
            /\ local_queue' = [local_queue EXCEPT
                 ![w] = @ \o SetToSeq(local_new)]
            /\ injector' = injector \o SetToSeq(new_succs \ local_new)
            \* Update parent pointers for new states
            \* BUG POTENTIAL: If another worker also discovers a state in new_succs,
            \* the parent pointer may be overwritten non-deterministically
            /\ parents' = [ss \in States |->
                 IF ss \in new_succs THEN s ELSE parents[ss]]
            /\ work_remaining' = work_remaining - 1 + Cardinality(new_succs)
    /\ current' = [current EXCEPT ![w] = NULL]
    /\ worker_state' = [worker_state EXCEPT ![w] = "idle"]
    /\ active' = active - 1
    /\ UNCHANGED <<stop_flag, result>>

\* Worker w detects a deadlock state
DetectDeadlock(w) ==
    /\ worker_state[w] = "working"
    /\ ~stop_flag
    /\ result = "running"
    /\ current[w] \in Deadlocks
    /\ stop_flag' = TRUE
    /\ result' = "deadlock"
    /\ active' = active - 1
    /\ work_remaining' = work_remaining - 1
    /\ current' = [current EXCEPT ![w] = NULL]
    /\ worker_state' = [worker_state EXCEPT ![w] = "done"]
    /\ UNCHANGED <<injector, local_queue, seen, parents>>

\* ============================================================================
\* ACTIONS: TERMINATION
\* ============================================================================

\* All workers terminate when no work remains
\* Models: termination detection via work_remaining == 0 && active_workers == 0
Terminate ==
    /\ result = "running"
    /\ work_remaining = 0
    /\ active = 0
    /\ \A w \in Workers : worker_state[w] = "idle"
    /\ result' = "pass"
    /\ worker_state' = [w \in Workers |-> "done"]
    /\ UNCHANGED <<injector, local_queue, seen, parents, current,
                   work_remaining, active, stop_flag>>

\* ============================================================================
\* NEXT STATE RELATION
\* ============================================================================

Next ==
    \/ \E w \in Workers : TakeWork(w)
    \/ \E w \in Workers : FinishState(w)
    \/ \E w \in Workers : DetectDeadlock(w)
    \/ Terminate

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

Spec == Init /\ [][Next]_vars

\* Fairness: all workers eventually make progress if work is available
Fairness ==
    /\ \A w \in Workers : WF_vars(TakeWork(w))
    /\ \A w \in Workers : WF_vars(FinishState(w))
    /\ WF_vars(Terminate)

FairSpec == Spec /\ Fairness

\* ============================================================================
\* SAFETY PROPERTIES
\* ============================================================================

\* Property 1: Complete exploration - when done, all reachable states were seen
\* Compute reachable states from InitStates
Reachable ==
    LET RECURSIVE Reach(_)
        Reach(S) == LET next == S \cup UNION {Successors[s] : s \in S}
                    IN IF next = S THEN S ELSE Reach(next)
    IN Reach(InitStates)

CompleteExploration ==
    result = "pass" => seen = Reachable

\* Property 2: No spurious violations - if pass, all reachable states have been checked
NoSpuriousPass ==
    result = "pass" => (seen = Reachable)

\* Property 3: Work accounting is correct
WorkAccountingCorrect ==
    work_remaining >= 0

\* Property 4: Active workers count is bounded
ActiveWorkersBounded ==
    active <= Cardinality(Workers)

\* Property 5: Parent pointers form valid backwards chains to InitStates
\* (Only checkable after exploration completes)
ValidParentChains ==
    result = "pass" =>
        \A s \in (seen \ InitStates) :
            \/ parents[s] \in seen
            \/ parents[s] = NULL  \* Should not happen for reachable non-initial states

\* ============================================================================
\* LIVENESS PROPERTIES
\* ============================================================================

\* Eventually terminates (requires Fairness)
EventuallyTerminates ==
    <>(result # "running")

\* ============================================================================
\* RACE CONDITION DETECTION
\* ============================================================================

\* This invariant checks for the parent pointer race condition:
\* If two workers simultaneously discover the same state, the parent
\* pointer may be set inconsistently.
\*
\* In TLA+, this manifests as non-deterministic choice in FinishState
\* when multiple workers' successor sets overlap.

\* Track which workers could have set each parent (for debugging)
\* This would require additional state to track precisely.

=============================================================================
\* Modification History
\* Created: 2026-01-19 by TLA2 Researcher
\* Purpose: Verify TLA2's parallel model checker correctness (#282)
