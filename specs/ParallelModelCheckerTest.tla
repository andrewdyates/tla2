---------------------------- MODULE ParallelModelCheckerTest ----------------------------
\* Test variant of ParallelModelChecker with built-in Successors function
\* This allows verification without complex config file expressions
\*
\* Author: TLA2 Researcher
\* Date: 2026-01-19
\* Re: #282

EXTENDS Integers, Sequences, FiniteSets, TLC

\* ============================================================================
\* CONSTANTS (simplified for testing)
\* ============================================================================

\* Two workers
Workers == {1, 2}

\* Small state space: diamond pattern
\*      s1
\*     /  \
\*    s2  s3
\*     \  /
\*      s4
States == {"s1", "s2", "s3", "s4"}
InitStates == {"s1"}

\* Successor function (defined here instead of config)
Successors == [s \in States |->
    CASE s = "s1" -> {"s2", "s3"}
      [] s = "s2" -> {"s4"}
      [] s = "s3" -> {"s4"}
      [] s = "s4" -> {}
]

\* No deadlock states in this test (s4 is terminal, not a deadlock)
Deadlocks == {}

\* NULL constant for parent pointers
NULL == "NULL"

\* ============================================================================
\* VARIABLES
\* ============================================================================

VARIABLES
    injector,       \* Global injector queue: Seq(States)
    local_queue,    \* Per-worker local deque: [Workers -> Seq(States)]
    seen,           \* Set of seen state fingerprints
    parents,        \* Function: States -> States \cup {NULL}
    worker_state,   \* [Workers -> {"idle", "working", "done"}]
    current,        \* [Workers -> States \cup {NULL}] - state being processed
    work_remaining, \* Counter: queued states + states being processed
    active,         \* Counter: workers currently processing
    stop_flag,      \* TRUE when termination or violation signaled
    result          \* "running" | "pass" | "violation" | "deadlock"

vars == <<injector, local_queue, seen, parents, worker_state, current,
          work_remaining, active, stop_flag, result>>

\* ============================================================================
\* HELPER OPERATORS
\* ============================================================================

\* Convert a set to a sequence (non-deterministic order)
RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

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
FinishState(w) ==
    /\ worker_state[w] = "working"
    /\ ~stop_flag
    /\ result = "running"
    /\ current[w] \notin Deadlocks
    /\ LET s == current[w]
           succs == Successors[s]
           new_succs == succs \ seen
       IN \E local_new \in SUBSET new_succs :
            /\ seen' = seen \cup new_succs
            /\ local_queue' = [local_queue EXCEPT
                 ![w] = @ \o SetToSeq(local_new)]
            /\ injector' = injector \o SetToSeq(new_succs \ local_new)
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

\* Fairness
Fairness ==
    /\ \A w \in Workers : WF_vars(TakeWork(w))
    /\ \A w \in Workers : WF_vars(FinishState(w))
    /\ WF_vars(Terminate)

FairSpec == Spec /\ Fairness

\* ============================================================================
\* SAFETY PROPERTIES
\* ============================================================================

\* Reachable states from InitStates
RECURSIVE Reach(_)
Reach(S) == LET next == S \cup UNION {Successors[s] : s \in S}
            IN IF next = S THEN S ELSE Reach(next)

Reachable == Reach(InitStates)

\* When done, all reachable states were seen
CompleteExploration ==
    result = "pass" => seen = Reachable

\* Work accounting is correct
WorkAccountingCorrect ==
    work_remaining >= 0

\* Active workers count is bounded
ActiveWorkersBounded ==
    active <= Cardinality(Workers)

=============================================================================
