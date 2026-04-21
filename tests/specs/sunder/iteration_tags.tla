-------------------------------- MODULE iteration_tags --------------------------------
(* TLA+ specification for commit tag iteration uniqueness
   Author: Andrew Yates <andrewyates.name@gmail.com>

   Models a lock-based iteration assignment protocol used by an external
   runner that allocates monotonically increasing commit tags.

   Key properties to verify:
   1. UniqueIterations: No two sessions get the same iteration number
   2. MonotonicGit: Git history iterations are strictly increasing
   3. LockSafety: Only one session reads+writes the tag file at a time
   4. Progress: Sessions eventually get an iteration or fail with timeout
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    None,           \* Model value for "no value" (distinct from all Sessions)
    Sessions,       \* Set of concurrent session IDs
    MaxIteration,   \* Upper bound for iteration numbers
    MaxSteps        \* Bound for model checking

VARIABLES
    \* Shared state
    lockHolder,     \* None or session ID holding the fcntl lock
    tagFile,        \* Current value in .commit_tag_{role} file (or -1 if doesn't exist)
    gitHistory,     \* Set of iteration numbers committed to git

    \* Per-session state
    sessionState,   \* Function: Session -> "idle" | "acquiring" | "holding" | "done" | "failed"
    assignedIter,   \* Function: Session -> assigned iteration (-1 if none)

    \* Model checking
    step            \* Step counter for bounded checking

vars == <<lockHolder, tagFile, gitHistory, sessionState, assignedIter, step>>

-----------------------------------------------------------------------------
(* Type invariants *)

TypeOK ==
    /\ lockHolder \in {None} \cup Sessions
    /\ tagFile \in -1..MaxIteration
    /\ gitHistory \subseteq 0..MaxIteration
    /\ sessionState \in [Sessions -> {"idle", "acquiring", "holding", "done", "failed"}]
    /\ assignedIter \in [Sessions -> -1..MaxIteration]
    /\ step \in Nat

-----------------------------------------------------------------------------
(* Helper definitions *)

\* Maximum iteration in git history (0 if empty)
MaxGitIteration ==
    IF gitHistory = {} THEN 0
    ELSE CHOOSE m \in gitHistory : \A n \in gitHistory : m >= n

\* Next iteration is max(tagFile, maxGit) + 1
NextIteration ==
    LET maxGit == MaxGitIteration
        maxFile == IF tagFile = -1 THEN 0 ELSE tagFile
    IN IF maxGit >= maxFile THEN maxGit + 1 ELSE maxFile + 1

\* Lock is available (no one holding)
LockAvailable == lockHolder = None

\* Session is in a terminal state
SessionTerminated(s) == sessionState[s] \in {"done", "failed"}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ lockHolder = None
    /\ tagFile = -1                                  \* File may not exist initially
    /\ gitHistory = {}                               \* Empty git history
    /\ sessionState = [s \in Sessions |-> "idle"]
    /\ assignedIter = [s \in Sessions |-> -1]
    /\ step = 0

-----------------------------------------------------------------------------
(* Actions *)

\* Session attempts to acquire fcntl lock (models _acquire_lock_with_timeout)
TryAcquireLock(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "idle"
    /\ LockAvailable                                 \* fcntl LOCK_EX|LOCK_NB succeeds
    /\ lockHolder' = s
    /\ sessionState' = [sessionState EXCEPT ![s] = "holding"]
    /\ UNCHANGED <<tagFile, gitHistory, assignedIter>>
    /\ step' = step + 1

\* Lock acquisition fails (another session holds it), session keeps trying
FailAcquireLock(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "idle"
    /\ ~LockAvailable                                \* LOCK_NB would block
    /\ sessionState' = [sessionState EXCEPT ![s] = "acquiring"]
    /\ UNCHANGED <<lockHolder, tagFile, gitHistory, assignedIter>>
    /\ step' = step + 1

\* Session in acquiring state gets the lock (lock holder released)
RetryAcquireLock(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "acquiring"
    /\ LockAvailable
    /\ lockHolder' = s
    /\ sessionState' = [sessionState EXCEPT ![s] = "holding"]
    /\ UNCHANGED <<tagFile, gitHistory, assignedIter>>
    /\ step' = step + 1

\* Session times out waiting for lock (models 30s timeout)
TimeoutAcquiring(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "acquiring"
    /\ sessionState' = [sessionState EXCEPT ![s] = "failed"]
    /\ UNCHANGED <<lockHolder, tagFile, gitHistory, assignedIter>>
    /\ step' = step + 1

\* Session reads file and git, computes next iteration, writes file, releases lock
\* This is atomic because we hold the fcntl lock
ComputeAndRelease(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "holding"
    /\ lockHolder = s                                \* Verify we hold lock
    /\ NextIteration <= MaxIteration                 \* Within bounds
    /\ LET nextIter == NextIteration
       IN /\ assignedIter' = [assignedIter EXCEPT ![s] = nextIter]
          /\ tagFile' = nextIter                     \* Write to tag file
          /\ lockHolder' = None                       \* Release fcntl lock
          /\ sessionState' = [sessionState EXCEPT ![s] = "done"]
    /\ UNCHANGED <<gitHistory>>
    /\ step' = step + 1

\* Session commits to git (iteration becomes part of authoritative history)
\* This happens AFTER releasing the iteration lock (separate operation)
CommitToGit(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "done"
    /\ assignedIter[s] /= -1
    /\ assignedIter[s] \notin gitHistory             \* Not already in history
    /\ gitHistory' = gitHistory \cup {assignedIter[s]}
    /\ UNCHANGED <<lockHolder, tagFile, sessionState, assignedIter>>
    /\ step' = step + 1

-----------------------------------------------------------------------------
(* Next state relation *)

\* AllTerminated - all sessions have reached terminal states
AllTerminated ==
    \A s \in Sessions : SessionTerminated(s)

\* Termination - allows model to end gracefully at step bound or when all done
Terminate ==
    /\ (step >= MaxSteps \/ AllTerminated)
    /\ UNCHANGED vars

Next ==
    \/ \E s \in Sessions : TryAcquireLock(s)
    \/ \E s \in Sessions : FailAcquireLock(s)
    \/ \E s \in Sessions : RetryAcquireLock(s)
    \/ \E s \in Sessions : TimeoutAcquiring(s)
    \/ \E s \in Sessions : ComputeAndRelease(s)
    \/ \E s \in Sessions : CommitToGit(s)
    \/ Terminate

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties - INVARIANTS *)

\* INVARIANT 1: Mutual Exclusion on Lock
\* At most one session holds the lock
LockMutex ==
    Cardinality({s \in Sessions : lockHolder = s}) <= 1

\* INVARIANT 2: Unique Iterations
\* No two sessions are assigned the same iteration
UniqueIterations ==
    \A s1, s2 \in Sessions :
        (s1 /= s2 /\ assignedIter[s1] /= -1 /\ assignedIter[s2] /= -1)
            => assignedIter[s1] /= assignedIter[s2]

\* INVARIANT 3: Holder Consistency
\* If session is in "holding" state, it must be the lock holder
HolderConsistency ==
    \A s \in Sessions :
        sessionState[s] = "holding" => lockHolder = s

\* INVARIANT 4: Assignment Consistency
\* Assigned iterations are positive (valid)
ValidAssignments ==
    \A s \in Sessions :
        assignedIter[s] /= -1 => assignedIter[s] >= 1

\* INVARIANT 5: No Phantom Assignments
\* Only done sessions have assigned iterations
DoneHasAssignment ==
    \A s \in Sessions :
        sessionState[s] = "done" <=> assignedIter[s] /= -1

\* INVARIANT 6: Git Monotonicity
\* All iterations in git history are unique (set property guarantees this)
\* The real check is that no duplicate can be committed
NoDuplicateCommits ==
    \A s \in Sessions :
        (assignedIter[s] /= -1 /\ assignedIter[s] \in gitHistory)
            => sessionState[s] = "done"  \* Only committed if done

\* Combined safety invariant
Safety ==
    /\ LockMutex
    /\ UniqueIterations
    /\ HolderConsistency
    /\ ValidAssignments

-----------------------------------------------------------------------------
(* Liveness Properties - PROPERTIES (require fairness) *)

\* PROPERTY 1: Progress
\* Every idle session eventually reaches done or failed
EventualTermination ==
    \A s \in Sessions :
        sessionState[s] = "idle" ~> SessionTerminated(s)

\* PROPERTY 2: Lock Progress
\* If lock is available and session is acquiring, it eventually gets it
LockProgress ==
    \A s \in Sessions :
        (sessionState[s] = "acquiring" /\ LockAvailable) ~>
            (sessionState[s] = "holding" \/ sessionState[s] = "failed")

-----------------------------------------------------------------------------
(* Fairness *)

Fairness ==
    /\ \A s \in Sessions : WF_vars(TryAcquireLock(s))
    /\ \A s \in Sessions : WF_vars(RetryAcquireLock(s))
    /\ \A s \in Sessions : WF_vars(ComputeAndRelease(s))
    /\ \A s \in Sessions : SF_vars(CommitToGit(s))

FairSpec == Spec /\ Fairness

=============================================================================
