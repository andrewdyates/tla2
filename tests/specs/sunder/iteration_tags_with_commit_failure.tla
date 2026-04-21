-------------------------------- MODULE iteration_tags_with_commit_failure --------------------------------
(* TLA+ specification for commit tag iteration uniqueness
   with COMMIT FAILURE scenarios

   Author: Andrew Yates <andrewyates.name@gmail.com>

   Based on iteration_tags.tla, extended to model:
   - Commit failures (pre-commit hook, network error, etc.)
   - Commit retries
   - The gap scenario where iteration is assigned but never committed

   Models a lock-based iteration assignment protocol used by an external
   runner that allocates monotonically increasing commit tags.

   Key properties to verify:
   1. UniqueIterations: No two sessions get the same iteration number
   2. MonotonicGit: Git history iterations are strictly increasing
   3. LockSafety: Only one session reads+writes the tag file at a time
   4. Progress: Sessions eventually get an iteration or fail with timeout
   5. GapDetection: Detect when tagFile > max(gitHistory) due to failed commits
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    None,               \* Model value for "no value" (distinct from all Sessions)
    Sessions,           \* Set of concurrent session IDs
    MaxIteration,       \* Upper bound for iteration numbers
    MaxSteps,           \* Bound for model checking
    MaxCommitAttempts   \* Max retries before commit failure becomes permanent

VARIABLES
    \* Shared state
    lockHolder,     \* None or session ID holding the fcntl lock
    tagFile,        \* Current value in .commit_tag_{role} file (or -1 if doesn't exist)
    gitHistory,     \* Set of iteration numbers committed to git

    \* Per-session state
    sessionState,   \* Function: Session -> "idle" | "acquiring" | "holding" |
                    \*   "committing" | "done" | "failed"
    assignedIter,   \* Function: Session -> assigned iteration (-1 if none)
    commitAttempts, \* Function: Session -> number of commit attempts made

    \* Model checking
    step            \* Step counter for bounded checking

vars == <<lockHolder, tagFile, gitHistory, sessionState, assignedIter, commitAttempts, step>>

-----------------------------------------------------------------------------
(* Type invariants *)

TypeOK ==
    /\ lockHolder \in {None} \cup Sessions
    /\ tagFile \in -1..MaxIteration
    /\ gitHistory \subseteq 0..MaxIteration
    /\ sessionState \in [Sessions -> {"idle", "acquiring", "holding",
                                       "committing", "done", "failed"}]
    /\ assignedIter \in [Sessions -> -1..MaxIteration]
    /\ commitAttempts \in [Sessions -> 0..MaxCommitAttempts]
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

\* Session can still retry commit
CanRetryCommit(s) == commitAttempts[s] < MaxCommitAttempts

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ lockHolder = None
    /\ tagFile = -1                                  \* File may not exist initially
    /\ gitHistory = {}                               \* Empty git history
    /\ sessionState = [s \in Sessions |-> "idle"]
    /\ assignedIter = [s \in Sessions |-> -1]
    /\ commitAttempts = [s \in Sessions |-> 0]
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
    /\ UNCHANGED <<tagFile, gitHistory, assignedIter, commitAttempts>>
    /\ step' = step + 1

\* Lock acquisition fails (another session holds it), session keeps trying
FailAcquireLock(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "idle"
    /\ ~LockAvailable                                \* LOCK_NB would block
    /\ sessionState' = [sessionState EXCEPT ![s] = "acquiring"]
    /\ UNCHANGED <<lockHolder, tagFile, gitHistory, assignedIter, commitAttempts>>
    /\ step' = step + 1

\* Session in acquiring state gets the lock (lock holder released)
RetryAcquireLock(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "acquiring"
    /\ LockAvailable
    /\ lockHolder' = s
    /\ sessionState' = [sessionState EXCEPT ![s] = "holding"]
    /\ UNCHANGED <<tagFile, gitHistory, assignedIter, commitAttempts>>
    /\ step' = step + 1

\* Session times out waiting for lock (models 30s timeout)
TimeoutAcquiring(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "acquiring"
    /\ sessionState' = [sessionState EXCEPT ![s] = "failed"]
    /\ UNCHANGED <<lockHolder, tagFile, gitHistory, assignedIter, commitAttempts>>
    /\ step' = step + 1

\* Session reads file and git, computes next iteration, writes file, releases lock
\* This is atomic because we hold the fcntl lock
\* After this action, session enters "committing" state (lock released, commit pending)
ComputeAndRelease(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "holding"
    /\ lockHolder = s                                \* Verify we hold lock
    /\ NextIteration <= MaxIteration                 \* Within bounds
    /\ LET nextIter == NextIteration
       IN /\ assignedIter' = [assignedIter EXCEPT ![s] = nextIter]
          /\ tagFile' = nextIter                     \* Write to tag file
          /\ lockHolder' = None                       \* Release fcntl lock
          /\ sessionState' = [sessionState EXCEPT ![s] = "committing"]
    /\ UNCHANGED <<gitHistory, commitAttempts>>
    /\ step' = step + 1

\* Session commits to git successfully (iteration becomes part of authoritative history)
\* This happens AFTER releasing the iteration lock (separate operation)
CommitToGitSuccess(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "committing"
    /\ assignedIter[s] /= -1
    /\ assignedIter[s] \notin gitHistory             \* Not already in history
    /\ gitHistory' = gitHistory \cup {assignedIter[s]}
    /\ sessionState' = [sessionState EXCEPT ![s] = "done"]
    /\ UNCHANGED <<lockHolder, tagFile, assignedIter, commitAttempts>>
    /\ step' = step + 1

\* Session commit fails (pre-commit hook, network error, etc.)
\* Session stays in "committing" state and can retry
CommitToGitFail(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "committing"
    /\ assignedIter[s] /= -1
    /\ CanRetryCommit(s)                             \* Still have retries left
    /\ commitAttempts' = [commitAttempts EXCEPT ![s] = @ + 1]
    /\ UNCHANGED <<lockHolder, tagFile, gitHistory, sessionState, assignedIter>>
    /\ step' = step + 1

\* Session exhausts commit retries and fails permanently
\* CRITICAL: This is where gaps occur!
\* The iteration was written to tagFile but never committed to git.
\* Another session will get tagFile+1, leaving a gap in git history.
CommitExhausted(s) ==
    /\ step < MaxSteps
    /\ sessionState[s] = "committing"
    /\ ~CanRetryCommit(s)                            \* No more retries
    /\ sessionState' = [sessionState EXCEPT ![s] = "failed"]
    /\ UNCHANGED <<lockHolder, tagFile, gitHistory, assignedIter, commitAttempts>>
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
    \/ \E s \in Sessions : CommitToGitSuccess(s)
    \/ \E s \in Sessions : CommitToGitFail(s)
    \/ \E s \in Sessions : CommitExhausted(s)
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

\* INVARIANT 5: Consistent Assignments
\* Sessions with assigned iterations must be in post-holding states.
\* Note: failed can be reached with or without assignment (timeout vs commit exhausted)
AssignmentConsistency ==
    \A s \in Sessions :
        assignedIter[s] /= -1 =>
            sessionState[s] \in {"committing", "done", "failed"}

\* INVARIANT 6: Git Monotonicity
\* All iterations in git history are unique (set property guarantees this)
\* The real check is that no duplicate can be committed
NoDuplicateCommits ==
    \A s \in Sessions :
        (assignedIter[s] /= -1 /\ assignedIter[s] \in gitHistory)
            => sessionState[s] = "done"  \* Only committed if done

\* INVARIANT 7: Gap Detection (commit failure scenario)
\* If tagFile = N, then all iterations 1..N should be either:
\*   - In git history, OR
\*   - Assigned to some live session (committing or done)
\* If this invariant is VIOLATED, we have a gap in iteration numbers.
\* NOTE: This invariant WILL BE VIOLATED when commit failures occur!
\* That's the point - it detects the gap bug.
GapDetection ==
    tagFile >= 1 =>
        \A i \in 1..tagFile :
            \/ i \in gitHistory                      \* Either in git
            \/ \E s \in Sessions :                    \* Or some non-failed session has it
                /\ assignedIter[s] = i
                /\ sessionState[s] /= "failed"

\* Combined safety invariant (excludes GapDetection - it's expected to fail)
Safety ==
    /\ LockMutex
    /\ UniqueIterations
    /\ HolderConsistency
    /\ ValidAssignments
    /\ AssignmentConsistency

-----------------------------------------------------------------------------
(* Liveness Properties - PROPERTIES (require fairness) *)

\* PROPERTY 1: Progress
\* Every idle session eventually reaches a terminal state
EventualTermination ==
    \A s \in Sessions :
        sessionState[s] = "idle" ~> SessionTerminated(s)

\* PROPERTY 2: Lock Progress
\* If lock is available and session is acquiring, it eventually gets it
LockProgress ==
    \A s \in Sessions :
        (sessionState[s] = "acquiring" /\ LockAvailable) ~>
            (sessionState[s] = "holding" \/ sessionState[s] = "failed")

\* PROPERTY 3: Commit Progress
\* A committing session eventually succeeds or fails
CommitProgress ==
    \A s \in Sessions :
        sessionState[s] = "committing" ~>
            (sessionState[s] = "done" \/ sessionState[s] = "failed")

-----------------------------------------------------------------------------
(* Fairness *)

Fairness ==
    /\ \A s \in Sessions : WF_vars(TryAcquireLock(s))
    /\ \A s \in Sessions : WF_vars(RetryAcquireLock(s))
    /\ \A s \in Sessions : WF_vars(ComputeAndRelease(s))
    /\ \A s \in Sessions : WF_vars(CommitToGitSuccess(s))
    /\ \A s \in Sessions : WF_vars(CommitExhausted(s))

FairSpec == Spec /\ Fairness

=============================================================================
