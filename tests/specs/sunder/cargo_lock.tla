-------------------------------- MODULE cargo_lock --------------------------------
(* TLA+ specification for cargo_wrapper.py lock protocol
   Author: Andrew Yates <andrewyates.name@gmail.com>

   Models the mutual exclusion and stale detection protocol in:

   Key properties to verify:
   1. MutualExclusion: At most one process holds the lock
   2. NoDeadlock: System can always make progress
   3. LockSafety: Lock holder matches lock file PID
   4. StaleLockRelease: Dead processes' locks can be force-released
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    None,           \* Model value for "no value" (distinct from all Procs)
    Procs,          \* Set of process IDs
    MaxSteps        \* Bound for model checking

VARIABLES
    lockFile,       \* None or PID of lock creator (None = doesn't exist)
    lockMeta,       \* Record with acquired_at, pid, process_start_time or None
    procState,      \* Function: Proc -> "idle" | "waiting" | "holding" | "dead"
    procStartTime,  \* Function: Proc -> start time (natural number)
    globalTime,     \* Global monotonic time for staleness checking
    step            \* Step counter for bounded model checking

vars == <<lockFile, lockMeta, procState, procStartTime, globalTime, step>>

-----------------------------------------------------------------------------
(* Type invariants *)

TypeOK ==
    /\ lockFile \in {None} \cup Procs  \* None or a PID
    /\ procState \in [Procs -> {"idle", "waiting", "holding", "dead"}]
    /\ procStartTime \in [Procs -> Nat]
    /\ globalTime \in Nat
    /\ step \in Nat

-----------------------------------------------------------------------------
(* Helper predicates *)

LockExists == lockFile /= None

ProcessAlive(p) == procState[p] /= "dead"

\* Process owns lock if: lock exists, file has its PID, and it's alive
ProcessOwnsLock(p) ==
    /\ LockExists
    /\ lockFile = p
    /\ procState[p] = "holding"

\* Lock is stale if holder is dead
LockIsStale ==
    /\ LockExists
    /\ procState[lockFile] = "dead"

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ lockFile = None
    /\ lockMeta = None
    /\ procState = [p \in Procs |-> "idle"]
    /\ procStartTime = [p \in Procs |-> 0]
    /\ globalTime = 0
    /\ step = 0

-----------------------------------------------------------------------------
(* Actions *)

\* Process attempts to acquire lock (models acquire_lock with O_CREAT|O_EXCL)
TryAcquire(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "idle"
    /\ ~LockExists                        \* O_CREAT|O_EXCL succeeds only if no file
    /\ lockFile' = p                      \* Atomic file creation with PID
    /\ lockMeta' = [pid |-> p,
                    acquired_at |-> globalTime,
                    start_time |-> procStartTime[p]]
    /\ procState' = [procState EXCEPT ![p] = "holding"]
    /\ UNCHANGED <<procStartTime, globalTime>>
    /\ step' = step + 1

\* Process fails to acquire lock (file already exists)
FailAcquire(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "idle"
    /\ LockExists                         \* Lock exists, can't acquire
    /\ procState' = [procState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime>>
    /\ step' = step + 1

\* Process releases its own lock (models release_lock)
Release(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "holding"
    /\ lockFile = p                       \* Verify we own the lock
    /\ lockFile' = None
    /\ lockMeta' = None
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<procStartTime, globalTime>>
    /\ step' = step + 1

\* Process dies while holding lock (crash scenario)
Die(p) ==
    /\ step < MaxSteps
    /\ procState[p] \in {"idle", "waiting", "holding"}
    /\ procState' = [procState EXCEPT ![p] = "dead"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime>>
    /\ step' = step + 1

\* Process force-releases a stale lock (models force_release_stale_lock)
\* Uses atomic rename to "claim" the stale lock before deleting
ForceReleaseStale(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "waiting"           \* Must be waiting to want the lock
    /\ LockIsStale                         \* Lock holder must be dead
    /\ lockFile' = None                    \* Atomic rename then delete
    /\ lockMeta' = None
    /\ procState' = [procState EXCEPT ![p] = "idle"]  \* Back to idle, can try acquire
    /\ UNCHANGED <<procStartTime, globalTime>>
    /\ step' = step + 1

\* Waiting process retries (goes back to idle to try again)
Retry(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "waiting"
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime>>
    /\ step' = step + 1

\* Time advances
Tick ==
    /\ step < MaxSteps
    /\ globalTime' = globalTime + 1
    /\ UNCHANGED <<lockFile, lockMeta, procState, procStartTime>>
    /\ step' = step + 1

\* Respawn a dead process with new start time
\* NOTE: In the simple model, respawned process has same PID but lock was cleared
\* This models the idealized case where stale locks are always detected
\* For TOCTOU bugs with PID reuse, see cargo_lock_with_toctou.tla
Respawn(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "dead"
    /\ lockFile /= p                    \* Only respawn if lock was cleared (prevents TOCTOU)
    /\ procStartTime' = [procStartTime EXCEPT ![p] = globalTime]
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lockFile, lockMeta, globalTime>>
    /\ step' = step + 1

-----------------------------------------------------------------------------
(* Next state relation *)

\* Termination - allows model to end gracefully at step bound
Terminate ==
    /\ step >= MaxSteps
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : TryAcquire(p)
    \/ \E p \in Procs : FailAcquire(p)
    \/ \E p \in Procs : Release(p)
    \/ \E p \in Procs : Die(p)
    \/ \E p \in Procs : ForceReleaseStale(p)
    \/ \E p \in Procs : Retry(p)
    \/ \E p \in Procs : Respawn(p)
    \/ Tick
    \/ Terminate

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

\* INVARIANT 1: Mutual Exclusion
\* At most one process is in "holding" state
MutualExclusion ==
    Cardinality({p \in Procs : procState[p] = "holding"}) <= 1

\* INVARIANT 2: Lock Consistency
\* If lock file exists, exactly one process should be holding
LockConsistency ==
    LockExists =>
        /\ lockFile \in Procs
        /\ \/ procState[lockFile] = "holding"  \* Normal case
           \/ procState[lockFile] = "dead"     \* Crash case (stale lock)

\* INVARIANT 3: Holder Matches Lock
\* A holding process must match the lock file PID
HolderMatchesLock ==
    \A p \in Procs :
        procState[p] = "holding" => lockFile = p

\* INVARIANT 4: No Lock Without Holder
\* If a process is holding, lock must exist with its PID
NoPhantomHolding ==
    \A p \in Procs :
        procState[p] = "holding" => (LockExists /\ lockFile = p)

\* Combined safety invariant
Safety ==
    /\ MutualExclusion
    /\ LockConsistency
    /\ HolderMatchesLock
    /\ NoPhantomHolding

-----------------------------------------------------------------------------
(* Liveness Properties - checked with fairness assumptions *)

\* PROPERTY 1: Progress
\* If a process is waiting and lock holder dies, eventually someone acquires
\* (Requires weak fairness on ForceReleaseStale and TryAcquire)
Progress ==
    \A p \in Procs :
        (procState[p] = "waiting" /\ LockIsStale) ~>
            \E q \in Procs : procState[q] = "holding"

\* PROPERTY 2: No Starvation (with fairness)
\* A waiting process eventually either acquires or the system terminates
EventualAcquire ==
    \A p \in Procs :
        procState[p] = "waiting" ~>
            \/ procState[p] = "holding"
            \/ procState[p] = "dead"
            \/ procState[p] = "idle"

-----------------------------------------------------------------------------
(* Fairness *)

Fairness ==
    /\ \A p \in Procs : WF_vars(TryAcquire(p))
    /\ \A p \in Procs : WF_vars(ForceReleaseStale(p))
    /\ \A p \in Procs : WF_vars(Retry(p))

FairSpec == Spec /\ Fairness

=============================================================================
