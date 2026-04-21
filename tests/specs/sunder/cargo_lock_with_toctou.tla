-------------------------------- MODULE cargo_lock_with_toctou --------------------------------
(* TLA+ specification for cargo_wrapper.py lock protocol
   with TOCTOU (Time-of-Check Time-of-Use) race conditions

   Author: Andrew Yates <andrewyates.name@gmail.com>

   Based on cargo_lock.tla, extended to model:
   - PID reuse within the 2-second tolerance window
   - TOCTOU race between reading lock file and checking process status
   - Race between is_lock_stale check and force_release_stale_lock

   Models the mutual exclusion and stale detection protocol in:

   Key properties to verify:
   1. MutualExclusion: At most one process holds the lock
   2. NoDeadlock: System can always make progress
   3. LockSafety: Lock holder matches lock file PID
   4. StaleLockRelease: Dead processes' locks can be force-released
   5. TOCTOU Safety: PID reuse within tolerance doesn't break safety
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    None,               \* Model value for "no value" (distinct from all Procs)
    Procs,              \* Set of process IDs
    MaxSteps,           \* Bound for model checking
    StartTimeTolerance  \* 2-second tolerance for PID reuse detection

VARIABLES
    lockFile,       \* None or PID of lock creator (None = doesn't exist)
    lockMeta,       \* Record with acquired_at, pid, process_start_time or None
    procState,      \* Function: Proc -> "idle" | "waiting" | "checking" | "releasing" | "holding" | "dead"
    procStartTime,  \* Function: Proc -> start time (natural number)
    globalTime,     \* Global monotonic time for staleness checking
    step,           \* Step counter for bounded model checking
    \* TOCTOU state - track what was read during check
    readLockPid,    \* What PID did checking process read from lock file?
    readStartTime   \* What start time did checking process read from metadata?

vars == <<lockFile, lockMeta, procState, procStartTime, globalTime, step, readLockPid, readStartTime>>

-----------------------------------------------------------------------------
(* Type invariants *)

TypeOK ==
    /\ lockFile \in {None} \cup Procs
    /\ \/ lockMeta = None
       \/ /\ lockMeta.pid \in Procs
          /\ lockMeta.acquired_at \in Nat
          /\ lockMeta.start_time \in Nat
    /\ procState \in [Procs -> {"idle", "waiting", "checking", "releasing", "holding", "dead"}]
    /\ procStartTime \in [Procs -> Nat]
    /\ globalTime \in Nat
    /\ step \in Nat
    /\ readLockPid \in [Procs -> {None} \cup Procs]
    /\ readStartTime \in [Procs -> {None} \cup Nat]

-----------------------------------------------------------------------------
(* Helper predicates *)

LockExists == lockFile /= None

ProcessAlive(p) == procState[p] /= "dead"

\* Process owns lock if: lock exists, file has its PID, and it's alive
ProcessOwnsLock(p) ==
    /\ LockExists
    /\ lockFile = p
    /\ procState[p] = "holding"

\* Lock is actually stale if holder is dead
LockIsActuallyStale ==
    /\ LockExists
    /\ procState[lockFile] = "dead"

\* PID reuse within tolerance - NEW process started within 2s of when lock was acquired
\* This is the condition where is_lock_stale might return FALSE incorrectly
PidReusedWithinTolerance(pid) ==
    /\ lockMeta /= None
    /\ lockMeta.pid = pid
    /\ procState[pid] /= "dead"           \* New process is alive
    /\ lockMeta.start_time /= None
    \* New process started within tolerance of recorded start time
    /\ LET currentStart == procStartTime[pid]
           recordedStart == lockMeta.start_time
       IN currentStart - recordedStart <= StartTimeTolerance

\* TOCTOU vulnerability: Check based on stale read
\* Process thinks lock is stale but it was reused
ToctouVulnerable(checker) ==
    /\ readLockPid[checker] /= None
    /\ LET pid == readLockPid[checker] IN
        /\ procState[pid] /= "dead"        \* Original owner died and PID reused
        /\ pid /= checker                   \* Not self
        /\ PidReusedWithinTolerance(pid)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ lockFile = None
    /\ lockMeta = None
    /\ procState = [p \in Procs |-> "idle"]
    /\ procStartTime = [p \in Procs |-> 0]
    /\ globalTime = 0
    /\ step = 0
    /\ readLockPid = [p \in Procs |-> None]
    /\ readStartTime = [p \in Procs |-> None]

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
    /\ UNCHANGED <<procStartTime, globalTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* Process fails to acquire lock (file already exists)
FailAcquire(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "idle"
    /\ LockExists                         \* Lock exists, can't acquire
    /\ procState' = [procState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* TOCTOU Step 1: Read lock file PID (start checking for staleness)
\* This captures the first read in the TOCTOU window
BeginStaleCheck(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "waiting"
    /\ LockExists
    /\ readLockPid' = [readLockPid EXCEPT ![p] = lockFile]
    /\ readStartTime' = [readStartTime EXCEPT ![p] =
        IF lockMeta /= None THEN lockMeta.start_time ELSE None]
    /\ procState' = [procState EXCEPT ![p] = "checking"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime>>
    /\ step' = step + 1

\* TOCTOU Step 2a: Finish stale check - lock is stale, enter releasing state
\* Between BeginStaleCheck and this, the lock holder could have died and PID reused!
FinishStaleCheckPositive(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "checking"
    /\ readLockPid[p] /= None
    /\ LET pid == readLockPid[p] IN
        \* Check if lock APPEARS stale based on read values
        \/ procState[pid] = "dead"        \* Process is dead
        \/ (readStartTime[p] /= None
            /\ procStartTime[pid] /= None
            /\ procStartTime[pid] - readStartTime[p] > StartTimeTolerance)
    /\ procState' = [procState EXCEPT ![p] = "releasing"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* TOCTOU Step 2b: Finish stale check - lock is NOT stale, go back to waiting
FinishStaleCheckNegative(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "checking"
    /\ readLockPid[p] /= None
    /\ LET pid == readLockPid[p] IN
        /\ procState[pid] /= "dead"       \* Process appears alive
        /\ (readStartTime[p] = None
            \/ procStartTime[pid] = None
            \/ procStartTime[pid] - readStartTime[p] <= StartTimeTolerance)
    /\ procState' = [procState EXCEPT ![p] = "waiting"]
    /\ readLockPid' = [readLockPid EXCEPT ![p] = None]
    /\ readStartTime' = [readStartTime EXCEPT ![p] = None]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime>>
    /\ step' = step + 1

\* Process force-releases a stale lock (models force_release_stale_lock)
\* Uses atomic rename to "claim" the stale lock before deleting
\* CRITICAL: This is where TOCTOU can cause incorrect release!
ForceReleaseStale(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "releasing"
    /\ LockExists
    /\ lockFile' = None                    \* Atomic rename then delete
    /\ lockMeta' = None
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ readLockPid' = [readLockPid EXCEPT ![p] = None]
    /\ readStartTime' = [readStartTime EXCEPT ![p] = None]
    /\ UNCHANGED <<procStartTime, globalTime>>
    /\ step' = step + 1

\* Process releases its own lock (models release_lock)
Release(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "holding"
    /\ lockFile = p                       \* Verify we own the lock
    /\ lockFile' = None
    /\ lockMeta' = None
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<procStartTime, globalTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* Process dies while in any active state (crash scenario)
Die(p) ==
    /\ step < MaxSteps
    /\ procState[p] \in {"idle", "waiting", "checking", "releasing", "holding"}
    /\ procState' = [procState EXCEPT ![p] = "dead"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* Waiting process retries (goes back to idle to try again)
Retry(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "waiting"
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lockFile, lockMeta, procStartTime, globalTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* Time advances
Tick ==
    /\ step < MaxSteps
    /\ globalTime' = globalTime + 1
    /\ UNCHANGED <<lockFile, lockMeta, procState, procStartTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* Respawn a dead process with new start time
\* CRITICAL: If new start time is within tolerance of old, PID reuse goes undetected!
Respawn(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "dead"
    /\ procStartTime' = [procStartTime EXCEPT ![p] = globalTime]
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lockFile, lockMeta, globalTime, readLockPid, readStartTime>>
    /\ step' = step + 1

\* Respawn a dead process with start time within tolerance (models fast PID reuse)
\* This is the problematic case!
RespawnFast(p) ==
    /\ step < MaxSteps
    /\ procState[p] = "dead"
    /\ lockMeta /= None
    /\ lockMeta.pid = p                   \* This PID was the lock holder
    \* New process starts within tolerance of recorded start time
    /\ procStartTime' = [procStartTime EXCEPT ![p] = lockMeta.start_time + 1]
    /\ procState' = [procState EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lockFile, lockMeta, globalTime, readLockPid, readStartTime>>
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
    \/ \E p \in Procs : BeginStaleCheck(p)
    \/ \E p \in Procs : FinishStaleCheckPositive(p)
    \/ \E p \in Procs : FinishStaleCheckNegative(p)
    \/ \E p \in Procs : ForceReleaseStale(p)
    \/ \E p \in Procs : Release(p)
    \/ \E p \in Procs : Die(p)
    \/ \E p \in Procs : Retry(p)
    \/ \E p \in Procs : Respawn(p)
    \/ \E p \in Procs : RespawnFast(p)
    \/ Tick
    \/ Terminate

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

\* INVARIANT 1: Mutual Exclusion
\* At most one process is in "holding" state
MutualExclusion ==
    Cardinality({p \in Procs : procState[p] = "holding"}) <= 1

\* INVARIANT 2: Lock Consistency (Type Safety Only)
\* If lock file exists, the PID in lockFile must be in Procs.
\* NOTE: In the TOCTOU model, we allow lockFile to point to any process state
\* because PID reuse can leave stale data. The interesting invariant is
\* NoIncorrectForceRelease which checks for actual TOCTOU bugs.
LockConsistency ==
    LockExists => lockFile \in Procs

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

\* INVARIANT 5: No Incorrect Force Release (TOCTOU check)
\* A process in "releasing" state should only be releasing an actually stale lock
\* This WILL BE VIOLATED when TOCTOU race occurs with PID reuse!
NoIncorrectForceRelease ==
    \A p \in Procs :
        procState[p] = "releasing" =>
            LockIsActuallyStale

\* Combined safety invariant (excludes NoIncorrectForceRelease - it demonstrates the bug)
Safety ==
    /\ MutualExclusion
    /\ LockConsistency
    /\ HolderMatchesLock
    /\ NoPhantomHolding

-----------------------------------------------------------------------------
(* Liveness Properties - checked with fairness assumptions *)

\* PROPERTY 1: Progress
\* If a process is waiting and lock holder dies, eventually someone acquires
Progress ==
    \A p \in Procs :
        (procState[p] = "waiting" /\ LockIsActuallyStale) ~>
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
