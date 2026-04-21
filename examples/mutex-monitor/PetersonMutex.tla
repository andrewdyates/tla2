---- MODULE PetersonMutex ----
\* Peterson's mutual exclusion algorithm for two processes.
\*
\* This is a classic concurrent algorithm that provides mutual exclusion
\* using only shared memory (no hardware atomics). It demonstrates:
\*
\*   - Non-deterministic interleaving of process actions
\*   - Safety invariants (mutual exclusion)
\*   - Type invariants (state space boundedness)
\*
\* Peterson's algorithm uses two shared variables:
\*   - flag[i]: process i wants to enter the critical section
\*   - turn:    tie-breaker — "the other process can go first"
\*
\* Protocol for process i (other = 1-i):
\*   1. Set flag[i] = TRUE      (announce interest)
\*   2. Set turn = other         (defer to the other process)
\*   3. Wait until flag[other] = FALSE \/ turn = i
\*   4. Enter critical section
\*   5. Set flag[i] = FALSE      (release)

VARIABLE
    pc,     \* pc[i] \in {"idle", "set_flag", "set_turn", "wait", "critical"}
    flag,   \* flag[i] \in {TRUE, FALSE}
    turn    \* turn \in {0, 1}

Procs == {0, 1}

Other(p) == 1 - p

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ flag = [p \in Procs |-> FALSE]
    /\ turn = 0

\* Process p announces interest in the critical section.
SetFlag(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "set_flag"]
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ UNCHANGED turn

\* Process p sets turn to the other process (deference).
SetTurn(p) ==
    /\ pc[p] = "set_flag"
    /\ pc' = [pc EXCEPT ![p] = "set_turn"]
    /\ turn' = Other(p)
    /\ UNCHANGED flag

\* Process p checks the wait condition.
\* It can enter critical section when either:
\*   - The other process is not interested (flag[other] = FALSE), OR
\*   - It is this process's turn (turn = p)
CheckWait(p) ==
    /\ pc[p] = "set_turn"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<flag, turn>>

Enter(p) ==
    /\ pc[p] = "wait"
    /\ \/ flag[Other(p)] = FALSE
       \/ turn = p
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<flag, turn>>

\* Process p exits the critical section.
Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED turn

Next == \E p \in Procs : SetFlag(p) \/ SetTurn(p) \/ CheckWait(p) \/ Enter(p) \/ Exit(p)

\* -----------------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------------

\* Type invariant: all variables are in expected domains.
TypeOK ==
    /\ pc \in [Procs -> {"idle", "set_flag", "set_turn", "wait", "critical"}]
    /\ flag \in [Procs -> {TRUE, FALSE}]
    /\ turn \in {0, 1}

\* Safety: at most one process is in the critical section.
MutualExclusion ==
    ~ (pc[0] = "critical" /\ pc[1] = "critical")

\* Auxiliary: at least one process can always make progress (no global deadlock).
\* This is checked by the model checker's deadlock detection, not as an invariant.

Spec == Init /\ [][Next]_<<pc, flag, turn>>

====
