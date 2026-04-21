---- MODULE Mutex ----
\* N processes competing for a mutex. Classic mutual exclusion.
\* Demonstrates: model values, invariants, deadlock detection.

CONSTANT Procs     \* The set of processes

VARIABLE pc        \* pc[p] is the program counter of process p

Init == pc = [p \in Procs |-> "idle"]

Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "waiting"]

Enter(p) ==
  /\ pc[p] = "waiting"
  /\ \A q \in Procs : q # p => pc[q] # "critical"
  /\ pc' = [pc EXCEPT ![p] = "critical"]

Exit(p) ==
  /\ pc[p] = "critical"
  /\ pc' = [pc EXCEPT ![p] = "idle"]

Next == \E p \in Procs : Request(p) \/ Enter(p) \/ Exit(p)

\* Safety: at most one process in the critical section
MutualExclusion ==
  \A p, q \in Procs : (p # q) => ~(pc[p] = "critical" /\ pc[q] = "critical")

\* Type invariant
TypeOK == pc \in [Procs -> {"idle", "waiting", "critical"}]

====
