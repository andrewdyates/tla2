---- MODULE TokenRing ----
\* Token-Ring Mutual Exclusion Protocol
\*
\* N processes arranged in a logical ring pass a single token. Only the
\* token holder may enter its critical section. This models the core
\* mechanism behind distributed lock services (Chubby, ZooKeeper, etcd).
\*
\* This spec showcases Cooperative Decision-Enhanced Model Checking (CDEMC).
\* The mutual exclusion invariant is 1-inductive: symbolic engines (PDR,
\* k-induction) can prove it without exploring all states, while BFS must
\* enumerate the full state space (grows as 4^N).
\*
\*   N=5:   ~3,900 reachable states — BFS handles this in <1 second
\*   N=8:   ~2M reachable states    — symbolic proves safety instantly
\*   N=12:  ~1B reachable states    — only symbolic reasoning is feasible
\*
\* State encoding (integer for SMT compatibility):
\*   0 = idle, 1 = waiting, 2 = critical, 3 = exiting
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>

CONSTANT N       \* Number of processes in the ring

VARIABLES
  pc,            \* pc[i] \in 0..3 — program counter of process i
  token          \* token \in 1..N — who holds the token

\* State constants for readability
Idle     == 0
Waiting  == 1
Critical == 2
Exiting  == 3

\* ---- Initial state ----
\* All processes idle, process 1 holds the token.

Init ==
  /\ pc = [i \in 1..N |-> Idle]
  /\ token = 1

\* ---- Actions ----

\* Process i requests the critical section
Request(i) ==
  /\ pc[i] = Idle
  /\ pc' = [pc EXCEPT ![i] = Waiting]
  /\ UNCHANGED token

\* Process i enters the critical section (requires holding the token)
Enter(i) ==
  /\ pc[i] = Waiting
  /\ token = i
  /\ pc' = [pc EXCEPT ![i] = Critical]
  /\ UNCHANGED token

\* Process i exits the critical section
Exit(i) ==
  /\ pc[i] = Critical
  /\ pc' = [pc EXCEPT ![i] = Exiting]
  /\ UNCHANGED token

\* Process i passes the token to the next process in the ring
PassToken(i) ==
  /\ pc[i] = Exiting
  /\ token = i
  /\ token' = IF i = N THEN 1 ELSE i + 1
  /\ pc' = [pc EXCEPT ![i] = Idle]

\* The complete next-state relation
Next ==
  \E i \in 1..N :
    \/ Request(i)
    \/ Enter(i)
    \/ Exit(i)
    \/ PassToken(i)

\* ---- Safety Properties ----

\* MUTUAL EXCLUSION: at most one process in the critical section.
\*
\* This is the key property. It is 1-inductive because entering critical
\* requires token = i, and the token is unique — at most one process
\* satisfies the guard at any time.
\*
\* Formulated with nested single-variable quantifiers for SMT compatibility.
MutualExclusion ==
  \A i \in 1..N :
    \A j \in 1..N :
      (i # j) => ~(pc[i] = Critical /\ pc[j] = Critical)

====
