---- MODULE TokenRingBuggy ----
\* BUGGY version of the Token-Ring Mutual Exclusion Protocol.
\*
\* This version has a subtle bug: process 1 can enter the critical
\* section without holding the token. This violates mutual exclusion
\* and demonstrates BMC (Bounded Model Checking) finding the bug
\* symbolically — often before BFS reaches the violating state.
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

Init ==
  /\ pc = [i \in 1..N |-> Idle]
  /\ token = 1

Request(i) ==
  /\ pc[i] = Idle
  /\ pc' = [pc EXCEPT ![i] = Waiting]
  /\ UNCHANGED token

\* BUG: Process 1 can enter without the token!
\* The correct guard is: token = i
\* The buggy guard for process 1 is: TRUE (always enabled)
Enter(i) ==
  /\ pc[i] = Waiting
  /\ IF i = 1 THEN TRUE ELSE token = i
  /\ pc' = [pc EXCEPT ![i] = Critical]
  /\ UNCHANGED token

Exit(i) ==
  /\ pc[i] = Critical
  /\ pc' = [pc EXCEPT ![i] = Exiting]
  /\ UNCHANGED token

PassToken(i) ==
  /\ pc[i] = Exiting
  /\ token = i
  /\ token' = IF i = N THEN 1 ELSE i + 1
  /\ pc' = [pc EXCEPT ![i] = Idle]

Next ==
  \E i \in 1..N :
    \/ Request(i)
    \/ Enter(i)
    \/ Exit(i)
    \/ PassToken(i)

\* MUTUAL EXCLUSION: should be violated because of the bug above.
MutualExclusion ==
  \A i \in 1..N :
    \A j \in 1..N :
      (i # j) => ~(pc[i] = Critical /\ pc[j] = Critical)

====
