---- MODULE TestShowsSafeAt ----
\* Minimal reproduction: tests eval of ShowsSafeAt in a specific state.
\* We set up the state directly in Init and check whether ShowsSafeAt is correct.

CONSTANT Acceptor, Value, Quorum, Ballot, A1, A2, A3, V1, V2

VARIABLES votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]
DidNotVoteAt(a, b) == \A v \in Value : ~VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  /\ \E c \in -1..(b-1) :
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

\* State where A1 has voted <<0,V1>>, maxBal[A1]=1, maxBal[A2]=1, maxBal[A3]=-1
Init ==
  /\ votes = (A1 :> {<<0, V1>>} @@ A2 :> {} @@ A3 :> {})
  /\ maxBal = (A1 :> 1 @@ A2 :> 1 @@ A3 :> -1)

\* No transitions - just check the initial state
Next == FALSE /\ UNCHANGED <<votes, maxBal>>

\* ShowsSafeAt should be FALSE for (Q, 1, V2) for ALL quorums
\* So this invariant should HOLD (no Q makes ShowsSafeAt true)
NoShowsSafeAtForV2 == ~(\E Q \in Quorum : ShowsSafeAt(Q, 1, V2))

====
