---------------------------- MODULE TestRecursiveFn ----------------------------
(* Test recursive function evaluation over a config-overridden domain.
   This isolates the SafeAt pattern from VoteProof. *)
EXTENDS Integers

CONSTANTS Value, Actor, Quorum

\* Defined operator, overridden by config to {0, 1, 2}
Ballot == Nat

VARIABLE votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]
DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

\* Recursive SafeAt (same structure as VoteProof)
SafeAt(b, v) ==
  LET SA[bb \in Ballot] ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
  IN  SA[b]

VoteFor(self, b, v) ==
  /\ maxBal[self] \leq b
  /\ DidNotVoteIn(self, b)
  /\ \A p \in Actor \ {self} :
        \A w \in Value : VotedFor(p, b, w) => (w = v)
  /\ SafeAt(b, v)
  /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]

IncreaseMaxBal(self, b) ==
  /\ b > maxBal[self]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED votes

Init == /\ votes = [a \in Actor |-> {}]
        /\ maxBal = [a \in Actor |-> -1]

Next == \E self \in Actor, b \in Ballot :
          \/ IncreaseMaxBal(self, b)
          \/ \E v \in Value : VoteFor(self, b, v)

\* Two different actors cannot vote for different values at the same ballot
Consistent == \A a1, a2 \in Actor, b \in Ballot, v1, v2 \in Value :
    VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Spec == Init /\ [][Next]_<<votes, maxBal>>
=============================================================================
