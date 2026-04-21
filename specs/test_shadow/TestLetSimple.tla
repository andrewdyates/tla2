---------------------------- MODULE TestLetSimple ----------------------------
(* Test LET with simple non-FuncDef expression.
   SafeAt uses LET x == TRUE IN x *)
EXTENDS Integers

CONSTANTS Value, Actor, Quorum

Ballot == Nat

VARIABLE votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]
DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

\* Simple LET, no FuncDef
SafeAt(b, v) ==
  LET x == TRUE
  IN  x

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

Consistent == \A a1, a2 \in Actor, b \in Ballot, v1, v2 \in Value :
    VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Spec == Init /\ [][Next]_<<votes, maxBal>>
=============================================================================
