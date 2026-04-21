---- MODULE SeqNatTest ----
\* Test: is <<>> in Seq(Nat)?
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

Init == x = <<>>

Next == UNCHANGED x

\* The empty sequence should be in Seq(Nat)
EmptyInSeqNat == <<>> \in Seq(Nat)

\* Also test non-empty
NonEmptyInSeqNat == <<1, 2, 3>> \in Seq(Nat)

\* Test as function
FuncInSeq == [r \in {"r1"} |-> <<>>] \in [{"r1"} -> Seq(Nat)]

====
