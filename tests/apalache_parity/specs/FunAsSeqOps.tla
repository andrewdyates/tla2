---- MODULE FunAsSeqOps ----
\* FunAsSeq with Append, Len, and sequence operations (Part of #3828).
\* Tests converting a function to a sequence and using sequence operators.
\* Expected: model check passes with all invariants holding.
EXTENDS Apalache, Naturals, Sequences

VARIABLE seq

\* Create a function and convert to sequence
f == [i \in {1, 2, 3} |-> i * 10]
asSeq == FunAsSeq(f, 3, 3)

Init == seq = asSeq

Next ==
    \/ /\ Len(seq) < 5
       /\ seq' = Append(seq, 40)
    \/ /\ Len(seq) > 1
       /\ seq' = Tail(seq)
    \/ UNCHANGED seq

\* Verify FunAsSeq produces correct sequence
AsSeqLenOK == Len(asSeq) = 3
AsSeqElem1 == asSeq[1] = 10
AsSeqElem2 == asSeq[2] = 20
AsSeqElem3 == asSeq[3] = 30
HeadOK == Head(asSeq) = 10
SubSeqOK == SubSeq(asSeq, 1, 2) = <<10, 20>>
====
