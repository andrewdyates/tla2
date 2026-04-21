---- MODULE SequenceOperations ----
\* Sequence operations: Head, Tail, Len, Append, SubSeq.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals, Sequences
VARIABLE seq

Init == seq = <<10, 20, 30>>
Next == IF Len(seq) < 4 THEN seq' = Append(seq, 40)
        ELSE UNCHANGED seq

LenOK == Len(seq) \in {3, 4}
HeadOK == Head(seq) = 10
TailOK == Head(Tail(seq)) = 20
AppendOK == Len(seq) <= 4
SubSeqOK == SubSeq(seq, 1, 2) = <<10, 20>>
====
