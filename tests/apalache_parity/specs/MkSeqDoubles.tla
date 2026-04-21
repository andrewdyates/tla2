---- MODULE MkSeqDoubles ----
\* Apalache MkSeq operator: builds sequence from operator.
\* Expected: model check passes, sequence invariant holds.
EXTENDS Apalache, Naturals, Sequences
VARIABLE seq
Double(i) == i * 2
Init == seq = MkSeq(4, Double)
Next == UNCHANGED seq
Correct == /\ Len(seq) = 4
           /\ seq[1] = 2 /\ seq[2] = 4
           /\ seq[3] = 6 /\ seq[4] = 8
====
