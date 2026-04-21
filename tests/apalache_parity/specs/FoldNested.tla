---- MODULE FoldNested ----
\* Nested fold operations: fold-of-fold and fold with record accumulator (Part of #3828).
\* Tests ApaFoldSet and ApaFoldSeqLeft in nested and complex contexts.
\* Expected: model check passes with all invariants holding.
EXTENDS Apalache, Naturals, Sequences, FiniteSets

VARIABLE result

\* Nested fold: fold over a set where each element is itself a fold result
Add(a, b) == a + b
Mul(a, b) == a * b

\* Sum of products: for sets {2,3} and {4,5}, compute product of each, then sum
SetA == {2, 3}
SetB == {4, 5}

ProdA == ApaFoldSet(Mul, 1, SetA)  \* 2*3 = 6
ProdB == ApaFoldSet(Mul, 1, SetB)  \* 4*5 = 20
SumOfProducts == ApaFoldSet(Add, 0, {ProdA, ProdB})  \* 6+20 = 26

\* Fold with record accumulator
MergeCount(acc, x) ==
    [sum |-> acc.sum + x, count |-> acc.count + 1]

Stats == ApaFoldSet(MergeCount, [sum |-> 0, count |-> 0], {10, 20, 30})

\* Fold over a sequence built by MkSeq
Triple(i) == i * 3
TripleSeq == MkSeq(4, Triple)  \* <<3, 6, 9, 12>>
SeqSum == ApaFoldSeqLeft(Add, 0, TripleSeq)  \* 3+6+9+12 = 30

Init == result = SumOfProducts

Next == UNCHANGED result

SumOfProductsOK == SumOfProducts = 26
StatsOK == Stats.sum = 60 /\ Stats.count = 3
SeqSumOK == SeqSum = 30
TripleSeqOK == Len(TripleSeq) = 4
====
