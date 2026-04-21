---- MODULE LambdaHigherOrder ----
\* LAMBDA expressions in various higher-order contexts (Part of #3828).
\* Tests LAMBDA with ApaFoldSet, ApaFoldSeqLeft, MkSeq, and nested lambdas.
\* Expected: model check passes with all invariants holding.
EXTENDS Apalache, Naturals, Sequences

VARIABLE n

Init == n = 0
Next == IF n < 1 THEN n' = n + 1 ELSE UNCHANGED n

\* LAMBDA in ApaFoldSet
SumWithLambda == ApaFoldSet(LAMBDA a, b: a + b, 0, {1, 2, 3, 4, 5})
SumOK == SumWithLambda = 15

\* LAMBDA in ApaFoldSeqLeft
ProductWithLambda == ApaFoldSeqLeft(LAMBDA acc, x: acc * x, 1, <<2, 3, 4>>)
ProductOK == ProductWithLambda = 24

\* LAMBDA in MkSeq
SquareSeq == MkSeq(4, LAMBDA i: i * i)
SquareOK == SquareSeq = <<1, 4, 9, 16>>

\* LAMBDA in Repeat
RepeatWithLambda == Repeat(LAMBDA x, i: x + i * 10, 3, 0)
\* i=1: 0 + 10 = 10, i=2: 10 + 20 = 30, i=3: 30 + 30 = 60
RepeatOK == RepeatWithLambda = 60

\* LAMBDA with conditional
ConditionalLambda == ApaFoldSet(
    LAMBDA a, b: IF b > 3 THEN a + b ELSE a,
    0,
    {1, 2, 3, 4, 5}
)
ConditionalOK == ConditionalLambda = 9  \* 4 + 5
====
