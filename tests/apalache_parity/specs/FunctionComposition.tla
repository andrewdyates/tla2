---- MODULE FunctionComposition ----
\* Function composition: nested function application, function sets.
\* Exercises [S -> T] function sets and function-valued functions.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals, FiniteSets

VARIABLE f

S == {1, 2}
T == {10, 20}

Init == f \in [S -> T]

Next ==
  \/ \E g \in [S -> T] : f' = g
  \/ UNCHANGED f

DomainOK == DOMAIN f = S
RangeOK == \A x \in S : f[x] \in T
FuncSetSize == Cardinality([S -> T]) = 4
FuncEq == [x \in S |-> 10] = [x \in S |-> 10]
FuncNeq == [x \in S |-> 10] # [x \in S |-> 20]
====
