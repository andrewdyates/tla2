---- MODULE LetInParametric ----
\* LET-IN with parametric (non-nullary) local operators.
\* Exercises LET op(x) == ... IN and nested LET bindings.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals

VARIABLE n

Init == n = 0
Next == IF n < 5 THEN n' = n + 1 ELSE UNCHANGED n

\* Parametric LET operator
DoubleInc(x) ==
  LET Inc(v) == v + 1
  IN Inc(Inc(x))

\* Nested LET with shadowing
NestedLet(x) ==
  LET a == x + 1
  IN LET b == a * 2
     IN b + a

\* LET with higher-order pattern: operator taking operator-like arg
ApplyTwice(base) ==
  LET Step(v) == v + base
  IN Step(Step(0))

DoubleOK == DoubleInc(3) = 5
NestedOK == NestedLet(2) = 9  \* a=3, b=6, 6+3=9
ApplyOK == ApplyTwice(7) = 14
InRange == n \in 0..5
====
