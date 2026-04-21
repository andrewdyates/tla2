---- MODULE RecursiveFactorial ----
\* RECURSIVE operator: factorial function.
\* Exercises RECURSIVE keyword and self-referential operator definitions.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals

VARIABLE f

RECURSIVE Fact(_)

Fact(n) ==
  IF n <= 1
  THEN 1
  ELSE n * Fact(n - 1)

Init == f = Fact(6)
Next == UNCHANGED f

FactOK == f = 720
SmallFact == Fact(0) = 1 /\ Fact(1) = 1
MedFact == Fact(4) = 24
====
