---- MODULE RecursiveFibonacci ----
\* RECURSIVE operator: Fibonacci sequence with mutual recursion test.
\* Exercises RECURSIVE keyword with branching recursion (not just linear).
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals

VARIABLE n

RECURSIVE Fib(_)

Fib(k) ==
  IF k <= 0 THEN 0
  ELSE IF k = 1 THEN 1
  ELSE Fib(k - 1) + Fib(k - 2)

Init == n \in {0, 1, 2, 3, 4, 5}
Next == UNCHANGED n

FibValues ==
  /\ Fib(0) = 0
  /\ Fib(1) = 1
  /\ Fib(2) = 1
  /\ Fib(3) = 2
  /\ Fib(4) = 3
  /\ Fib(5) = 5

FibMonotone == \A i \in 2..5 : Fib(i) >= Fib(i - 1)
NInRange == n \in 0..5
====
