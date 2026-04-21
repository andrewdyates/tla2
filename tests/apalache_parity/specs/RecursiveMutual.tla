---- MODULE RecursiveMutual ----
\* Mutually recursive operators (Part of #3828).
\* Tests RECURSIVE with two mutually recursive definitions (even/odd).
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals

VARIABLE k

RECURSIVE IsEven(_)
RECURSIVE IsOdd(_)

IsEven(n) == IF n = 0 THEN TRUE ELSE IsOdd(n - 1)
IsOdd(n) == IF n = 0 THEN FALSE ELSE IsEven(n - 1)

Init == k \in 0..6
Next == IF k < 6 THEN k' = k + 1 ELSE UNCHANGED k

\* Invariants
EvenZero == IsEven(0) = TRUE
OddZero == IsOdd(0) = FALSE
EvenTwo == IsEven(2) = TRUE
OddThree == IsOdd(3) = TRUE
EvenFive == IsEven(5) = FALSE
OddFour == IsOdd(4) = FALSE
KBounded == k \in 0..6
====
