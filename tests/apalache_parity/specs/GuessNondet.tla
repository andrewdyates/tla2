---- MODULE GuessNondet ----
\* Apalache Guess operator: nondeterministic choice from set.
\* In BFS mode, Guess picks first in TLC order.
\* Expected: model check passes.
EXTENDS Apalache, Naturals
VARIABLE chosen
Init == chosen = Guess({1, 2, 3})
Next == UNCHANGED chosen
InRange == chosen \in {1, 2, 3}
====
