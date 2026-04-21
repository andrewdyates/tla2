---- MODULE ItfTrace ----
\* ITF output: spec that produces a short deterministic trace.
\* Used to test ITF-compatible trace output.
\* Expected: model check passes, trace is well-formed.
EXTENDS Naturals
VARIABLE step

Init == step = 0
Next == step < 3 /\ step' = step + 1

TypeOK == step \in 0..3
Bounded == step <= 3
====
