---- MODULE AssignOpCase ----
\* Apalache := operator inside CASE expressions (Part of #3828).
\* Tests := within CASE arms and CASE OTHER.
\* Expected: model check passes with all invariants holding.
EXTENDS Apalache, Naturals

VARIABLE phase

Init == phase := 0

Next ==
    CASE phase = 0 -> phase' := 1
      [] phase = 1 -> phase' := 2
      [] phase = 2 -> phase' := 3
      [] OTHER -> phase' := 0

InRange == phase \in 0..3
====
