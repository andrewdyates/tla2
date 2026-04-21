---- MODULE DieHard ----
\* The Die Hard 3 water jugs puzzle.
\* Two jugs: 3-gallon and 5-gallon. Measure exactly 4 gallons.
\* Demonstrates: a spec with an invariant VIOLATION (the puzzle is solvable).

EXTENDS Naturals

VARIABLES small, big   \* Water levels in the 3-gallon and 5-gallon jugs

Init == small = 0 /\ big = 0

FillSmall  == small' = 3 /\ big' = big
FillBig    == big' = 5   /\ small' = small
EmptySmall == small' = 0 /\ big' = big
EmptyBig   == big' = 0   /\ small' = small

SmallToBig == IF small + big <= 5
              THEN /\ big' = small + big
                   /\ small' = 0
              ELSE /\ big' = 5
                   /\ small' = small + big - 5

BigToSmall == IF small + big <= 3
              THEN /\ small' = small + big
                   /\ big' = 0
              ELSE /\ small' = 3
                   /\ big' = small + big - 3

Next == FillSmall \/ FillBig \/ EmptySmall \/ EmptyBig
     \/ SmallToBig \/ BigToSmall

\* This invariant says "we never get 4 gallons in the big jug."
\* TLA2 will find a counterexample trace showing how to solve the puzzle!
NotSolved == big # 4

TypeOK == small \in 0..3 /\ big \in 0..5

====
