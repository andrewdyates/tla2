--------------------------- MODULE BmcRecordSpec ---------------------------
\* Record-valued state variables for BMC compound type testing.
\*
\* Models a simple "point" with x/y coordinates that step diagonally.
\* Tests: record construction, field access, EXCEPT on records.
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Dropbox. | Apache 2.0

EXTENDS Integers

VARIABLES point  \* Record: [x |-> Int, y |-> Int]

Init == point = [x |-> 0, y |-> 0]

Next == point' = [point EXCEPT !.x = point.x + 1, !.y = point.y + 1]

\* Invariant: both coordinates remain non-negative
NonNegative == point.x >= 0 /\ point.y >= 0

\* Invariant: coordinates always equal (diagonal movement)
CoordsEqual == point.x = point.y

\* Invariant that should fail at step 3: coordinates < 3
CoordsSmall == point.x < 3 /\ point.y < 3

=============================================================================
