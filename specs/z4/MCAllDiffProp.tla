--------------------------- MODULE MCAllDiffProp ---------------------------
\* Model checking wrapper for AllDiffProp with a small concrete instance.
\*
\* 3 variables, domain 1..4:
\*   Variables: {1, 2, 3}
\*   Values: {1, 2, 3, 4}
\*
\* This is a satisfiable instance with multiple valid all-different assignments:
\*   (1,2,3), (1,2,4), (1,3,2), (1,3,4), (1,4,2), (1,4,3),
\*   (2,1,3), (2,1,4), (2,3,1), (2,3,4), (2,4,1), (2,4,3),
\*   (3,1,2), (3,1,4), (3,2,1), (3,2,4), (3,4,1), (3,4,2),
\*   (4,1,2), (4,1,3), (4,2,1), (4,2,3), (4,3,1), (4,3,2)
\*
\* The propagator will explore various domain narrowings, branching decisions,
\* and verify that invariants hold throughout.

EXTENDS AllDiffProp

MCNumVars == 3

MCDomainMax == 4
=============================================================================
