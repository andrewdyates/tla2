--------------------------- MODULE MCCDCL ---------------------------
\* Model checking wrapper for CDCL with a 4-variable instance
\*
\* 4 variables, 8 clauses (UNSAT — requires clause learning):
\*
\* This is a minimal UNSAT instance where pure BCP+backtracking is insufficient
\* without learning. The clauses encode a constrained pigeonhole-like structure:
\*
\*   C1: (x1 \/ x2)           = {1, 2}
\*   C2: (x3 \/ x4)           = {3, 4}
\*   C3: (~x1 \/ ~x3)         = {-1, -3}
\*   C4: (~x1 \/ ~x4)         = {-1, -4}
\*   C5: (~x2 \/ ~x3)         = {-2, -3}
\*   C6: (~x2 \/ ~x4)         = {-2, -4}
\*   C7: (x1 \/ x3)           = {1, 3}
\*   C8: (x2 \/ x4)           = {2, 4}
\*
\* UNSAT proof sketch:
\*   From C1: x1 or x2. From C2: x3 or x4.
\*   From C3,C4: if x1 then ~x3 and ~x4, contradicting C2.
\*   From C5,C6: if x2 then ~x3 and ~x4, contradicting C2.
\*   So neither x1 nor x2 can be true, contradicting C1.
\*
\* The solver will learn clauses like (~x1) and (~x2) through conflict analysis.

EXTENDS CDCL

MCNumVars == 4

MCClauses == {
    {1, 2},         \* x1 \/ x2
    {3, 4},         \* x3 \/ x4
    {-1, -3},       \* ~x1 \/ ~x3
    {-1, -4},       \* ~x1 \/ ~x4
    {-2, -3},       \* ~x2 \/ ~x3
    {-2, -4},       \* ~x2 \/ ~x4
    {1, 3},         \* x1 \/ x3
    {2, 4}          \* x2 \/ x4
}
=============================================================================
