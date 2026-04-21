--------------------------- MODULE MCBCP ---------------------------
\* Model checking wrapper for BCP with concrete clause instance
\*
\* 3 variables, 4 clauses:
\*   C1: (x1 \/ x2)          = {1, 2}
\*   C2: (~x1 \/ x3)         = {-1, 3}
\*   C3: (~x2 \/ ~x3)        = {-2, -3}
\*   C4: (x1 \/ ~x2 \/ x3)   = {1, -2, 3}
\*
\* This is satisfiable: x1=T, x2=F, x3=T (among others)

EXTENDS BCP

MCNumVars == 3

MCClauses == {{1, 2}, {-1, 3}, {-2, -3}, {1, -2, 3}}
=============================================================================
