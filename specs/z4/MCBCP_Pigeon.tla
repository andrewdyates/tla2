--------------------------- MODULE MCBCP_Pigeon ---------------------------
\* Pigeonhole principle: 3 pigeons into 2 holes (UNSAT)
\*
\* Variables: p_ij means "pigeon i goes to hole j"
\*   p11=1, p12=2, p21=3, p22=4, p31=5, p32=6
\*
\* At-least-one constraints (each pigeon goes somewhere):
\*   p11 \/ p12 = {1, 2}
\*   p21 \/ p22 = {3, 4}
\*   p31 \/ p32 = {5, 6}
\*
\* At-most-one constraints (no two pigeons in same hole):
\*   ~p11 \/ ~p21 = {-1, -3}
\*   ~p11 \/ ~p31 = {-1, -5}
\*   ~p21 \/ ~p31 = {-3, -5}
\*   ~p12 \/ ~p22 = {-2, -4}
\*   ~p12 \/ ~p32 = {-2, -6}
\*   ~p22 \/ ~p32 = {-4, -6}
\*
\* This is UNSAT: BCP + decisions will always reach conflict.

EXTENDS BCP

MCNumVars == 6

MCClauses == {
    {1, 2},         \* pigeon 1 -> hole 1 or hole 2
    {3, 4},         \* pigeon 2 -> hole 1 or hole 2
    {5, 6},         \* pigeon 3 -> hole 1 or hole 2
    {-1, -3},       \* not both pigeon 1 and 2 in hole 1
    {-1, -5},       \* not both pigeon 1 and 3 in hole 1
    {-3, -5},       \* not both pigeon 2 and 3 in hole 1
    {-2, -4},       \* not both pigeon 1 and 2 in hole 2
    {-2, -6},       \* not both pigeon 1 and 3 in hole 2
    {-4, -6}        \* not both pigeon 2 and 3 in hole 2
}
=============================================================================
