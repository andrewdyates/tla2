---- MODULE LetGuardBug ----
\* Minimal reproduction for #277 - LET-bound variable in guard causes undercount
\*
\* Expected behavior: Both A and B should be enabled from state {x=1, y=0}
\*   - A: enabled because x >= (y+1) = 1 >= 1 = TRUE
\*   - B: always enabled
\*
\* Bug: A is never enabled because LET-bound 'z' gets stale cached value
\*
\* TLC: Finds 14 distinct states
\* TLA2 with bug: Should also find 14 states but may find fewer (linear chain)

EXTENDS Integers

VARIABLES x, y

Init ==
    /\ x = 1
    /\ y = 0

\* Action A uses LET-bound variable in guard
A ==
    LET z == y + 1
    IN /\ x >= z       \* Guard: should be TRUE when x=1, y=0 (z=1)
       /\ y' = z
       /\ x' = x

\* Action B is always enabled
B ==
    /\ x' = x + 1
    /\ y' = y

Next == A \/ B

StateConstraint == x < 5 /\ y < 5

Spec == Init /\ [][Next]_<<x, y>>
====
