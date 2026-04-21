---- MODULE QuantifiedLetGuard ----
\* Minimal reproduction for #277 - LET depends on quantified variable
\*
\* Pattern: \E p \in Processes : LET x == var[p] + 1 IN Guard(x) /\ ...
\*
\* This tests LOCAL variable dependency tracking (works correctly).
\* The actual bug (#277) requires INSTANCE context - see Disruptor spec.
\*
\* TLC: Finds 64 distinct states
\* TLA2: Finds 64 distinct states (PASS - local deps tracked correctly)

EXTENDS Integers

CONSTANTS Processes

VARIABLES cursor, pc

ASSUME Processes = {"p1", "p2", "p3"}  \* 3 processes

Init ==
    /\ cursor = [p \in Processes |-> 0]
    /\ pc = [p \in Processes |-> "ready"]

\* The buggy pattern: LET depends on quantified 'proc'
Advance(proc) ==
    LET
        next == cursor[proc] + 1  \* 'next' depends on 'proc'
    IN
        /\ pc[proc] = "ready"
        /\ next <= 3               \* Guard uses LET-bound 'next'
        /\ cursor' = [cursor EXCEPT ![proc] = next]
        /\ pc' = pc

\* Control action to create branching
Ready(proc) ==
    /\ pc[proc] = "ready"
    /\ cursor[proc] < 3
    /\ pc' = [pc EXCEPT ![proc] = "ready"]
    /\ UNCHANGED cursor

Next == \E p \in Processes : Advance(p) \/ Ready(p)

Spec == Init /\ [][Next]_<<cursor, pc>>

StateConstraint == \A p \in Processes : cursor[p] <= 3

\* Sanity invariant - should never be violated
CursorBound == \A p \in Processes : cursor[p] <= 3

====
