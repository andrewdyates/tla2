--------------------------- MODULE BCP ---------------------------
\* Boolean Constraint Propagation (Unit Propagation) for SAT solving
\*
\* Models the BCP core of a CDCL SAT solver on a small instance.
\* This is the smallest verifiable unit of the self-verifying solver
\* bootstrap (Phase A, Step 1).
\*
\* The spec models:
\*   - A fixed clause database over N boolean variables
\*   - An assignment function (TRUE/FALSE/UNSET)
\*   - A propagation trail recording decisions and implications
\*   - Unit propagation: when a clause has exactly one unassigned literal
\*     and all others are falsified, force that literal
\*   - Conflict detection: when all literals in a clause are falsified
\*
\* Invariants verified:
\*   - TrailConsistent: trail agrees with assignment
\*   - NoSpuriousConflict: conflict only declared when genuinely all-false
\*   - PropagationSound: every implied literal is forced by its reason clause
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Andrew Yates. | Apache 2.0

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    NumVars,      \* Number of boolean variables (e.g. 3)
    Clauses       \* Set of clauses, each a set of literals (signed ints)
                  \* Positive int = positive literal, negative = negation
                  \* e.g. {1, -2, 3} means (x1 \/ ~x2 \/ x3)

VARIABLES
    assignment,   \* Function: 1..NumVars -> {"TRUE", "FALSE", "UNSET"}
    trail,        \* Sequence of <<variable, value, reason>> tuples
                  \* reason = a clause (the unit clause that forced it) or {} (decision)
    conflict,     \* TRUE if a conflict has been detected
    propagating   \* TRUE if BCP is still running (not yet quiescent)

vars == <<assignment, trail, conflict, propagating>>

\* ---- Helper operators ----

\* The variable of a literal
Var(lit) == IF lit > 0 THEN lit ELSE -lit

\* The sign/polarity of a literal: TRUE means positive
Positive(lit) == lit > 0

\* Is a literal satisfied by the current assignment?
LitTrue(lit) ==
    LET v == Var(lit)
    IN IF Positive(lit)
       THEN assignment[v] = "TRUE"
       ELSE assignment[v] = "FALSE"

\* Is a literal falsified by the current assignment?
LitFalse(lit) ==
    LET v == Var(lit)
    IN IF Positive(lit)
       THEN assignment[v] = "FALSE"
       ELSE assignment[v] = "TRUE"

\* Is a literal unassigned?
LitUnset(lit) == assignment[Var(lit)] = "UNSET"

\* Is a clause satisfied? (at least one literal is true)
ClauseSat(c) == \E lit \in c : LitTrue(lit)

\* Is a clause conflicting? (all literals are false)
ClauseConflict(c) == \A lit \in c : LitFalse(lit)

\* Is a clause unit? (exactly one unset literal, all others false)
ClauseUnit(c) ==
    /\ ~ClauseSat(c)
    /\ Cardinality({lit \in c : LitUnset(lit)}) = 1

\* Get the unset literal from a unit clause
UnitLit(c) ==
    CHOOSE lit \in c : LitUnset(lit)

\* The value to assign to make a literal true
LitValue(lit) == IF Positive(lit) THEN "TRUE" ELSE "FALSE"

\* ---- Initial state ----

Init ==
    /\ assignment = [v \in 1..NumVars |-> "UNSET"]
    /\ trail = <<>>
    /\ conflict = FALSE
    /\ propagating = TRUE

\* ---- Actions ----

\* Unit Propagation: find a unit clause, propagate its forced literal
Propagate ==
    /\ propagating = TRUE
    /\ conflict = FALSE
    /\ \E c \in Clauses :
        /\ ClauseUnit(c)
        /\ LET lit == UnitLit(c)
               v == Var(lit)
               val == LitValue(lit)
           IN /\ assignment' = [assignment EXCEPT ![v] = val]
              /\ trail' = Append(trail, <<v, val, c>>)
              /\ conflict' = FALSE
              /\ propagating' = TRUE

\* Conflict Detection: a clause has all literals falsified
DetectConflict ==
    /\ propagating = TRUE
    /\ conflict = FALSE
    /\ \E c \in Clauses : ClauseConflict(c)
    /\ conflict' = TRUE
    /\ propagating' = FALSE
    /\ UNCHANGED <<assignment, trail>>

\* BCP Quiescent: no unit clauses and no conflict -> BCP is done
Quiesce ==
    /\ propagating = TRUE
    /\ conflict = FALSE
    /\ ~\E c \in Clauses : ClauseUnit(c)
    /\ ~\E c \in Clauses : ClauseConflict(c)
    /\ propagating' = FALSE
    /\ UNCHANGED <<assignment, trail, conflict>>

\* Decision: pick an unassigned variable and assign it (models branching)
Decide ==
    /\ propagating = FALSE
    /\ conflict = FALSE
    /\ \E v \in 1..NumVars :
        /\ assignment[v] = "UNSET"
        /\ \E val \in {"TRUE", "FALSE"} :
            /\ assignment' = [assignment EXCEPT ![v] = val]
            /\ trail' = Append(trail, <<v, val, {}>>)
            /\ propagating' = TRUE
            /\ conflict' = FALSE

\* Terminal: all variables assigned and BCP quiescent, or conflict found
Done ==
    /\ \/ conflict = TRUE
       \/ /\ propagating = FALSE
          /\ \A v \in 1..NumVars : assignment[v] /= "UNSET"
    /\ UNCHANGED vars

Next == Propagate \/ DetectConflict \/ Quiesce \/ Decide \/ Done

\* ---- Invariants ----

\* The trail is consistent with the assignment
TrailConsistent ==
    \A i \in 1..Len(trail) :
        LET entry == trail[i]
            v == entry[1]
            val == entry[2]
        IN assignment[v] = val

\* Conflict is only declared when a clause is genuinely all-false
NoSpuriousConflict ==
    conflict => \E c \in Clauses : ClauseConflict(c)

\* Every propagated literal is forced by its reason clause
PropagationSound ==
    \A i \in 1..Len(trail) :
        LET entry == trail[i]
            v == entry[1]
            val == entry[2]
            reason == entry[3]
        IN \* Only check non-decision entries (reason is a clause, not {})
           \A c \in Clauses :
               reason = c =>
                   \E lit \in c :
                       /\ Var(lit) = v
                       /\ LitValue(lit) = val

\* Type invariant
TypeOK ==
    /\ assignment \in [1..NumVars -> {"TRUE", "FALSE", "UNSET"}]
    /\ conflict \in BOOLEAN
    /\ propagating \in BOOLEAN

Spec == Init /\ [][Next]_vars
=============================================================================
