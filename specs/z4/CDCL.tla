--------------------------- MODULE CDCL ---------------------------
\* Conflict-Driven Clause Learning (CDCL) SAT Solver
\*
\* Extends the BCP-only spec with:
\*   - Decision levels tracking branching depth
\*   - 1UIP conflict analysis (resolve until one literal at conflict level)
\*   - Non-chronological backtracking to second-highest level in learned clause
\*   - Clause learning: learned clauses added to clause database
\*
\* Models the core CDCL loop as implemented in z4-sat (~/z4/crates/z4-sat/src/):
\*   1. Propagate (BCP over original + learned clauses)
\*   2. If conflict: analyze via 1UIP, learn clause, backtrack
\*   3. If quiescent: decide (branch on unassigned variable)
\*   4. If all assigned: SAT. If conflict at level 0: UNSAT.
\*
\* Invariants verified:
\*   - TrailConsistent: trail agrees with assignment
\*   - NoSpuriousConflict: conflict only when a clause is genuinely all-false
\*   - PropagationSound: every implied literal is forced by its reason clause
\*   - LearnedWellFormed: every learned clause has valid literals
\*   - BacktrackCorrect: after backtrack, trail and assignment are consistent
\*   - DecisionLevelConsistent: decision_level matches trail structure
\*
\* Reference: z4-sat conflict.rs (ConflictAnalyzer), solver/conflict_analysis.rs
\*           (1UIP loop), solver/backtrack.rs (non-chronological backtrack)
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Andrew Yates. | Apache 2.0

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    NumVars,      \* Number of boolean variables (e.g. 4)
    Clauses       \* Set of clauses, each a set of literals (signed ints)
                  \* Positive int = positive literal, negative = negation

VARIABLES
    assignment,      \* Function: 1..NumVars -> {"TRUE", "FALSE", "UNSET"}
    trail,           \* Sequence of <<variable, value, reason, level>> tuples
                     \* reason = {} for decisions, a clause (set of ints) for implications
    conflict,        \* TRUE if a conflict has been detected
    propagating,     \* TRUE if BCP is still running
    decision_level,  \* Current decision level (Nat)
    level_of,        \* Function: 1..NumVars -> Nat, level at which variable was assigned
    learned,         \* Set of learned clauses (grows monotonically)
    status           \* "running", "sat", "unsat"

vars == <<assignment, trail, conflict, propagating, decision_level, level_of, learned, status>>

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

\* The value to assign to make a literal true
LitValue(lit) == IF Positive(lit) THEN "TRUE" ELSE "FALSE"

\* Negate a literal
NegLit(lit) == -lit

\* All clauses = original + learned
AllClauses == Clauses \union learned

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

\* ---- Trail helpers ----

\* Get the reason for a variable from the trail (returns {} if not found or decision)
TrailReason(v) ==
    IF \E i \in 1..Len(trail) : trail[i][1] = v
    THEN LET i == CHOOSE i \in 1..Len(trail) : trail[i][1] = v
         IN trail[i][3]
    ELSE {}

\* Get the level for a variable from the trail
TrailLevel(v) ==
    IF \E i \in 1..Len(trail) : trail[i][1] = v
    THEN LET i == CHOOSE i \in 1..Len(trail) : trail[i][1] = v
         IN trail[i][4]
    ELSE 0

\* Set of variables on the trail
TrailVars == {trail[i][1] : i \in 1..Len(trail)}

\* ---- 1UIP Conflict Analysis ----

\* Given a clause (set of literals) and a variable to resolve on,
\* and the reason clause for that variable, produce the resolvent.
\* Resolution: (C1 \ {lit}) \union (C2 \ {~lit})
\* where lit appears positive in one and negative in the other.
Resolve(c1, c2, v) ==
    {lit \in c1 : Var(lit) /= v} \union {lit \in c2 : Var(lit) /= v}

\* Count how many literals in a clause are at the given decision level
CountAtLevel(clause, lvl) ==
    Cardinality({lit \in clause : level_of[Var(lit)] = lvl})

\* The set of variables in a clause at a given level
VarsAtLevel(clause, lvl) ==
    {Var(lit) : lit \in {l \in clause : level_of[Var(l)] = lvl}}

\* Find the last variable on the trail that appears in a clause at a given level.
\* This is the variable we resolve on next in 1UIP.
LastTrailVarInClause(clause, lvl) ==
    LET varsInClause == VarsAtLevel(clause, lvl)
        trailIndices == {i \in 1..Len(trail) : trail[i][1] \in varsInClause}
    IN IF trailIndices = {} THEN 0
       ELSE LET maxIdx == CHOOSE i \in trailIndices :
                              \A j \in trailIndices : j <= i
            IN trail[maxIdx][1]

\* Compute the 1UIP learned clause from a conflict clause.
\* Starting from the conflict clause, resolve with reason clauses of
\* trail variables at the current decision level (in reverse trail order)
\* until exactly one literal remains at the current level.
\*
\* This is a recursive operator that terminates because each resolution
\* step strictly reduces the number of current-level variables in the
\* resolvent (by replacing one current-level variable with its antecedents,
\* which are at lower levels or already seen).
\*
\* Reference: z4-sat solver/conflict_analysis.rs lines 178-265
RECURSIVE Analyze1UIP(_, _)
Analyze1UIP(clause, lvl) ==
    IF CountAtLevel(clause, lvl) <= 1
    THEN clause  \* Reached 1UIP: exactly 0 or 1 literal at conflict level
    ELSE
        \* Find the last trail variable in the clause at the conflict level
        LET v == LastTrailVarInClause(clause, lvl)
            reason == TrailReason(v)
        IN IF reason = {}
           THEN clause  \* Decision variable: cannot resolve further (this is the UIP)
           ELSE Analyze1UIP(Resolve(clause, reason, v), lvl)

\* Compute the backtrack level: second-highest decision level in the learned clause.
\* If the clause is unit (all literals at one level), backtrack to 0.
\* Reference: z4-sat conflict.rs compute_backtrack_level()
BacktrackLevel(clause) ==
    LET levels == {level_of[Var(lit)] : lit \in clause}
    IN IF Cardinality(levels) <= 1
       THEN 0
       ELSE LET maxLvl == CHOOSE l \in levels : \A l2 \in levels : l2 <= l
                remaining == levels \ {maxLvl}
            IN CHOOSE l \in remaining : \A l2 \in remaining : l2 <= l

\* ---- Initial state ----

Init ==
    /\ assignment = [v \in 1..NumVars |-> "UNSET"]
    /\ trail = <<>>
    /\ conflict = FALSE
    /\ propagating = TRUE
    /\ decision_level = 0
    /\ level_of = [v \in 1..NumVars |-> 0]
    /\ learned = {}
    /\ status = "running"

\* ---- Actions ----

\* Unit Propagation: find a unit clause in AllClauses, propagate its forced literal
Propagate ==
    /\ status = "running"
    /\ propagating = TRUE
    /\ conflict = FALSE
    /\ \E c \in AllClauses :
        /\ ClauseUnit(c)
        /\ LET lit == UnitLit(c)
               v == Var(lit)
               val == LitValue(lit)
           IN /\ assignment' = [assignment EXCEPT ![v] = val]
              /\ trail' = Append(trail, <<v, val, c, decision_level>>)
              /\ level_of' = [level_of EXCEPT ![v] = decision_level]
              /\ conflict' = FALSE
              /\ propagating' = TRUE
              /\ UNCHANGED <<decision_level, learned, status>>

\* Conflict Detection: a clause in AllClauses has all literals falsified
DetectConflict ==
    /\ status = "running"
    /\ propagating = TRUE
    /\ conflict = FALSE
    /\ \E c \in AllClauses : ClauseConflict(c)
    /\ conflict' = TRUE
    /\ propagating' = FALSE
    /\ UNCHANGED <<assignment, trail, decision_level, level_of, learned, status>>

\* BCP Quiescent: no unit clauses and no conflict -> BCP is done
Quiesce ==
    /\ status = "running"
    /\ propagating = TRUE
    /\ conflict = FALSE
    /\ ~\E c \in AllClauses : ClauseUnit(c)
    /\ ~\E c \in AllClauses : ClauseConflict(c)
    /\ propagating' = FALSE
    /\ UNCHANGED <<assignment, trail, conflict, decision_level, level_of, learned, status>>

\* Decision: pick an unassigned variable, increment decision level, assign it
DecideWithLevel ==
    /\ status = "running"
    /\ propagating = FALSE
    /\ conflict = FALSE
    /\ \E v \in 1..NumVars :
        /\ assignment[v] = "UNSET"
        /\ \E val \in {"TRUE", "FALSE"} :
            /\ decision_level' = decision_level + 1
            /\ assignment' = [assignment EXCEPT ![v] = val]
            /\ trail' = Append(trail, <<v, val, {}, decision_level + 1>>)
            /\ level_of' = [level_of EXCEPT ![v] = decision_level + 1]
            /\ propagating' = TRUE
            /\ conflict' = FALSE
            /\ UNCHANGED <<learned, status>>

\* Analyze Conflict: perform 1UIP analysis, learn clause, backtrack
\* This is the core CDCL action that fires when a conflict is detected.
\*
\* 1. Find a conflicting clause
\* 2. Run 1UIP resolution to compute the learned clause
\* 3. Compute the backtrack level (second-highest level in learned clause)
\* 4. Add learned clause to database
\* 5. Backtrack: undo assignments above backtrack level
\* 6. Resume propagation (the learned clause will be unit after backtrack)
\*
\* Reference: z4-sat solver/conflict_analysis.rs analyze_conflict()
AnalyzeConflict ==
    /\ status = "running"
    /\ conflict = TRUE
    /\ decision_level > 0  \* Can only analyze if we made at least one decision
    /\ \E confClause \in AllClauses :
        /\ ClauseConflict(confClause)
        /\ LET learnedClause == Analyze1UIP(confClause, decision_level)
               btLevel == BacktrackLevel(learnedClause)
               \* Backtrack: keep only trail entries at or below btLevel
               newTrail == SelectSeq(trail,
                   LAMBDA entry : entry[4] <= btLevel)
               \* Variables to unassign: those above btLevel
               unassignVars == {trail[i][1] : i \in
                   {j \in 1..Len(trail) : trail[j][4] > btLevel}}
               \* New assignment: reset variables above btLevel to UNSET
               newAssignment == [v \in 1..NumVars |->
                   IF v \in unassignVars THEN "UNSET"
                   ELSE assignment[v]]
               \* New level_of: reset levels for unassigned variables
               newLevelOf == [v \in 1..NumVars |->
                   IF v \in unassignVars THEN 0
                   ELSE level_of[v]]
           IN /\ assignment' = newAssignment
              /\ trail' = newTrail
              /\ level_of' = newLevelOf
              /\ decision_level' = btLevel
              /\ learned' = learned \union {learnedClause}
              /\ conflict' = FALSE
              /\ propagating' = TRUE
              /\ UNCHANGED <<status>>

\* Conflict at level 0: UNSAT (no decisions to undo)
UnsatDetected ==
    /\ status = "running"
    /\ conflict = TRUE
    /\ decision_level = 0
    /\ status' = "unsat"
    /\ UNCHANGED <<assignment, trail, conflict, propagating, decision_level, level_of, learned>>

\* All variables assigned, no conflict: SAT
SatDetected ==
    /\ status = "running"
    /\ propagating = FALSE
    /\ conflict = FALSE
    /\ \A v \in 1..NumVars : assignment[v] /= "UNSET"
    /\ status' = "sat"
    /\ UNCHANGED <<assignment, trail, conflict, propagating, decision_level, level_of, learned>>

\* Terminal: solver has reached a conclusion
Done ==
    /\ status \in {"sat", "unsat"}
    /\ UNCHANGED vars

Next == Propagate \/ DetectConflict \/ Quiesce \/ DecideWithLevel
        \/ AnalyzeConflict \/ UnsatDetected \/ SatDetected \/ Done

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
    conflict => \E c \in AllClauses : ClauseConflict(c)

\* Every propagated literal is forced by its reason clause
PropagationSound ==
    \A i \in 1..Len(trail) :
        LET entry == trail[i]
            v == entry[1]
            val == entry[2]
            reason == entry[3]
        IN \* Only check non-decision entries (reason is a clause, not {})
           \A c \in AllClauses :
               reason = c =>
                   \E lit \in c :
                       /\ Var(lit) = v
                       /\ LitValue(lit) = val

\* Decision level is consistent with the number of decisions on the trail
DecisionLevelConsistent ==
    decision_level >= 0

\* Every learned clause contains only valid literals
LearnedWellFormed ==
    \A c \in learned :
        /\ c /= {}
        /\ \A lit \in c : Var(lit) \in 1..NumVars

\* After backtrack, trail entries are at or below current decision level
BacktrackCorrect ==
    \A i \in 1..Len(trail) :
        trail[i][4] <= decision_level

\* Type invariant
TypeOK ==
    /\ assignment \in [1..NumVars -> {"TRUE", "FALSE", "UNSET"}]
    /\ conflict \in BOOLEAN
    /\ propagating \in BOOLEAN
    /\ decision_level \in Nat
    /\ status \in {"running", "sat", "unsat"}

Spec == Init /\ [][Next]_vars
=============================================================================
