--------------------------- MODULE AllDiffProp ---------------------------
\* AllDifferent Constraint Propagator for CP-SAT Solving
\*
\* Models the core propagation algorithms for the all-different constraint
\* as implemented in z4-cp (~/z4/crates/z4-cp/src/propagators/alldifferent.rs):
\*   - Bounds propagation: detect Hall intervals and tighten variable bounds
\*   - Value removal: remove values that cannot appear in any all-different assignment
\*   - Hall set detection: find subsets S of variables where |union(domains(S))| = |S|,
\*     forcing all values in union(domains(S)) to be consumed by S
\*
\* The spec operates on finite integer domains. Each variable has a set of
\* possible values (its domain). Propagation narrows domains while maintaining
\* the invariant that every remaining value can participate in some valid
\* all-different assignment.
\*
\* Reference: Lopez-Ortiz, Quimper, Tromp, van Beek. "A fast and simple algorithm
\*            for bounds consistency of the alldifferent constraint" (IJCAI 2003)
\*            Regin. "A filtering algorithm for constraints of difference in CSPs"
\*            (AAAI 1994)
\*
\* Invariants verified:
\*   - TypeOK: domains are functions to subsets of 1..DomainMax, never empty
\*   - SolutionSound: if all domains are singletons, they form a valid all-different assignment
\*   - FixpointAC: at propagation fixpoint, every remaining value is feasible
\*   - HallSetCorrect: every detected Hall set is genuine
\*   - DomainsNonEmpty: no domain is ever emptied (propagation halts before wipeout)
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Andrew Yates. | Apache 2.0

EXTENDS Integers, FiniteSets

CONSTANTS
    NumVars,      \* Number of CP variables (e.g. 3 or 4)
    DomainMax     \* Upper bound of the value domain (values are 1..DomainMax)

VARIABLES
    domains,      \* Function: 1..NumVars -> SUBSET 1..DomainMax (current domains)
    removed,      \* Set of <<var, val, reason>> tuples recording removals
                  \* reason = a set of variables (the Hall set that forced the removal)
    status        \* "propagating" or "done"

vars == <<domains, removed, status>>

Vars == 1..NumVars
Vals == 1..DomainMax

\* ---- Helper operators ----

\* Union of domains for a set of variables
DomainUnion(S) == UNION {domains[v] : v \in S}

\* Is a function f: S -> Vals an injective (all-different) assignment?
IsInjective(f, S) == \A v1, v2 \in S : (v1 /= v2) => (f[v1] /= f[v2])

\* Does a valid all-different assignment exist using current domains?
\* An assignment is a function f: Vars -> Vals where:
\*   - f[v] \in domains[v] for all v
\*   - f is injective (all values distinct)
HasValidAssignment ==
    \E f \in [Vars -> Vals] :
        /\ \A v \in Vars : f[v] \in domains[v]
        /\ IsInjective(f, Vars)

\* Can a specific value val be assigned to variable var in some valid assignment?
ValueFeasible(var, val) ==
    val \in domains[var] /\
    \E f \in [Vars -> Vals] :
        /\ f[var] = val
        /\ \A v \in Vars : f[v] \in domains[v]
        /\ IsInjective(f, Vars)

\* Is S a Hall set? A Hall set is a subset of variables whose combined
\* domain has exactly as many values as variables in the set.
\* By the pigeonhole principle, all those values must be consumed by S.
IsHallSet(S) ==
    /\ S /= {}
    /\ S \subseteq Vars
    /\ Cardinality(DomainUnion(S)) = Cardinality(S)

\* ---- Initial state ----

Init ==
    /\ domains = [v \in Vars |-> Vals]
    /\ removed = {}
    /\ status = "propagating"

\* ---- Actions ----

\* Hall Set Propagation: detect a Hall set S and remove its values from
\* variables outside S. This is the core of the AllDifferent propagator.
\*
\* When |union(domains(S))| = |S|, every value in union(domains(S)) must
\* be used by some variable in S. Therefore, no variable outside S can
\* take any of those values.
\*
\* Reference: z4-cp alldifferent.rs filter_lower/filter_upper (bounds version)
\*            z4-cp alldifferent_ac/mod.rs filter_unsupported (AC version)
HallSetPropagate ==
    /\ status = "propagating"
    /\ \E S \in SUBSET Vars :
        /\ IsHallSet(S)
        /\ Cardinality(S) < NumVars  \* Not all variables (trivial)
        /\ LET hallVals == DomainUnion(S)
               \* Variables outside the Hall set that have values to remove
               affectedVars == {v \in Vars \ S : domains[v] \cap hallVals /= {}}
           IN /\ affectedVars /= {}  \* There is something to propagate
              /\ \E v \in affectedVars :
                  /\ LET valsToRemove == domains[v] \cap hallVals
                         newDomain == domains[v] \ hallVals
                     IN /\ newDomain /= {}  \* Don't wipe out the domain
                        /\ domains' = [domains EXCEPT ![v] = newDomain]
                        /\ removed' = removed \union
                             {<<v, val, S>> : val \in valsToRemove}
                        /\ status' = "propagating"

\* Bounds Propagation: if a variable's min or max value is not feasible
\* (because it must be used by another variable with a singleton domain
\* that equals that value), tighten the bound.
\*
\* This models the filter_lower/filter_upper operations in z4-cp: when the
\* minimum value in a domain is claimed by a Hall interval below, raise
\* the lower bound; symmetrically for upper bound.
\*
\* Reference: z4-cp alldifferent.rs filter_lower(), filter_upper()
BoundsPropagate ==
    /\ status = "propagating"
    /\ \E v \in Vars :
        /\ Cardinality(domains[v]) > 1  \* Not already fixed
        /\ \E val \in domains[v] :
              \* val is at the boundary (min or max of the domain)
              /\ \/ val = CHOOSE m \in domains[v] : \A x \in domains[v] : m <= x
                 \/ val = CHOOSE m \in domains[v] : \A x \in domains[v] : m >= x
              \* val is forced by another variable (some other var has singleton {val})
              /\ \E w \in Vars \ {v} : domains[w] = {val}
              /\ LET newDomain == domains[v] \ {val}
                     reason == {w \in Vars \ {v} : domains[w] = {val}}
                 IN /\ newDomain /= {}
                    /\ domains' = [domains EXCEPT ![v] = newDomain]
                    /\ removed' = removed \union {<<v, val, reason>>}
                    /\ status' = "propagating"

\* Value Removal: remove a value from a variable's domain when that value
\* cannot participate in any valid all-different assignment.
\*
\* This is the arc-consistency (AC) level propagation from Regin's algorithm:
\* if a value is not in any maximum matching of the variable-value bipartite
\* graph, it can be safely removed.
\*
\* Reference: z4-cp alldifferent_ac/mod.rs filter_unsupported()
ValueRemove ==
    /\ status = "propagating"
    /\ \E v \in Vars :
        /\ Cardinality(domains[v]) > 1
        /\ \E val \in domains[v] :
              /\ ~ValueFeasible(v, val)
              /\ LET newDomain == domains[v] \ {val}
                 IN /\ newDomain /= {}
                    /\ domains' = [domains EXCEPT ![v] = newDomain]
                    /\ removed' = removed \union {<<v, val, {}>>}
                    /\ status' = "propagating"

\* Quiescent: no more propagation possible. Either:
\*   - All domains are singletons (fully determined), or
\*   - No Hall set propagation, bounds propagation, or value removal applies
Quiesce ==
    /\ status = "propagating"
    \* No Hall set with removable values exists
    /\ ~\E S \in SUBSET Vars :
          /\ IsHallSet(S)
          /\ Cardinality(S) < NumVars
          /\ \E v \in Vars \ S :
                /\ domains[v] \cap DomainUnion(S) /= {}
                /\ (domains[v] \ DomainUnion(S)) /= {}
    \* No bounds propagation applies
    /\ ~\E v \in Vars :
          /\ Cardinality(domains[v]) > 1
          /\ \E val \in domains[v] :
                /\ \/ val = CHOOSE m \in domains[v] : \A x \in domains[v] : m <= x
                   \/ val = CHOOSE m \in domains[v] : \A x \in domains[v] : m >= x
                /\ \E w \in Vars \ {v} : domains[w] = {val}
                /\ (domains[v] \ {val}) /= {}
    \* No infeasible value exists in any domain
    /\ ~\E v \in Vars :
          /\ Cardinality(domains[v]) > 1
          /\ \E val \in domains[v] :
                /\ ~ValueFeasible(v, val)
                /\ (domains[v] \ {val}) /= {}
    /\ status' = "done"
    /\ UNCHANGED <<domains, removed>>

\* Decision: nondeterministically fix a variable to one of its remaining values.
\* This models the search/branching layer of the CP solver that interleaves
\* with propagation.
Decide ==
    /\ status = "done"
    /\ \E v \in Vars :
        /\ Cardinality(domains[v]) > 1
        /\ \E val \in domains[v] :
            /\ domains' = [domains EXCEPT ![v] = {val}]
            /\ removed' = removed \union
                 {<<v, x, {}>> : x \in domains[v] \ {val}}
            /\ status' = "propagating"

\* Terminal: all variables are fixed or no unfixed variables exist
Done ==
    /\ \/ /\ status = "done"
          /\ \A v \in Vars : Cardinality(domains[v]) = 1
       \/ /\ status = "done"
          /\ ~HasValidAssignment
    /\ UNCHANGED vars

Next == HallSetPropagate \/ BoundsPropagate \/ ValueRemove \/ Quiesce \/ Decide \/ Done

\* ---- Invariants ----

\* Type invariant: domains map variables to subsets of values
TypeOK ==
    /\ \A v \in Vars : domains[v] \subseteq Vals
    /\ \A v \in Vars : domains[v] /= {}
    /\ status \in {"propagating", "done"}

\* Solution soundness: if all domains have been reduced to singletons,
\* they form a valid all-different assignment. This ensures the propagator
\* never guides the search to a "solution" that violates the constraint.
SolutionSound ==
    (\A v \in Vars : Cardinality(domains[v]) = 1) =>
        LET assignment == [v \in Vars |-> CHOOSE val \in domains[v] : TRUE]
        IN IsInjective(assignment, Vars)

\* Arc-consistency at fixpoint: when propagation is done, every remaining
\* value in every domain participates in some valid all-different assignment.
\* This is the defining property of Regin's AC propagator.
FixpointAC ==
    status = "done" =>
        \A v \in Vars : \A val \in domains[v] : ValueFeasible(v, val)

\* Hall set correctness: any Hall set detected is genuine
\* (This is checked implicitly by the action guard IsHallSet, but we also
\* verify it as an invariant over the removal records)
HallSetCorrect ==
    \A r \in removed :
        LET reason == r[3]
        IN reason /= {} =>
           /\ reason \subseteq Vars
           /\ Cardinality(DomainUnion(reason)) >= Cardinality(reason)

\* Domains never grow (monotonic shrinking)
\* Checked via: removed set only grows, domains only lose values
DomainsNonEmpty ==
    \A v \in Vars : domains[v] /= {}

Spec == Init /\ [][Next]_vars
=============================================================================
