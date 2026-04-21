---- MODULE ConstantsConfig ----
\* CONSTANTS with config file parameter overrides.
\* Exercises CONSTANT declarations with values assigned via .cfg.
\* Expected: model check passes with CONSTANT values from config.
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

VARIABLE pc

Init == pc = [p \in Procs |-> "idle"]

Next == \E p \in Procs :
          \/ /\ pc[p] = "idle"
             /\ pc' = [pc EXCEPT ![p] = "running"]
          \/ /\ pc[p] = "running"
             /\ pc' = [pc EXCEPT ![p] = "done"]
          \/ /\ pc[p] = "done"
             /\ UNCHANGED pc

TypeOK == \A p \in Procs : pc[p] \in {"idle", "running", "done"}
ProcCount == Cardinality(Procs) = N
DomainOK == DOMAIN pc = Procs
====
