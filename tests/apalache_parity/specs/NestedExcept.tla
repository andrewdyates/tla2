---- MODULE NestedExcept ----
\* Nested EXCEPT: deep path updates on functions and records.
\* Exercises [f EXCEPT ![i].field = v] and multi-path EXCEPT.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals

VARIABLE table

Init == table = [i \in {1, 2} |-> [name |-> "init", val |-> i * 10]]

Next ==
  \/ table' = [table EXCEPT ![1].val = 99]
  \/ table' = [table EXCEPT ![1].name = "updated", ![2].val = 50]
  \/ UNCHANGED table

\* Invariants
DomainOK == DOMAIN table = {1, 2}
NameType == table[1].name \in {"init", "updated"}
Val1OK == table[1].val \in {10, 99}
Val2OK == table[2].val \in {20, 50}
RecordStructure == \A i \in DOMAIN table :
                     DOMAIN table[i] = {"name", "val"}
====
