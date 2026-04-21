---- MODULE ExceptMultiField ----
\* Multiple EXCEPT field updates on records and nested structures (Part of #3828).
\* Tests [r EXCEPT !.f1 = v1, !.f2 = v2] and deep nested EXCEPT.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals

VARIABLE db

Init == db = [
    user |-> [name |-> "alice", age |-> 25, active |-> TRUE],
    count |-> 0
]

Next ==
    \/ /\ db.user.age < 27
       /\ db' = [db EXCEPT !.user.age = db.user.age + 1,
                            !.count = db.count + 1]
    \/ /\ db.count < 2
       /\ db' = [db EXCEPT !.user.name = "bob",
                            !.user.active = FALSE,
                            !.count = db.count + 1]
    \/ UNCHANGED db

NameOK == db.user.name \in {"alice", "bob"}
AgeOK == db.user.age >= 25 /\ db.user.age <= 27
CountOK == db.count >= 0 /\ db.count <= 4
ActiveOK == db.user.active \in BOOLEAN
StructureOK == DOMAIN db = {"user", "count"}
====
