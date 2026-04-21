---- MODULE RecordOperations ----
\* Record operations: construction, field access, EXCEPT.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals
VARIABLE r

Init == r = [name |-> "alice", age |-> 30]
Next == IF r.age < 31 THEN r' = [r EXCEPT !.age = r.age + 1]
        ELSE UNCHANGED r

FieldOK == r.name = "alice"
AgeOK == r.age >= 30
ExceptOK == r.age <= 31
DomainOK == DOMAIN r = {"name", "age"}
====
