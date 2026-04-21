---- MODULE FunctionOperations ----
\* Function operations: construction, application, DOMAIN, EXCEPT.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals, FiniteSets
VARIABLE f

Init == f = [i \in {1, 2, 3} |-> i * 10]
Next == f' = [f EXCEPT ![2] = 99]

DomainOK == DOMAIN f = {1, 2, 3}
AppOK == f[1] = 10
ExceptOK == f[2] \in {20, 99}
FuncSetOK == [{"a", "b"} -> {0, 1}] # {}
====
