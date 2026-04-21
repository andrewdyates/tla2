---- MODULE TypeCheckBasics ----
\* Type checking basics: typed operators and well-formed expressions.
\* Exercises typed constants, typed variables, and operator types.
\* Expected: model check passes, type-safe invariants hold.
EXTENDS Naturals, FiniteSets
VARIABLES count, flag, items

Init == /\ count = 0
        /\ flag = FALSE
        /\ items = {}

Next == /\ count' = IF count < 3 THEN count + 1 ELSE count
        /\ flag' = (count' >= 2)
        /\ items' = items \union {count'}

CountTypeOK == count \in Nat
FlagTypeOK == flag \in BOOLEAN
ItemsTypeOK == \A i \in items : i \in Nat
SizeOK == Cardinality(items) <= 4
====
