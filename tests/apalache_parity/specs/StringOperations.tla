---- MODULE StringOperations ----
\* String operations: comparison, set membership, record field names.
\* Exercises string literals, string equality, and strings as set elements.
\* Expected: model check passes, all invariants hold.
EXTENDS Naturals, FiniteSets

VARIABLE state

Names == {"alice", "bob", "charlie"}

Init == state = [name |-> "alice", count |-> 0]

Next ==
  \/ /\ state.count < 2
     /\ \E n \in Names :
          state' = [name |-> n, count |-> state.count + 1]
  \/ state.count >= 2 /\ UNCHANGED state

TypeOK == state.name \in Names /\ state.count \in 0..2
StringEqOK == "alice" = "alice" /\ "alice" # "bob"
StringSetOK == Cardinality(Names) = 3
DomainStringOK == DOMAIN state = {"name", "count"}
====
