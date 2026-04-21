---- MODULE TypeAnnotation ----
\* Apalache <: type annotation operator (Part of #3828).
\* Tests <: used as identity annotation on various expression types.
\* In BFS mode, a <: b == a, so <: is pure identity.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals, FiniteSets

\* Define the <: operator (identity, used as type annotation in Apalache)
a <: b == a

VARIABLE state

Init ==
    /\ state = [
        nums |-> {} <: {"set_of_int"},
        flag |-> FALSE,
        count |-> 0
       ]

Next ==
    \/ /\ state.count < 3
       /\ state' = [state EXCEPT
            !.nums = state.nums \union {state.count},
            !.count = state.count + 1]
    \/ UNCHANGED state

\* Verify <: acts as identity
EmptyAnnotated == ({} <: {"type_hint"}) = {}
SetAnnotated == ({1, 2} <: {"type_hint"}) = {1, 2}
IntAnnotated == (42 <: "type_hint") = 42
BoolAnnotated == (TRUE <: "type_hint") = TRUE
SeqAnnotated == (<<1, 2>> <: "type_hint") = <<1, 2>>
CountOK == state.count \in 0..3
NumsOK == state.nums \subseteq 0..2
FlagOK == state.flag \in BOOLEAN
====
