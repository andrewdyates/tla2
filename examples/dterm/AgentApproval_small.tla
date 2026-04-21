---- MODULE AgentApproval_small ----
\* Small reproduction for #320 - ModelValue union membership with records
EXTENDS Integers

VARIABLE requests

Request == [
    id: Nat,
    completedAt: Nat \union {-1}
]

TypeInvariant ==
    /\ DOMAIN requests \subseteq 0..1
    /\ \A id \in DOMAIN requests:
        /\ requests[id].id \in Nat
        /\ requests[id].completedAt \in Nat \union {-1}

Init == requests = [
    i \in {0} |->
        [id |-> 0, completedAt |-> -1]
]

Next == UNCHANGED requests

Spec == Init /\ [][Next]_requests
====
