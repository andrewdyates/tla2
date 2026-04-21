---- MODULE LetWithoutIn ----
\* LET-without-IN in operator definitions (Apalache extension) (Part of #3828).
\* Tests that LET ... IN LET ... (no final IN body) is accepted.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals, Sequences, FiniteSets

VARIABLE items

\* Helper using LET-without-IN pattern from Apalache's FoldDefined.tla
AddToSet(S, e) == S \union {e}

\* Build a range from a sequence using nested LET
Range(seq) ==
    LET helper(S, e) == S \union {e}
    IN LET result == helper(helper({}, 1), 2)
    IN result

Init == items = {1, 2}

Next == IF Cardinality(items) < 4
        THEN \E x \in 1..5 : items' = items \union {x}
        ELSE UNCHANGED items

RangeOK == Range(<<1, 2>>) = {1, 2}
ItemsSubset == items \subseteq 1..5
ItemsBounded == Cardinality(items) <= 5
====
