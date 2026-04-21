---- MODULE SetComprehension ----
\* Set comprehensions (map and filter) in various forms (Part of #3828).
\* Tests {expr : x \in S}, {x \in S : pred}, nested comprehensions.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals, FiniteSets

VARIABLE items

Init == items = {1, 2, 3, 4, 5}
Next == UNCHANGED items

\* Set map: {f(x) : x \in S}
Doubled == {x * 2 : x \in items}
DoubledOK == Doubled = {2, 4, 6, 8, 10}

\* Set filter: {x \in S : P(x)}
Evens == {x \in items : x % 2 = 0}
EvensOK == Evens = {2, 4}

\* Nested comprehension
Pairs == {<<x, y>> : x \in {1, 2}, y \in {3, 4}}
PairsOK == Cardinality(Pairs) = 4

\* Comprehension with complex expression
Sums == {x + y : x \in {1, 2}, y \in {10, 20}}
SumsOK == Sums = {11, 12, 21, 22}

\* Filtered map
BigDoubled == {x * 2 : x \in {y \in items : y > 3}}
BigDoubledOK == BigDoubled = {8, 10}

\* Empty set comprehension
EmptyFilter == {x \in items : x > 100} = {}
====
