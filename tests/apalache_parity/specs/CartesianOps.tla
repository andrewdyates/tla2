---- MODULE CartesianOps ----
\* Cartesian product operations and tuple destructuring (Part of #3828).
\* Tests S \X T with quantifiers, tuple indexing, and nested products.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals, FiniteSets

VARIABLE pair

Colors == {"R", "G", "B"}
Sizes == {1, 2, 3}

Init == pair \in Colors \X Sizes

Next ==
    \E c \in Colors, s \in Sizes :
        pair' = <<c, s>>

\* Invariants
PairInProduct == pair \in Colors \X Sizes
Color == pair[1] \in Colors
Size == pair[2] \in Sizes
ProductCard == Cardinality(Colors \X Sizes) = 9
NestedProduct == Cardinality({1, 2} \X {3, 4} \X {5}) = 4
ForAllPairs == \A p \in Colors \X Sizes : p[2] >= 1
ExistsPair == \E p \in Colors \X Sizes : p[1] = "R" /\ p[2] = 3
====
