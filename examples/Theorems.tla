---- MODULE Theorems ----

THEOREM BasicImplication == \A x \in Int : x > 5 => x > 3

THEOREM SimpleTautology == TRUE

THEOREM BooleanLogic == \A a, b \in BOOLEAN : (a /\ b) => a

THEOREM FalseTheorem == \A x \in Int : x > 3 => x > 5

====
