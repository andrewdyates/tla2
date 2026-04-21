----------------------------- MODULE TestShadow -----------------------------
(* Minimal reproduction of variable shadowing bug hypothesis.
   Tests whether an inner quantifier binding `v` inside an operator call
   corrupts an outer `v` bound by \E v \in Value.

   Expected: TLC passes, TLA2 should also pass.
   If TLA2 finds a false positive invariant violation, the bug is confirmed
   to be in variable shadowing during operator evaluation. *)

EXTENDS Integers

CONSTANTS Value, Actor

VARIABLE state

\* This operator uses `v` as a bound variable (same name as outer binding)
HasValueAt(a, k) == \A v \in Value : <<k, v>> \notin state[a]

\* This action has \E v \in Value: ... HasValueAt(self, b) ... where
\* HasValueAt also binds v internally.
\* The guard checks that no other actor has a different value at slot b.
DoAction(self, b, v) ==
  /\ HasValueAt(self, b)
  /\ \A p \in Actor \ {self} :
       \A w \in Value : <<b, w>> \in state[p] => (w = v)
  /\ state' = [state EXCEPT ![self] = @ \cup {<<b, v>>}]

Init == state = [a \in Actor |-> {}]

Next == \E self \in Actor, b \in {0, 1} :
          \/ \E v \in Value : DoAction(self, b, v)

\* Invariant: two different actors cannot have different values at the same slot
Consistent == \A a1, a2 \in Actor, b \in {0, 1}, v1, v2 \in Value :
    (<<b, v1>> \in state[a1] /\ <<b, v2>> \in state[a2]) => (v1 = v2)

Spec == Init /\ [][Next]_state
=============================================================================
