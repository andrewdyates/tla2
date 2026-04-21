---- MODULE CannotHandleTemporalFormula2213 ----
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\*
\* Repro for TLC liveness conversion failure:
\*   "TLC cannot handle the temporal formula ..." (EC 2213).
\*
\* The property below requires expanding a bounded temporal-level quantifier
\* over a non-enumerable domain (Nat).

EXTENDS Naturals, TLC

VARIABLE x

Init == x = 0
Next == x' = x

Spec == Init /\ [][Next]_x

\* Temporal-level bounded quantifier (because of <>), with a non-enumerable
\* bound domain. Both TLC and TLA2 should report EC 2213.
\*
\* Prefer a variant where TLC uses the "two-parameter" (reason-on-newline) form.
Prop == \A n \in Nat : <> (x = n)

====
