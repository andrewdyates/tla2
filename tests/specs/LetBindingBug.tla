----- MODULE LetBindingBug -----
(* Minimal reproduction for #278 false positive bug.
 *
 * Root cause hypothesis: LET bindings stored in ctx.env are not captured
 * by get_local_bindings() when expressions are deferred, causing the
 * LET-bound variable to be missing during later evaluation.
 *)
EXTENDS Integers

VARIABLES rows, total_lines, display_offset

\* Clamp helper - same as Grid.tla
Clamp(val, minVal, maxVal) ==
    IF val < minVal THEN minVal
    ELSE IF val > maxVal THEN maxVal
    ELSE val

Init ==
    /\ rows = 2
    /\ total_lines = 2
    /\ display_offset = 0

\* This action should ALWAYS produce display_offset' = 0
\* when rows = 2 and total_lines = 2.
\*
\* The LET binding maxOffset evaluates to 0 in current state,
\* so Clamp(delta, 0, 0) = 0 for any delta.
Scroll(delta) ==
    LET maxOffset == IF total_lines > rows THEN total_lines - rows ELSE 0
    IN /\ display_offset' = Clamp(display_offset + delta, 0, maxOffset)
       /\ UNCHANGED <<rows, total_lines>>

Next == \E delta \in -10..10 : Scroll(delta)

\* This invariant should ALWAYS hold when rows = total_lines
\* because maxOffset = 0 and Clamp forces display_offset' = 0
DisplayOffsetValid ==
    display_offset <= IF total_lines > rows THEN total_lines - rows ELSE 0

\* If rows = total_lines, display_offset MUST be 0
ZeroWhenEqual ==
    (rows = total_lines) => (display_offset = 0)

====
