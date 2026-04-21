----- MODULE LetBindingBug2 -----
(* More complex reproduction for #278 false positive bug.
 *
 * Testing if the bug manifests when:
 * - Multiple variables can change
 * - LET binding depends on mutable state
 * - Parallel exploration with many workers
 *)
EXTENDS Integers

VARIABLES rows, total_lines, display_offset, dummy

\* Clamp helper
Clamp(val, minVal, maxVal) ==
    IF val < minVal THEN minVal
    ELSE IF val > maxVal THEN maxVal
    ELSE val

\* Start with rows = total_lines (maxOffset = 0)
Init ==
    /\ rows = 2
    /\ total_lines = 2
    /\ display_offset = 0
    /\ dummy = 0

\* Resize action - can change rows and total_lines
Resize(newRows) ==
    /\ newRows \in 1..3
    /\ rows' = newRows
    /\ total_lines' = IF total_lines >= newRows THEN total_lines ELSE newRows
    \* Adjust display_offset like Grid.tla
    /\ LET newMaxOffset == IF total_lines' > newRows THEN total_lines' - newRows ELSE 0
       IN display_offset' = IF display_offset > newMaxOffset THEN newMaxOffset ELSE display_offset
    /\ UNCHANGED dummy

\* Scroll action - uses LET binding
Scroll(delta) ==
    LET maxOffset == IF total_lines > rows THEN total_lines - rows ELSE 0
    IN /\ display_offset' = Clamp(display_offset + delta, 0, maxOffset)
       /\ UNCHANGED <<rows, total_lines, dummy>>

\* Dummy action to increase state space
IncrementDummy ==
    /\ dummy < 3
    /\ dummy' = dummy + 1
    /\ UNCHANGED <<rows, total_lines, display_offset>>

Next ==
    \/ \E delta \in -5..5 : Scroll(delta)
    \/ \E newRows \in 1..3 : Resize(newRows)
    \/ IncrementDummy

\* Invariant: display_offset <= max possible offset
DisplayOffsetValid ==
    display_offset <= IF total_lines > rows THEN total_lines - rows ELSE 0

====
