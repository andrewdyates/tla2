---- MODULE MinimalClamp ----
\* Minimal reproduction of Grid.tla issue #278
\* When rows=total_lines, display_offset should never change from 0

EXTENDS Integers

CONSTANTS MaxRows, MaxScrollback

VARIABLES rows, total_lines, display_offset

Clamp(val, minVal, maxVal) ==
    IF val < minVal THEN minVal
    ELSE IF val > maxVal THEN maxVal
    ELSE val

Init ==
    /\ rows \in 1..MaxRows
    /\ total_lines = rows  \* Start with no scrollback
    /\ display_offset = 0

\* This is the exact pattern from Grid.tla
Scroll(delta) ==
    LET maxOffset == IF total_lines > rows THEN total_lines - rows ELSE 0
    IN /\ display_offset' = Clamp(display_offset + delta, 0, maxOffset)
       /\ UNCHANGED <<rows, total_lines>>

Next ==
    \E delta \in -10..10 : Scroll(delta)

\* This should ALWAYS be true when rows = total_lines
DisplayOffsetValid ==
    /\ display_offset >= 0
    /\ display_offset <= IF total_lines > rows
                         THEN total_lines - rows
                         ELSE 0

vars == <<rows, total_lines, display_offset>>
Spec == Init /\ [][Next]_vars

====
