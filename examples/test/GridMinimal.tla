---- MODULE GridMinimal ----
\* Minimal reproduction of Grid.tla issue #278
\* Tests Scroll action with cells (function with tuple domain)

EXTENDS Integers, FiniteSets

CONSTANTS MaxRows, MaxCols

VARIABLES rows, cols, display_offset, total_lines, cells

Clamp(val, minVal, maxVal) ==
    IF val < minVal THEN minVal
    ELSE IF val > maxVal THEN maxVal
    ELSE val

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

Init ==
    /\ rows \in 1..MaxRows
    /\ cols \in 1..MaxCols
    /\ display_offset = 0
    /\ total_lines = rows
    /\ cells = [pos \in {<<r, c>> : r \in 0..rows-1, c \in 0..cols-1} |-> 0]

Scroll(delta) ==
    LET maxOffset == IF total_lines > rows THEN total_lines - rows ELSE 0
    IN /\ display_offset' = Clamp(display_offset + delta, 0, maxOffset)
       /\ UNCHANGED <<rows, cols, total_lines, cells>>

Resize(newRows, newCols) ==
    /\ newRows \in 1..MaxRows
    /\ newCols \in 1..MaxCols
    /\ rows' = newRows
    /\ cols' = newCols
    /\ total_lines' = Min(Max(total_lines, newRows), 5 + newRows)
    /\ LET newMaxOffset == IF total_lines' > newRows THEN total_lines' - newRows ELSE 0
       IN display_offset' = Min(display_offset, newMaxOffset)
    /\ cells' = [pos \in {<<r, c>> : r \in 0..total_lines'-1, c \in 0..newCols-1} |->
        IF <<pos[1], pos[2]>> \in DOMAIN cells
        THEN cells[<<pos[1], pos[2]>>]
        ELSE 0]

Next ==
    \/ \E delta \in -5..5 : Scroll(delta)
    \/ \E nr \in 1..MaxRows, nc \in 1..MaxCols : Resize(nr, nc)

DisplayOffsetValid ==
    /\ display_offset >= 0
    /\ display_offset <= IF total_lines > rows
                         THEN total_lines - rows
                         ELSE 0

Safety == DisplayOffsetValid

vars == <<rows, cols, display_offset, total_lines, cells>>
Spec == Init /\ [][Next]_vars

====
