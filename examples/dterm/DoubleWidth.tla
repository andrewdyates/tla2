--------------------------- MODULE DoubleWidth ---------------------------
(***************************************************************************)
(* TLA+ Specification for Double-Width/Height Line Cursor Behavior         *)
(*                                                                          *)
(* This specification defines:                                              *)
(* - Line size attributes (SingleWidth, DoubleWidth, DoubleHeight)         *)
(* - Effective column limits based on line size                            *)
(* - Cursor movement respecting line size constraints                      *)
(* - Character writing on double-width lines                               *)
(*                                                                          *)
(* Reference: VT100 User Guide, DECDWL/DECDHL escape sequences             *)
(* VTTEST Section 5: Double-size characters                                 *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    MaxRows,              \* Maximum terminal rows (e.g., 24)
    MaxCols               \* Maximum terminal columns (e.g., 80)

\* Constraint assumptions for model checking
ASSUME MaxRows \in Nat /\ MaxRows > 0
ASSUME MaxCols \in Nat /\ MaxCols > 0 /\ MaxCols >= 2

(***************************************************************************)
(* LINE SIZE DEFINITIONS                                                    *)
(***************************************************************************)

\* Line size enum values
LineSizeValues == {"SingleWidth", "DoubleWidth", "DoubleHeightTop", "DoubleHeightBottom"}

\* Check if a line size is double-width (includes double-height)
IsDoubleWidth(size) ==
    size \in {"DoubleWidth", "DoubleHeightTop", "DoubleHeightBottom"}

(***************************************************************************)
(* VARIABLES                                                                *)
(***************************************************************************)

VARIABLES
    rows,                 \* Current visible row count
    cols,                 \* Current column count (physical)
    cursor_row,           \* Current cursor row (0-indexed)
    cursor_col,           \* Current cursor column (0-indexed, logical)
    line_size             \* Function: row index -> line size

vars == <<rows, cols, cursor_row, cursor_col, line_size>>

(***************************************************************************)
(* HELPER FUNCTIONS                                                         *)
(***************************************************************************)

\* Get the effective column limit for a row
\* Double-width lines have half the usable columns
EffectiveColLimit(row) ==
    IF row \in DOMAIN line_size /\ IsDoubleWidth(line_size[row])
    THEN cols \div 2
    ELSE cols

\* Get the current row's effective column limit
CurrentEffectiveColLimit ==
    EffectiveColLimit(cursor_row)

\* Convert logical column to physical column
\* On double-width lines, logical col 0 is physical cols 0-1, etc.
LogicalToPhysical(row, logical_col) ==
    IF row \in DOMAIN line_size /\ IsDoubleWidth(line_size[row])
    THEN logical_col * 2
    ELSE logical_col

\* Convert physical column to logical column
PhysicalToLogical(row, physical_col) ==
    IF row \in DOMAIN line_size /\ IsDoubleWidth(line_size[row])
    THEN physical_col \div 2
    ELSE physical_col

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(***************************************************************************)

TypeInvariant ==
    /\ rows \in 1..MaxRows
    /\ cols \in 2..MaxCols
    /\ cursor_row \in 0..rows-1
    /\ cursor_col \in 0..cols-1
    /\ line_size \in [0..rows-1 -> LineSizeValues]

(***************************************************************************)
(* SAFETY INVARIANTS                                                        *)
(***************************************************************************)

\* INV-DW-1: Cursor column never exceeds effective limit for current line
CursorWithinEffectiveLimit ==
    cursor_col < CurrentEffectiveColLimit

\* INV-DW-2: Cursor is always within grid bounds
CursorWithinBounds ==
    /\ cursor_row >= 0
    /\ cursor_row < rows
    /\ cursor_col >= 0
    /\ cursor_col < cols

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ CursorWithinEffectiveLimit
    /\ CursorWithinBounds

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    /\ rows = MaxRows
    /\ cols = MaxCols
    /\ cursor_row = 0
    /\ cursor_col = 0
    /\ line_size = [r \in 0..MaxRows-1 |-> "SingleWidth"]

(***************************************************************************)
(* CURSOR MOVEMENT ACTIONS                                                  *)
(***************************************************************************)

\* Move cursor right by n logical columns
\* Stops at effective column limit
CursorForward(n) ==
    /\ n > 0
    /\ LET limit == CurrentEffectiveColLimit
           new_col == cursor_col + n
       IN cursor_col' = IF new_col >= limit THEN limit - 1 ELSE new_col
    /\ UNCHANGED <<rows, cols, cursor_row, line_size>>

\* Move cursor left by n logical columns
\* Stops at column 0
CursorBackward(n) ==
    /\ n > 0
    /\ cursor_col' = IF cursor_col >= n THEN cursor_col - n ELSE 0
    /\ UNCHANGED <<rows, cols, cursor_row, line_size>>

\* Move cursor up by n rows
\* Stops at row 0
CursorUp(n) ==
    /\ n > 0
    /\ cursor_row' = IF cursor_row >= n THEN cursor_row - n ELSE 0
    \* Clamp column to new row's effective limit
    /\ LET new_row == IF cursor_row >= n THEN cursor_row - n ELSE 0
           new_limit == EffectiveColLimit(new_row)
       IN cursor_col' = IF cursor_col >= new_limit THEN new_limit - 1 ELSE cursor_col
    /\ UNCHANGED <<rows, cols, line_size>>

\* Move cursor down by n rows
\* Stops at last row
CursorDown(n) ==
    /\ n > 0
    /\ LET new_row == IF cursor_row + n >= rows THEN rows - 1 ELSE cursor_row + n
       IN cursor_row' = new_row
    \* Clamp column to new row's effective limit
    /\ LET new_row == IF cursor_row + n >= rows THEN rows - 1 ELSE cursor_row + n
           new_limit == EffectiveColLimit(new_row)
       IN cursor_col' = IF cursor_col >= new_limit THEN new_limit - 1 ELSE cursor_col
    /\ UNCHANGED <<rows, cols, line_size>>

\* Move cursor to absolute position (row, col)
\* Clamps to effective limits
CursorPosition(row, col) ==
    /\ row \in 0..rows-1
    /\ col \in 0..cols-1
    /\ cursor_row' = row
    /\ LET limit == EffectiveColLimit(row)
       IN cursor_col' = IF col >= limit THEN limit - 1 ELSE col
    /\ UNCHANGED <<rows, cols, line_size>>

\* Carriage return - move to column 0
CarriageReturn ==
    /\ cursor_col' = 0
    /\ UNCHANGED <<rows, cols, cursor_row, line_size>>

(***************************************************************************)
(* LINE SIZE ACTIONS                                                        *)
(***************************************************************************)

\* Set line size for current row
\* If setting to double-width, clamp cursor column
SetLineSize(size) ==
    /\ size \in LineSizeValues
    /\ line_size' = [line_size EXCEPT ![cursor_row] = size]
    \* Clamp cursor if new line is double-width
    /\ LET new_limit == IF IsDoubleWidth(size) THEN cols \div 2 ELSE cols
       IN cursor_col' = IF cursor_col >= new_limit THEN new_limit - 1 ELSE cursor_col
    /\ UNCHANGED <<rows, cols, cursor_row>>

\* DECDWL - Set current line to double-width
DECDWL ==
    SetLineSize("DoubleWidth")

\* DECDHL top - Set current line to double-height top
DECDHLTop ==
    SetLineSize("DoubleHeightTop")

\* DECDHL bottom - Set current line to double-height bottom
DECDHLBottom ==
    SetLineSize("DoubleHeightBottom")

\* DECSWL - Set current line to single-width
DECSWL ==
    SetLineSize("SingleWidth")

(***************************************************************************)
(* CHARACTER WRITING                                                        *)
(***************************************************************************)

\* Write a character at cursor position
\* On double-width line, character occupies 2 physical cells
\* Advances cursor by 1 logical column
WriteChar ==
    /\ LET limit == CurrentEffectiveColLimit
       IN /\ cursor_col < limit - 1
          /\ cursor_col' = cursor_col + 1
    /\ UNCHANGED <<rows, cols, cursor_row, line_size>>

\* Write character at last column - cursor stays at last column
WriteCharAtEnd ==
    /\ cursor_col = CurrentEffectiveColLimit - 1
    /\ UNCHANGED vars

\* Write character with line wrap
\* When at end of line with autowrap, moves to next line column 0
WriteCharWithWrap ==
    /\ cursor_col = CurrentEffectiveColLimit - 1
    /\ cursor_row < rows - 1
    /\ cursor_row' = cursor_row + 1
    /\ cursor_col' = 0
    /\ UNCHANGED <<rows, cols, line_size>>

(***************************************************************************)
(* NEXT STATE RELATION                                                      *)
(***************************************************************************)

Next ==
    \/ \E n \in 1..10 : CursorForward(n)
    \/ \E n \in 1..10 : CursorBackward(n)
    \/ \E n \in 1..10 : CursorUp(n)
    \/ \E n \in 1..10 : CursorDown(n)
    \/ \E r \in 0..rows-1, c \in 0..cols-1 : CursorPosition(r, c)
    \/ CarriageReturn
    \/ DECDWL
    \/ DECDHLTop
    \/ DECDHLBottom
    \/ DECSWL
    \/ WriteChar
    \/ WriteCharAtEnd
    \/ WriteCharWithWrap

(***************************************************************************)
(* SPECIFICATION                                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* THEOREMS                                                                 *)
(***************************************************************************)

\* The cursor always respects the effective column limit
THEOREM CursorLimitTheorem == Spec => []CursorWithinEffectiveLimit

\* The cursor is always within grid bounds
THEOREM CursorBoundsTheorem == Spec => []CursorWithinBounds

\* Type invariant is maintained
THEOREM TypeTheorem == Spec => []TypeInvariant

=============================================================================
