------------------------------ MODULE VT52 ------------------------------
(****************************************************************************)
(* TLA+ Specification for VT52 Compatibility Mode                           *)
(*                                                                          *)
(* This specification defines:                                              *)
(* - VT52 mode state (ANSI vs VT52)                                        *)
(* - VT52 cursor addressing state machine (ESC Y row col)                  *)
(* - VT52 escape sequence handling                                         *)
(*                                                                          *)
(* Reference: VT52 Programmer Information, DEC                             *)
(* Implementation: crates/dterm-core/src/terminal/mod.rs                   *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets

(****************************************************************************)
(* CONSTANTS                                                                *)
(****************************************************************************)

CONSTANTS
    MaxRows,              \* Maximum terminal rows (e.g., 24)
    MaxCols               \* Maximum terminal columns (e.g., 80)

\* Constraint assumptions for model checking
ASSUME MaxRows \in Nat /\ MaxRows > 0
ASSUME MaxCols \in Nat /\ MaxCols > 0

(****************************************************************************)
(* VT52 CURSOR STATE DEFINITIONS                                           *)
(****************************************************************************)

\* VT52 cursor addressing states (for ESC Y row col sequence)
\* All states use tuple format for TLC type consistency:
\* - <<"None">>: Normal operation, not collecting cursor position
\* - <<"WaitingRow">>: After ESC Y, waiting for row byte
\* - <<"WaitingCol", row>>: After row byte, waiting for col byte
CursorStateNone == <<"None">>
CursorStateWaitingRow == <<"WaitingRow">>
CursorStateWaitingCol(r) == <<"WaitingCol", r>>

Vt52CursorStateValues ==
    {CursorStateNone, CursorStateWaitingRow} \cup {CursorStateWaitingCol(r) : r \in 0..MaxRows-1}

\* VT52 escape sequence final bytes
Vt52EscSequences == {
    "A",    \* Cursor up
    "B",    \* Cursor down
    "C",    \* Cursor right
    "D",    \* Cursor left
    "H",    \* Cursor home
    "I",    \* Reverse line feed
    "J",    \* Erase to end of screen
    "K",    \* Erase to end of line
    "Y",    \* Direct cursor addressing (starts ESC Y row col)
    "Z",    \* Identify terminal
    "<",    \* Exit VT52 mode (return to ANSI)
    "F",    \* Enter graphics character set
    "G",    \* Exit graphics character set
    "=",    \* Enter alternate keypad mode
    ">"     \* Exit alternate keypad mode
}

(****************************************************************************)
(* VARIABLES                                                                *)
(****************************************************************************)

VARIABLES
    vt52_mode,            \* Boolean: true if in VT52 mode, false if ANSI
    cursor_state,         \* VT52 cursor addressing state
    cursor_row,           \* Current cursor row (0-indexed)
    cursor_col,           \* Current cursor column (0-indexed)
    graphics_mode,        \* VT52 graphics character set active
    keypad_mode           \* Alternate keypad mode active

vars == <<vt52_mode, cursor_state, cursor_row, cursor_col, graphics_mode, keypad_mode>>

(****************************************************************************)
(* TYPE INVARIANT                                                           *)
(****************************************************************************)

TypeInvariant ==
    /\ vt52_mode \in BOOLEAN
    /\ cursor_state \in Vt52CursorStateValues
    /\ cursor_row \in 0..MaxRows-1
    /\ cursor_col \in 0..MaxCols-1
    /\ graphics_mode \in BOOLEAN
    /\ keypad_mode \in BOOLEAN

(****************************************************************************)
(* SAFETY INVARIANTS                                                        *)
(****************************************************************************)

\* INV-VT52-1: Cursor state is valid
CursorStateValid ==
    cursor_state \in Vt52CursorStateValues

\* INV-VT52-2: Cursor position within bounds
CursorInBounds ==
    /\ cursor_row >= 0
    /\ cursor_row < MaxRows
    /\ cursor_col >= 0
    /\ cursor_col < MaxCols

\* INV-VT52-3: When collecting cursor position, must be in VT52 mode
\* (This invariant ensures cursor_state is only non-None in VT52 mode)
CursorStateOnlyInVt52 ==
    cursor_state # CursorStateNone => vt52_mode

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ CursorStateValid
    /\ CursorInBounds
    /\ CursorStateOnlyInVt52

(****************************************************************************)
(* INITIAL STATE                                                            *)
(****************************************************************************)

Init ==
    /\ vt52_mode = FALSE          \* Start in ANSI mode
    /\ cursor_state = CursorStateNone
    /\ cursor_row = 0
    /\ cursor_col = 0
    /\ graphics_mode = FALSE
    /\ keypad_mode = FALSE

(****************************************************************************)
(* MODE TRANSITIONS                                                         *)
(****************************************************************************)

\* Enter VT52 mode (CSI ? 2 l)
EnterVt52Mode ==
    /\ vt52_mode = FALSE
    /\ vt52_mode' = TRUE
    /\ cursor_state' = CursorStateNone
    /\ UNCHANGED <<cursor_row, cursor_col, graphics_mode, keypad_mode>>

\* Exit VT52 mode via ANSI sequence (CSI ? 2 h)
ExitVt52ModeAnsi ==
    /\ vt52_mode = TRUE
    /\ vt52_mode' = FALSE
    /\ cursor_state' = CursorStateNone
    /\ UNCHANGED <<cursor_row, cursor_col, graphics_mode, keypad_mode>>

\* Exit VT52 mode via VT52 sequence (ESC <)
ExitVt52ModeVt52 ==
    /\ vt52_mode = TRUE
    /\ vt52_mode' = FALSE
    /\ cursor_state' = CursorStateNone
    /\ UNCHANGED <<cursor_row, cursor_col, graphics_mode, keypad_mode>>

(****************************************************************************)
(* VT52 CURSOR MOVEMENT                                                     *)
(****************************************************************************)

\* ESC A: Cursor up
Vt52CursorUp ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ cursor_row' = IF cursor_row > 0 THEN cursor_row - 1 ELSE 0
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_col, graphics_mode, keypad_mode>>

\* ESC B: Cursor down
Vt52CursorDown ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ cursor_row' = IF cursor_row < MaxRows - 1 THEN cursor_row + 1 ELSE cursor_row
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_col, graphics_mode, keypad_mode>>

\* ESC C: Cursor right
Vt52CursorRight ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ cursor_col' = IF cursor_col < MaxCols - 1 THEN cursor_col + 1 ELSE cursor_col
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_row, graphics_mode, keypad_mode>>

\* ESC D: Cursor left
Vt52CursorLeft ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ cursor_col' = IF cursor_col > 0 THEN cursor_col - 1 ELSE 0
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_row, graphics_mode, keypad_mode>>

\* ESC H: Cursor home (0, 0)
Vt52CursorHome ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ cursor_row' = 0
    /\ cursor_col' = 0
    /\ UNCHANGED <<vt52_mode, cursor_state, graphics_mode, keypad_mode>>

(****************************************************************************)
(* VT52 DIRECT CURSOR ADDRESSING (ESC Y row col)                           *)
(****************************************************************************)

\* ESC Y received - start cursor addressing sequence
Vt52StartCursorAddress ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ cursor_state' = CursorStateWaitingRow
    /\ UNCHANGED <<vt52_mode, cursor_row, cursor_col, graphics_mode, keypad_mode>>

\* Row byte received (row = byte - 32)
Vt52ReceiveRow(row) ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateWaitingRow
    /\ row \in 0..MaxRows-1
    /\ cursor_state' = CursorStateWaitingCol(row)
    /\ UNCHANGED <<vt52_mode, cursor_row, cursor_col, graphics_mode, keypad_mode>>

\* Column byte received (col = byte - 32), complete addressing
Vt52ReceiveCol(row, col) ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateWaitingCol(row)
    /\ col \in 0..MaxCols-1
    /\ cursor_state' = CursorStateNone
    /\ cursor_row' = row
    /\ cursor_col' = col
    /\ UNCHANGED <<vt52_mode, graphics_mode, keypad_mode>>

(****************************************************************************)
(* VT52 OTHER SEQUENCES                                                     *)
(****************************************************************************)

\* ESC F: Enter graphics mode
Vt52EnterGraphics ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ graphics_mode' = TRUE
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_row, cursor_col, keypad_mode>>

\* ESC G: Exit graphics mode
Vt52ExitGraphics ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ graphics_mode' = FALSE
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_row, cursor_col, keypad_mode>>

\* ESC =: Enter alternate keypad mode
Vt52EnterKeypad ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ keypad_mode' = TRUE
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_row, cursor_col, graphics_mode>>

\* ESC >: Exit alternate keypad mode
Vt52ExitKeypad ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ keypad_mode' = FALSE
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_row, cursor_col, graphics_mode>>

\* ESC I: Reverse line feed (move up, scroll if at top)
Vt52ReverseLineFeed ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ cursor_row' = IF cursor_row > 0 THEN cursor_row - 1 ELSE 0
    /\ UNCHANGED <<vt52_mode, cursor_state, cursor_col, graphics_mode, keypad_mode>>

\* ESC J: Erase to end of screen (no cursor movement)
\* ESC K: Erase to end of line (no cursor movement)
\* ESC Z: Identify (response sent, no state change)
Vt52NoStateChange ==
    /\ vt52_mode = TRUE
    /\ cursor_state = CursorStateNone
    /\ UNCHANGED vars

(****************************************************************************)
(* ANSI MODE ACTIONS (when not in VT52 mode)                               *)
(****************************************************************************)

\* Normal ANSI cursor movement (simplified)
AnsiCursorMove(new_row, new_col) ==
    /\ vt52_mode = FALSE
    /\ new_row \in 0..MaxRows-1
    /\ new_col \in 0..MaxCols-1
    /\ cursor_row' = new_row
    /\ cursor_col' = new_col
    /\ UNCHANGED <<vt52_mode, cursor_state, graphics_mode, keypad_mode>>

(****************************************************************************)
(* NEXT STATE RELATION                                                      *)
(****************************************************************************)

Next ==
    \* Mode transitions
    \/ EnterVt52Mode
    \/ ExitVt52ModeAnsi
    \/ ExitVt52ModeVt52
    \* VT52 cursor movement
    \/ Vt52CursorUp
    \/ Vt52CursorDown
    \/ Vt52CursorRight
    \/ Vt52CursorLeft
    \/ Vt52CursorHome
    \/ Vt52ReverseLineFeed
    \* VT52 direct cursor addressing
    \/ Vt52StartCursorAddress
    \/ \E r \in 0..MaxRows-1 : Vt52ReceiveRow(r)
    \/ \E r \in 0..MaxRows-1, c \in 0..MaxCols-1 : Vt52ReceiveCol(r, c)
    \* VT52 mode switches
    \/ Vt52EnterGraphics
    \/ Vt52ExitGraphics
    \/ Vt52EnterKeypad
    \/ Vt52ExitKeypad
    \* VT52 no-op sequences
    \/ Vt52NoStateChange
    \* ANSI mode cursor movement
    \/ \E r \in 0..MaxRows-1, c \in 0..MaxCols-1 : AnsiCursorMove(r, c)

(****************************************************************************)
(* SPECIFICATION                                                            *)
(****************************************************************************)

Spec == Init /\ [][Next]_vars

(****************************************************************************)
(* LIVENESS PROPERTIES                                                      *)
(****************************************************************************)

\* Eventually cursor addressing completes (if started)
CursorAddressingTerminates ==
    (cursor_state # CursorStateNone) ~> (cursor_state = CursorStateNone)

(****************************************************************************)
(* THEOREMS                                                                 *)
(****************************************************************************)

\* The cursor state is always valid
THEOREM CursorStateTheorem == Spec => []CursorStateValid

\* The cursor is always within bounds
THEOREM CursorBoundsTheorem == Spec => []CursorInBounds

\* Type invariant is maintained
THEOREM TypeTheorem == Spec => []TypeInvariant

\* Cursor addressing state only exists in VT52 mode
THEOREM CursorStateOnlyInVt52Theorem == Spec => []CursorStateOnlyInVt52

=============================================================================
