--------------------------- MODULE Selection ---------------------------
(***************************************************************************)
(* TLA+ Specification for dTerm Text Selection State Machine               *)
(*                                                                          *)
(* This specification defines the selection system for mouse-based text    *)
(* selection in the terminal:                                               *)
(* - Selection lifecycle: None -> InProgress -> Complete -> (Clear | Extend) *)
(* - Selection types: Simple, Block, Semantic, Lines                        *)
(* - Anchor points with side tracking (Left/Right of character)            *)
(* - Selection persistence across scroll operations                         *)
(*                                                                          *)
(* Key invariants:                                                          *)
(* - Start and end points are always valid grid coordinates                 *)
(* - Selection type cannot change during a selection                        *)
(* - Completed selection can be cleared by text changes or new selection   *)
(*                                                                          *)
(* Reference: Alacritty selection.rs, research/alacritty/                   *)
(***************************************************************************)

EXTENDS Integers, Naturals

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    MaxRows,              \* Maximum grid rows (display + scrollback)
    MaxCols,              \* Maximum grid columns
    SelectionTypes,       \* Set: {"Simple", "Block", "Semantic", "Lines"}
    Sides                 \* Set: {"Left", "Right"} - which side of a cell

\* Constraint assumptions for model checking
ASSUME MaxRows \in Nat /\ MaxRows > 0
ASSUME MaxCols \in Nat /\ MaxCols > 0
ASSUME SelectionTypes = {"Simple", "Block", "Semantic", "Lines"}
ASSUME Sides = {"Left", "Right"}

(***************************************************************************)
(* TYPE DEFINITIONS                                                         *)
(***************************************************************************)

\* A point in the grid (row, column)
\* Row 0 is the top of the visible area; negative rows are in scrollback
ValidRow == -(MaxRows - 1)..MaxRows
ValidCol == 0..(MaxCols - 1)

\* An anchor is a point plus which side of the cell
Anchors == [row: ValidRow, col: ValidCol, side: Sides]

\* Selection states
SelectionStates == {"None", "InProgress", "Complete"}

(***************************************************************************)
(* VARIABLES                                                                *)
(***************************************************************************)

VARIABLES
    state,            \* Current selection state: None, InProgress, Complete
    selType,          \* Selection type: Simple, Block, Semantic, Lines (or NONE)
    startAnchor,      \* Starting anchor point (set on mouse down)
    endAnchor,        \* Current end anchor point (updated on mouse move)
    scrollOffset      \* Current scroll position (for selection rotation)

vars == <<state, selType, startAnchor, endAnchor, scrollOffset>>

(***************************************************************************)
(* HELPER DEFINITIONS                                                       *)
(***************************************************************************)

\* Null anchor (used when no selection)
NullAnchor == [row |-> 0, col |-> 0, side |-> "Left"]

\* Check if an anchor is valid within grid bounds
ValidAnchor(a) ==
    /\ a.row \in ValidRow
    /\ a.col \in ValidCol
    /\ a.side \in Sides

\* Normalize selection to ensure start <= end (for Simple/Semantic/Lines)
\* For Block selection, this doesn't apply (rectangular region)
NormalizedStart(s, e, ty) ==
    IF ty = "Block"
    THEN s
    ELSE IF s.row < e.row \/ (s.row = e.row /\ s.col <= e.col)
         THEN s
         ELSE e

NormalizedEnd(s, e, ty) ==
    IF ty = "Block"
    THEN e
    ELSE IF s.row < e.row \/ (s.row = e.row /\ s.col <= e.col)
         THEN e
         ELSE s

\* Check if a point is within the selection range
\* This is simplified; real implementation handles wide chars, line wrapping
PointInSelection(row, col, s, e, ty) ==
    IF state # "Complete" /\ state # "InProgress"
    THEN FALSE
    ELSE
        LET ns == NormalizedStart(s, e, ty)
            ne == NormalizedEnd(s, e, ty)
        IN
            IF ty = "Block"
            THEN \* Rectangular selection
                /\ row >= ns.row /\ row <= ne.row
                /\ col >= ns.col /\ col <= ne.col
            ELSE \* Linear selection (Simple, Semantic, Lines)
                /\ row >= ns.row /\ row <= ne.row
                /\ (row > ns.row \/ col >= ns.col)
                /\ (row < ne.row \/ col <= ne.col)

\* Check if selection is empty (start equals end with same side)
IsEmptySelection ==
    /\ startAnchor.row = endAnchor.row
    /\ startAnchor.col = endAnchor.col
    /\ startAnchor.side = endAnchor.side

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(***************************************************************************)

TypeInvariant ==
    /\ state \in SelectionStates
    /\ selType \in SelectionTypes \cup {"NONE"}
    /\ ValidAnchor(startAnchor)
    /\ ValidAnchor(endAnchor)
    /\ scrollOffset \in 0..MaxRows
    \* If no selection, type should be NONE
    /\ (state = "None" => selType = "NONE")
    \* If selecting, type must be set
    /\ (state \in {"InProgress", "Complete"} => selType \in SelectionTypes)

(***************************************************************************)
(* SAFETY PROPERTIES                                                        *)
(***************************************************************************)

\* Selection endpoints are always valid grid coordinates
EndpointsValid ==
    /\ startAnchor.row \in ValidRow
    /\ startAnchor.col \in ValidCol
    /\ endAnchor.row \in ValidRow
    /\ endAnchor.col \in ValidCol

\* Selection type doesn't change during an active selection
\* (Modeled implicitly: updates don't modify selType)

\* If selection is None, anchors should be at default position
\* (This is a soft invariant - implementation may keep old values)

Safety ==
    /\ EndpointsValid
    /\ TypeInvariant

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    /\ state = "None"
    /\ selType = "NONE"
    /\ startAnchor = NullAnchor
    /\ endAnchor = NullAnchor
    /\ scrollOffset = 0

(***************************************************************************)
(* SELECTION OPERATIONS                                                     *)
(***************************************************************************)

\* Start a new selection (mouse button down)
\* This clears any existing selection and begins a new one
StartSelection(row, col, side, ty) ==
    /\ row \in ValidRow
    /\ col \in ValidCol
    /\ side \in Sides
    /\ ty \in SelectionTypes
    /\ state' = "InProgress"
    /\ selType' = ty
    /\ startAnchor' = [row |-> row, col |-> col, side |-> side]
    /\ endAnchor' = [row |-> row, col |-> col, side |-> side]
    /\ UNCHANGED scrollOffset

\* Update selection endpoint (mouse drag)
\* Can only update while selection is in progress
UpdateSelection(row, col, side) ==
    /\ state = "InProgress"
    /\ row \in ValidRow
    /\ col \in ValidCol
    /\ side \in Sides
    /\ endAnchor' = [row |-> row, col |-> col, side |-> side]
    /\ UNCHANGED <<state, selType, startAnchor, scrollOffset>>

\* Complete the selection (mouse button up)
CompleteSelection ==
    /\ state = "InProgress"
    /\ state' = "Complete"
    /\ UNCHANGED <<selType, startAnchor, endAnchor, scrollOffset>>

\* Clear selection (text change, escape, click outside selection)
ClearSelection ==
    /\ state \in {"InProgress", "Complete"}
    /\ state' = "None"
    /\ selType' = "NONE"
    \* Note: We keep anchor values but they're invalid when state is None
    /\ UNCHANGED <<startAnchor, endAnchor, scrollOffset>>

\* Extend an existing complete selection (shift-click)
\* Updates the end anchor while keeping start anchor fixed
ExtendSelection(row, col, side) ==
    /\ state = "Complete"
    /\ row \in ValidRow
    /\ col \in ValidCol
    /\ side \in Sides
    /\ endAnchor' = [row |-> row, col |-> col, side |-> side]
    \* Back to in-progress until mouse up
    /\ state' = "InProgress"
    /\ UNCHANGED <<selType, startAnchor, scrollOffset>>

(***************************************************************************)
(* SCROLL OPERATIONS                                                        *)
(* Selection must be adjusted when terminal scrolls                         *)
(***************************************************************************)

\* Scroll the terminal (positive delta scrolls down, negative scrolls up)
\* Selection rows are adjusted by the scroll amount
\* Selection is cleared if it scrolls entirely off-screen
Scroll(delta) ==
    /\ delta \in -MaxRows..MaxRows
    /\ scrollOffset' = (scrollOffset + delta) % MaxRows
    /\ IF state \in {"InProgress", "Complete"}
       THEN
           LET newStartRow == startAnchor.row - delta
               newEndRow == endAnchor.row - delta
               \* Check if selection is still visible
               stillValid == newStartRow \in ValidRow /\ newEndRow \in ValidRow
           IN
               IF stillValid
               THEN
                   /\ startAnchor' = [startAnchor EXCEPT !.row = newStartRow]
                   /\ endAnchor' = [endAnchor EXCEPT !.row = newEndRow]
                   /\ UNCHANGED <<state, selType>>
               ELSE
                   \* Selection scrolled off - clear it
                   /\ state' = "None"
                   /\ selType' = "NONE"
                   /\ UNCHANGED <<startAnchor, endAnchor>>
       ELSE UNCHANGED <<state, selType, startAnchor, endAnchor>>

\* Text added/modified in scroll region - may invalidate selection
TextChanged(affectedRowStart, affectedRowEnd) ==
    /\ affectedRowStart \in ValidRow
    /\ affectedRowEnd \in ValidRow
    /\ affectedRowStart <= affectedRowEnd
    /\ IF state \in {"InProgress", "Complete"}
       THEN
           LET ns == NormalizedStart(startAnchor, endAnchor, selType)
               ne == NormalizedEnd(startAnchor, endAnchor, selType)
               \* Selection overlaps with changed region
               overlaps == ~(ne.row < affectedRowStart \/ ns.row > affectedRowEnd)
           IN
               IF overlaps
               THEN
                   \* Clear selection on text change
                   /\ state' = "None"
                   /\ selType' = "NONE"
                   /\ UNCHANGED <<startAnchor, endAnchor, scrollOffset>>
               ELSE UNCHANGED vars
       ELSE UNCHANGED vars

(***************************************************************************)
(* SEMANTIC SELECTION EXPANSION                                             *)
(* For Semantic selection, boundaries expand to word boundaries             *)
(***************************************************************************)

\* Expand selection to semantic boundaries (word selection)
\* This is called automatically when semantic selection is started/updated
\* Modeled as a separate action; in practice it's part of start/update
ExpandSemantic(wordStartCol, wordEndCol) ==
    /\ state = "InProgress"
    /\ selType = "Semantic"
    /\ wordStartCol \in ValidCol
    /\ wordEndCol \in ValidCol
    /\ wordStartCol <= wordEndCol
    \* Expand start anchor to word start
    /\ startAnchor' = [startAnchor EXCEPT !.col = wordStartCol, !.side = "Left"]
    \* Expand end anchor to word end
    /\ endAnchor' = [endAnchor EXCEPT !.col = wordEndCol, !.side = "Right"]
    /\ UNCHANGED <<state, selType, scrollOffset>>

\* Expand selection to full lines (for Lines selection type)
ExpandLines ==
    /\ state = "InProgress"
    /\ selType = "Lines"
    \* Expand to full line width
    /\ startAnchor' = [startAnchor EXCEPT !.col = 0, !.side = "Left"]
    /\ endAnchor' = [endAnchor EXCEPT !.col = MaxCols - 1, !.side = "Right"]
    /\ UNCHANGED <<state, selType, scrollOffset>>

(***************************************************************************)
(* NEXT STATE RELATION                                                      *)
(***************************************************************************)

Next ==
    \* Start new selection with any type
    \/ \E r \in ValidRow, c \in ValidCol, s \in Sides, ty \in SelectionTypes :
           StartSelection(r, c, s, ty)
    \* Update selection endpoint during drag
    \/ \E r \in ValidRow, c \in ValidCol, s \in Sides :
           UpdateSelection(r, c, s)
    \* Complete selection
    \/ CompleteSelection
    \* Clear selection
    \/ ClearSelection
    \* Extend existing selection
    \/ \E r \in ValidRow, c \in ValidCol, s \in Sides :
           ExtendSelection(r, c, s)
    \* Scroll operations
    \/ \E d \in -MaxRows..MaxRows : Scroll(d)
    \* Text changes
    \/ \E rs \in ValidRow, re \in ValidRow :
           rs <= re /\ TextChanged(rs, re)
    \* Semantic expansion
    \/ \E sc \in ValidCol, ec \in ValidCol :
           sc <= ec /\ ExpandSemantic(sc, ec)
    \* Lines expansion
    \/ ExpandLines

(***************************************************************************)
(* SPECIFICATION                                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* THEOREMS                                                                 *)
(***************************************************************************)

\* Type invariant is always maintained
THEOREM TypeSafe == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyHolds == Spec => []Safety

\* Selection state machine is well-formed
\* - Can only go from None to InProgress (start)
\* - Can only go from InProgress to Complete (finish) or None (clear)
\* - Can only go from Complete to InProgress (extend) or None (clear)
SelectionStateValid ==
    [][
        \/ state = state'
        \/ (state = "None" /\ state' = "InProgress")
        \/ (state = "InProgress" /\ state' \in {"Complete", "None"})
        \/ (state = "Complete" /\ state' \in {"InProgress", "None"})
    ]_vars

THEOREM StateTransitionsValid == Spec => SelectionStateValid

\* Starting a selection sets both anchors to the same point
StartSetsBothAnchors ==
    [][
        (state = "None" /\ state' = "InProgress") =>
            startAnchor' = endAnchor'
    ]_vars

THEOREM StartAnchorsEqual == Spec => StartSetsBothAnchors

\* Completing a selection doesn't change the anchors
CompletePreservesAnchors ==
    [][
        (state = "InProgress" /\ state' = "Complete") =>
            (startAnchor' = startAnchor /\ endAnchor' = endAnchor)
    ]_vars

THEOREM CompleteKeepsAnchors == Spec => CompletePreservesAnchors

(***************************************************************************)
(* MODEL CHECKING CONFIGURATION                                             *)
(*                                                                          *)
(* For tractable model checking, use small constants:                       *)
(* MaxRows = 2, MaxCols = 3                                                 *)
(* SelectionTypes = {"Simple", "Block", "Semantic", "Lines"}                *)
(* Sides = {"Left", "Right"}                                                *)
(***************************************************************************)

==========================================================================
