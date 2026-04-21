------------------------------ MODULE Editor ------------------------------
(***************************************************************************)
(* TLA+ Specification for dTerm Built-in Editor                            *)
(*                                                                         *)
(* This specification defines the editor state machine:                    *)
(* - Buffer management (simplified as sequence of line lengths)            *)
(* - Cursor positioning with preferred column tracking                     *)
(* - Undo/redo with grouping and coalescing                               *)
(* - Modified flag tracking                                                *)
(*                                                                         *)
(* Key invariants:                                                         *)
(* - Cursor always valid: line < line_count, column <= line_length        *)
(* - Group depth >= 0 (no negative nesting)                               *)
(* - Undo/redo symmetry: undo then redo restores state                    *)
(* - Modified flag correct: tracks whether at saved state                 *)
(*                                                                         *)
(* This spec would have caught bugs #88, #89, #95 through invariant       *)
(* violations on cursor bounds after delete operations.                    *)
(*                                                                         *)
(* Reference: crates/dterm-core/src/editor/mod.rs, undo.rs                *)
(***************************************************************************)

EXTENDS Integers, Naturals, Sequences, FiniteSets

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)

CONSTANTS
    MaxLines,           \* Maximum number of lines (for bounded checking)
    MaxLineLen,         \* Maximum line length (for bounded checking)
    MaxUndoDepth,       \* Maximum undo/redo stack depth
    MaxGroupDepth,      \* Maximum undo group nesting depth
    MaxChangeSize       \* Maximum change size (chars inserted/deleted)

\* Constraint assumptions for model checking
ASSUME MaxLines \in Nat /\ MaxLines > 0
ASSUME MaxLineLen \in Nat /\ MaxLineLen >= 0
ASSUME MaxUndoDepth \in Nat /\ MaxUndoDepth > 0
ASSUME MaxGroupDepth \in Nat /\ MaxGroupDepth > 0
ASSUME MaxChangeSize \in Nat /\ MaxChangeSize > 0

(***************************************************************************)
(* TYPE DEFINITIONS                                                        *)
(***************************************************************************)

\* Valid line indices (1-indexed, matching cursorLine)
ValidLineIdx == 1..MaxLines

\* Valid column indices (0-indexed, inclusive of line end)
ValidColIdx == 0..MaxLineLen

\* Change kinds
ChangeKinds == {"Insert", "Delete"}

\* An undo entry: kind, offset, length, cursor_before
\* Simplified: we track change type and cursor state
UndoEntries == [kind: ChangeKinds, cursorLine: ValidLineIdx, cursorCol: ValidColIdx]

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES
    \* Buffer state: sequence of line lengths (simplified from actual text)
    \* lineLengths[i] = length of line i (excluding newline)
    lineLengths,

    \* Cursor position
    cursorLine,
    cursorCol,

    \* Preferred column (for vertical movement across varying line lengths)
    preferredCol,

    \* Undo/redo stacks (sequences of undo entries)
    undoStack,
    redoStack,

    \* Undo grouping state
    groupDepth,
    groupChanges,       \* Accumulated changes during group

    \* Modified flag tracking
    modified,
    savedUndoDepth,     \* Undo depth at last save (or -1 if never saved)
    branchedSinceSave   \* True if new changes made after undo

vars == <<lineLengths, cursorLine, cursorCol, preferredCol,
          undoStack, redoStack, groupDepth, groupChanges,
          modified, savedUndoDepth, branchedSinceSave>>

(***************************************************************************)
(* HELPER DEFINITIONS                                                      *)
(***************************************************************************)

\* Number of lines in buffer (always at least 1)
LineCount == Len(lineLengths)

\* Length of a specific line
LineLength(line) ==
    IF line >= 1 /\ line <= LineCount
    THEN lineLengths[line]
    ELSE 0

\* Check if cursor position is valid
ValidCursor(line, col) ==
    /\ line >= 1 /\ line <= LineCount
    /\ col >= 0 /\ col <= LineLength(line)

\* Check if a line index is valid (1-indexed for sequences)
ValidLine(line) == line >= 1 /\ line <= LineCount

\* Clamp line to valid range
ClampLine(line) ==
    IF line < 1 THEN 1
    ELSE IF line > LineCount THEN LineCount
    ELSE line

\* Clamp column to valid range for a line (line must be valid)
ClampCol(line, col) ==
    LET validLine == ClampLine(line)
    IN IF col < 0 THEN 0
       ELSE IF col > LineLength(validLine) THEN LineLength(validLine)
       ELSE col

\* Check if at saved state
\* Must account for pending changes in groupChanges during active grouping
IsAtSavedState ==
    /\ savedUndoDepth >= 0
    /\ ~branchedSinceSave
    /\ Len(undoStack) = savedUndoDepth
    /\ groupChanges = <<>>  \* No pending grouped changes

\* Group change accumulator.
\*
\* We only track the *first* change in an active group to avoid combinatorial
\* explosion from modeling long sequences of grouped edits. This is sufficient
\* for the spec's grouping semantics because only the first change is used to
\* construct the single committed undo entry at EndGroup.
RecordGroupChange(entry) ==
    IF groupChanges = <<>> THEN <<entry>> ELSE groupChanges

\* Min helper
Min(a, b) == IF a < b THEN a ELSE b

\* Max helper
Max(a, b) == IF a > b THEN a ELSE b

(***************************************************************************)
(* TYPE INVARIANT                                                          *)
(***************************************************************************)

TypeInvariant ==
    \* Buffer: sequence of non-negative line lengths
    /\ lineLengths \in Seq(0..MaxLineLen)
    /\ Len(lineLengths) >= 1
    /\ Len(lineLengths) <= MaxLines

    \* Cursor: valid position
    /\ cursorLine \in 1..MaxLines
    /\ cursorCol \in 0..MaxLineLen

    \* Preferred column
    /\ preferredCol \in 0..MaxLineLen

    \* Undo/redo stacks bounded
    /\ Len(undoStack) <= MaxUndoDepth
    /\ Len(redoStack) <= MaxUndoDepth

    \* Group state
    /\ groupDepth \in 0..MaxGroupDepth
    /\ groupChanges \in Seq(UndoEntries)
    \* groupChanges: only the first change in the current group is tracked to
    \* keep the model finite and tractable.
    /\ Len(groupChanges) <= 1

    \* Modified flag state
    /\ modified \in BOOLEAN
    /\ savedUndoDepth \in -1..MaxUndoDepth
    /\ branchedSinceSave \in BOOLEAN

(***************************************************************************)
(* SAFETY PROPERTIES                                                       *)
(***************************************************************************)

\* CRITICAL: Cursor always within valid bounds
\* This is the invariant that would catch bugs #88, #89, #95
CursorValid ==
    /\ cursorLine >= 1
    /\ cursorLine <= LineCount
    /\ cursorCol >= 0
    /\ cursorCol <= LineLength(cursorLine)

\* Group depth never negative
GroupDepthNonNegative == groupDepth >= 0

\* Modified flag is correct
ModifiedFlagCorrect ==
    modified = ~IsAtSavedState

\* Combined safety
Safety ==
    /\ CursorValid
    /\ GroupDepthNonNegative
    /\ ModifiedFlagCorrect

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)

Init ==
    \* Start with single empty line
    /\ lineLengths = <<0>>

    \* Cursor at start
    /\ cursorLine = 1
    /\ cursorCol = 0
    /\ preferredCol = 0

    \* Empty undo/redo
    /\ undoStack = <<>>
    /\ redoStack = <<>>

    \* No grouping
    /\ groupDepth = 0
    /\ groupChanges = <<>>

    \* Clean state (conceptually "saved")
    /\ modified = FALSE
    /\ savedUndoDepth = 0
    /\ branchedSinceSave = FALSE

(***************************************************************************)
(* BUFFER OPERATIONS                                                       *)
(***************************************************************************)

\* Insert chars at cursor position
\* Simplified: just increases line length or adds newline
InsertChars(nChars) ==
    LET entry == [kind |-> "Insert",
                  cursorLine |-> cursorLine,
                  cursorCol |-> cursorCol]
        willTrim == groupDepth = 0 /\ Len(undoStack) >= MaxUndoDepth
        \* Trimming loses saved state if we had one (savedUndoDepth >= 0)
        trimCausesBranch == willTrim /\ savedUndoDepth >= 0
    IN
    /\ nChars > 0
    /\ nChars <= MaxChangeSize
    /\ LineLength(cursorLine) + nChars <= MaxLineLen

    \* Record undo entry and handle stack trimming
    /\ IF groupDepth > 0
       THEN /\ groupChanges' = RecordGroupChange(entry)
            /\ UNCHANGED undoStack
       ELSE /\ undoStack' = IF willTrim
                            THEN Tail(undoStack) \o <<entry>>
                            ELSE Append(undoStack, entry)
            /\ UNCHANGED groupChanges

    \* Update buffer: increase line length
    /\ lineLengths' = [lineLengths EXCEPT ![cursorLine] = @ + nChars]

    \* Move cursor forward
    /\ cursorCol' = cursorCol + nChars
    /\ preferredCol' = cursorCol + nChars
    /\ UNCHANGED cursorLine

    \* Clear redo, mark branched if needed, handle trim-induced branch
    /\ IF redoStack # <<>> \/ trimCausesBranch
       THEN branchedSinceSave' = TRUE
       ELSE UNCHANGED branchedSinceSave
    /\ redoStack' = <<>>
    /\ modified' = TRUE
    /\ UNCHANGED <<savedUndoDepth, groupDepth>>

\* Insert newline at cursor position
InsertNewline ==
    LET entry == [kind |-> "Insert",
                  cursorLine |-> cursorLine,
                  cursorCol |-> cursorCol]
        willTrim == groupDepth = 0 /\ Len(undoStack) >= MaxUndoDepth
        trimCausesBranch == willTrim /\ savedUndoDepth >= 0
        charsAfter == LineLength(cursorLine) - cursorCol
    IN
    /\ LineCount < MaxLines

    \* Record undo entry
    /\ IF groupDepth > 0
       THEN /\ groupChanges' = RecordGroupChange(entry)
            /\ UNCHANGED undoStack
       ELSE /\ undoStack' = IF willTrim
                            THEN Tail(undoStack) \o <<entry>>
                            ELSE Append(undoStack, entry)
            /\ UNCHANGED groupChanges

    \* Split line at cursor: chars before cursor stay, chars after go to new line
    /\ LET newLineLengths == [i \in 1..(LineCount + 1) |->
               IF i < cursorLine THEN lineLengths[i]
               ELSE IF i = cursorLine THEN cursorCol  \* Truncate current line
               ELSE IF i = cursorLine + 1 THEN charsAfter  \* New line with rest
               ELSE lineLengths[i - 1]]  \* Shift subsequent lines
       IN lineLengths' = newLineLengths

    \* Cursor moves to start of new line
    /\ cursorLine' = cursorLine + 1
    /\ cursorCol' = 0
    /\ preferredCol' = 0

    \* Clear redo, mark branched (including trim-induced branch)
    /\ IF redoStack # <<>> \/ trimCausesBranch
       THEN branchedSinceSave' = TRUE
       ELSE UNCHANGED branchedSinceSave
    /\ redoStack' = <<>>
    /\ modified' = TRUE
    /\ UNCHANGED <<savedUndoDepth, groupDepth>>

\* Delete char before cursor (backspace)
\* This is where bugs #88, #89 were found - cursor not properly adjusted
DeleteCharBefore ==
    LET entry == [kind |-> "Delete",
                  cursorLine |-> cursorLine,
                  cursorCol |-> cursorCol]
        willTrim == groupDepth = 0 /\ Len(undoStack) >= MaxUndoDepth
        trimCausesBranch == willTrim /\ savedUndoDepth >= 0
    IN
    /\ cursorCol > 0 \/ cursorLine > 1  \* Not at start of buffer
    \* If at BOL and joining with previous line, ensure result doesn't exceed MaxLineLen
    /\ (cursorCol > 0 \/
        LineLength(cursorLine - 1) + LineLength(cursorLine) <= MaxLineLen)

    \* Record undo entry
    /\ IF groupDepth > 0
       THEN /\ groupChanges' = RecordGroupChange(entry)
            /\ UNCHANGED undoStack
       ELSE /\ undoStack' = IF willTrim
                            THEN Tail(undoStack) \o <<entry>>
                            ELSE Append(undoStack, entry)
            /\ UNCHANGED groupChanges

    /\ IF cursorCol > 0
       THEN \* Delete within line: decrease line length
            /\ lineLengths' = [lineLengths EXCEPT ![cursorLine] = @ - 1]
            /\ cursorCol' = cursorCol - 1
            /\ preferredCol' = cursorCol - 1
            /\ UNCHANGED cursorLine
       ELSE \* Delete newline: join with previous line
            /\ LET prevLineLen == LineLength(cursorLine - 1)
                   currLineLen == LineLength(cursorLine)
                   newLineLengths == [i \in 1..(LineCount - 1) |->
                       IF i < cursorLine - 1 THEN lineLengths[i]
                       ELSE IF i = cursorLine - 1 THEN prevLineLen + currLineLen
                       ELSE lineLengths[i + 1]]
               IN lineLengths' = newLineLengths
            /\ cursorLine' = cursorLine - 1
            /\ cursorCol' = LineLength(cursorLine - 1)
            /\ preferredCol' = LineLength(cursorLine - 1)

    \* Clear redo, mark branched (including trim-induced branch)
    /\ IF redoStack # <<>> \/ trimCausesBranch
       THEN branchedSinceSave' = TRUE
       ELSE UNCHANGED branchedSinceSave
    /\ redoStack' = <<>>
    /\ modified' = TRUE
    /\ UNCHANGED <<savedUndoDepth, groupDepth>>

\* Delete char at cursor (delete key)
DeleteCharAt ==
    LET entry == [kind |-> "Delete",
                  cursorLine |-> cursorLine,
                  cursorCol |-> cursorCol]
        willTrim == groupDepth = 0 /\ Len(undoStack) >= MaxUndoDepth
        trimCausesBranch == willTrim /\ savedUndoDepth >= 0
    IN
    /\ cursorCol < LineLength(cursorLine) \/ cursorLine < LineCount  \* Not at end of buffer
    \* If at EOL and joining lines, ensure result doesn't exceed MaxLineLen
    /\ (cursorCol < LineLength(cursorLine) \/
        LineLength(cursorLine) + LineLength(cursorLine + 1) <= MaxLineLen)

    \* Record undo entry
    /\ IF groupDepth > 0
       THEN /\ groupChanges' = RecordGroupChange(entry)
            /\ UNCHANGED undoStack
       ELSE /\ undoStack' = IF willTrim
                            THEN Tail(undoStack) \o <<entry>>
                            ELSE Append(undoStack, entry)
            /\ UNCHANGED groupChanges

    /\ IF cursorCol < LineLength(cursorLine)
       THEN \* Delete within line
            /\ lineLengths' = [lineLengths EXCEPT ![cursorLine] = @ - 1]
            /\ UNCHANGED <<cursorLine, cursorCol>>
       ELSE \* Delete newline: join with next line
            /\ LET currLineLen == LineLength(cursorLine)
                   nextLineLen == LineLength(cursorLine + 1)
                   newLineLengths == [i \in 1..(LineCount - 1) |->
                       IF i < cursorLine THEN lineLengths[i]
                       ELSE IF i = cursorLine THEN currLineLen + nextLineLen
                       ELSE lineLengths[i + 1]]
               IN lineLengths' = newLineLengths
            /\ UNCHANGED <<cursorLine, cursorCol>>

    \* Cursor stays in place for delete
    /\ UNCHANGED preferredCol

    \* Clear redo, mark branched (including trim-induced branch)
    /\ IF redoStack # <<>> \/ trimCausesBranch
       THEN branchedSinceSave' = TRUE
       ELSE UNCHANGED branchedSinceSave
    /\ redoStack' = <<>>
    /\ modified' = TRUE
    /\ UNCHANGED <<savedUndoDepth, groupDepth>>

(***************************************************************************)
(* CURSOR MOVEMENT OPERATIONS                                              *)
(***************************************************************************)

\* Move cursor left
CursorLeft ==
    /\ cursorCol > 0 \/ cursorLine > 1
    /\ IF cursorCol > 0
       THEN /\ cursorCol' = cursorCol - 1
            /\ UNCHANGED cursorLine
       ELSE /\ cursorLine' = cursorLine - 1
            /\ cursorCol' = LineLength(cursorLine - 1)
    /\ preferredCol' = cursorCol'
    /\ UNCHANGED <<lineLengths, undoStack, redoStack, groupDepth, groupChanges,
                   modified, savedUndoDepth, branchedSinceSave>>

\* Move cursor right
CursorRight ==
    /\ cursorCol < LineLength(cursorLine) \/ cursorLine < LineCount
    /\ IF cursorCol < LineLength(cursorLine)
       THEN /\ cursorCol' = cursorCol + 1
            /\ UNCHANGED cursorLine
       ELSE /\ cursorLine' = cursorLine + 1
            /\ cursorCol' = 0
    /\ preferredCol' = cursorCol'
    /\ UNCHANGED <<lineLengths, undoStack, redoStack, groupDepth, groupChanges,
                   modified, savedUndoDepth, branchedSinceSave>>

\* Move cursor up (with preferred column)
CursorUp ==
    /\ cursorLine > 1
    /\ cursorLine' = cursorLine - 1
    \* Use preferred column, clamped to new line length
    /\ cursorCol' = Min(preferredCol, LineLength(cursorLine - 1))
    /\ UNCHANGED <<lineLengths, preferredCol, undoStack, redoStack, groupDepth,
                   groupChanges, modified, savedUndoDepth, branchedSinceSave>>

\* Move cursor down (with preferred column)
CursorDown ==
    /\ cursorLine < LineCount
    /\ cursorLine' = cursorLine + 1
    \* Use preferred column, clamped to new line length
    /\ cursorCol' = Min(preferredCol, LineLength(cursorLine + 1))
    /\ UNCHANGED <<lineLengths, preferredCol, undoStack, redoStack, groupDepth,
                   groupChanges, modified, savedUndoDepth, branchedSinceSave>>

\* Move cursor to line start
CursorHome ==
    /\ cursorCol' = 0
    /\ preferredCol' = 0
    /\ UNCHANGED <<lineLengths, cursorLine, undoStack, redoStack, groupDepth,
                   groupChanges, modified, savedUndoDepth, branchedSinceSave>>

\* Move cursor to line end
CursorEnd ==
    /\ cursorCol' = LineLength(cursorLine)
    /\ preferredCol' = LineLength(cursorLine)
    /\ UNCHANGED <<lineLengths, cursorLine, undoStack, redoStack, groupDepth,
                   groupChanges, modified, savedUndoDepth, branchedSinceSave>>

(***************************************************************************)
(* UNDO/REDO OPERATIONS                                                    *)
(***************************************************************************)

\* Undo last change (simplified: restores cursor, clamped to valid bounds)
\* Note: Real implementation restores buffer too, spec abstracts buffer content
Undo ==
    /\ undoStack # <<>>
    /\ groupDepth = 0  \* Can't undo while in group
    /\ LET entry == Head(undoStack)
           \* Clamp cursor to valid bounds (spec doesn't track buffer restoration)
           clampedLine == ClampLine(entry.cursorLine)
           clampedCol == ClampCol(clampedLine, entry.cursorCol)
       IN /\ cursorLine' = clampedLine
          /\ cursorCol' = clampedCol
          /\ preferredCol' = clampedCol
          \* Move entry to redo stack
          /\ redoStack' = IF Len(redoStack) >= MaxUndoDepth
                          THEN Tail(redoStack) \o <<entry>>
                          ELSE Append(redoStack, entry)
    /\ undoStack' = Tail(undoStack)
    \* Update modified based on new undo depth
    /\ modified' = ~(savedUndoDepth >= 0 /\ ~branchedSinceSave /\ Len(undoStack) - 1 = savedUndoDepth)
    /\ UNCHANGED <<lineLengths, groupDepth, groupChanges, savedUndoDepth, branchedSinceSave>>

\* Redo last undone change
Redo ==
    /\ redoStack # <<>>
    /\ groupDepth = 0  \* Can't redo while in group
    /\ LET entry == Head(redoStack)
           \* Clamp cursor to valid bounds (spec doesn't track buffer restoration)
           clampedLine == ClampLine(entry.cursorLine)
           clampedCol == ClampCol(clampedLine, entry.cursorCol)
       IN /\ cursorLine' = clampedLine
          /\ cursorCol' = clampedCol
          /\ preferredCol' = clampedCol
          \* Move entry to undo stack
          /\ undoStack' = IF Len(undoStack) >= MaxUndoDepth
                          THEN Tail(undoStack) \o <<entry>>
                          ELSE Append(undoStack, entry)
    /\ redoStack' = Tail(redoStack)
    \* Update modified
    /\ modified' = ~(savedUndoDepth >= 0 /\ ~branchedSinceSave /\ Len(undoStack) + 1 = savedUndoDepth)
    /\ UNCHANGED <<lineLengths, groupDepth, groupChanges, savedUndoDepth, branchedSinceSave>>

(***************************************************************************)
(* UNDO GROUPING OPERATIONS                                                *)
(***************************************************************************)

\* Begin undo group
BeginGroup ==
    /\ groupDepth < MaxGroupDepth
    /\ groupDepth' = groupDepth + 1
    /\ UNCHANGED <<lineLengths, cursorLine, cursorCol, preferredCol,
                   undoStack, redoStack, groupChanges,
                   modified, savedUndoDepth, branchedSinceSave>>

\* End undo group (commits accumulated changes as one entry)
EndGroup ==
    LET isOuterGroup == groupDepth = 1
        hasChanges == groupChanges # <<>>
        willCommit == isOuterGroup /\ hasChanges
        willTrim == willCommit /\ Len(undoStack) >= MaxUndoDepth
        trimCausesBranch == willTrim /\ savedUndoDepth >= 0
    IN
    /\ groupDepth > 0
    /\ groupDepth' = groupDepth - 1
    \* Only commit on outermost group
    /\ IF willCommit
       THEN \* Commit grouped changes as single entry
            /\ LET firstChange == Head(groupChanges)
                   entry == [kind |-> firstChange.kind,
                             cursorLine |-> firstChange.cursorLine,
                             cursorCol |-> firstChange.cursorCol]
               IN undoStack' = IF willTrim
                               THEN Tail(undoStack) \o <<entry>>
                               ELSE Append(undoStack, entry)
            /\ groupChanges' = <<>>
       ELSE /\ UNCHANGED <<undoStack, groupChanges>>
    \* Mark branched if trimming loses saved state
    /\ IF trimCausesBranch
       THEN branchedSinceSave' = TRUE
       ELSE UNCHANGED branchedSinceSave
    /\ UNCHANGED <<lineLengths, cursorLine, cursorCol, preferredCol,
                   redoStack, modified, savedUndoDepth>>

\* Cancel undo group (discards accumulated changes)
\* If groupChanges non-empty, we've branched from saved state (can't undo back)
CancelGroup ==
    /\ groupDepth > 0
    /\ groupDepth' = 0
    /\ groupChanges' = <<>>
    /\ IF groupChanges # <<>>
       THEN branchedSinceSave' = TRUE
       ELSE UNCHANGED branchedSinceSave
    /\ UNCHANGED <<lineLengths, cursorLine, cursorCol, preferredCol,
                   undoStack, redoStack, modified, savedUndoDepth>>

(***************************************************************************)
(* SAVE OPERATIONS                                                         *)
(***************************************************************************)

\* Mark current state as saved
\* Only valid when not in a group (groupChanges must be empty)
MarkSaved ==
    /\ groupDepth = 0  \* Can't save while grouping
    /\ savedUndoDepth' = Len(undoStack)
    /\ branchedSinceSave' = FALSE
    /\ modified' = FALSE
    /\ UNCHANGED <<lineLengths, cursorLine, cursorCol, preferredCol,
                   undoStack, redoStack, groupDepth, groupChanges>>

(***************************************************************************)
(* LOAD OPERATIONS                                                         *)
(***************************************************************************)

\* Load new content (clear and reset)
LoadContent(nLines, lineLens) ==
    /\ nLines >= 1
    /\ nLines <= MaxLines
    /\ Len(lineLens) = nLines
    /\ \A i \in 1..nLines : lineLens[i] \in 0..MaxLineLen
    /\ lineLengths' = lineLens
    /\ cursorLine' = 1
    /\ cursorCol' = 0
    /\ preferredCol' = 0
    /\ undoStack' = <<>>
    /\ redoStack' = <<>>
    /\ groupDepth' = 0
    /\ groupChanges' = <<>>
    /\ modified' = FALSE
    /\ savedUndoDepth' = 0
    /\ branchedSinceSave' = FALSE

(***************************************************************************)
(* NEXT STATE RELATION                                                     *)
(***************************************************************************)

Next ==
    \* Insert operations
    \/ \E n \in 1..MaxChangeSize : InsertChars(n)
    \/ InsertNewline

    \* Delete operations
    \/ DeleteCharBefore
    \/ DeleteCharAt

    \* Cursor movement
    \/ CursorLeft
    \/ CursorRight
    \/ CursorUp
    \/ CursorDown
    \/ CursorHome
    \/ CursorEnd

    \* Undo/redo
    \/ Undo
    \/ Redo

    \* Grouping
    \/ BeginGroup
    \/ EndGroup
    \/ CancelGroup

    \* Save
    \/ MarkSaved

    \* Load (bounded for model checking)
    \/ \E lens \in UNION {[1..n -> 0..MaxLineLen] : n \in 1..MaxLines} :
           LoadContent(Len(lens), lens)

(***************************************************************************)
(* SPECIFICATION                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* THEOREMS                                                                *)
(***************************************************************************)

\* Type invariant always holds
THEOREM TypeSafe == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyHolds == Spec => []Safety

\* Cursor is always valid after any operation
THEOREM CursorAlwaysValid == Spec => []CursorValid

\* Group depth never negative
THEOREM GroupDepthValid == Spec => []GroupDepthNonNegative

(***************************************************************************)
(* STATE MACHINE THEOREMS                                                  *)
(***************************************************************************)

\* Undo/redo are symmetric: if we can undo then redo, we return to same stack sizes
UndoRedoSymmetric ==
    [][
        (undoStack # <<>> /\ undoStack' # undoStack /\ redoStack' = Append(redoStack, Head(undoStack)))
        =>
        (Len(undoStack') = Len(undoStack) - 1 /\ Len(redoStack') = Len(redoStack) + 1)
    ]_vars

THEOREM UndoRedoIsSymmetric == Spec => UndoRedoSymmetric

\* Grouping always balanced: BeginGroup increments, EndGroup decrements
GroupingBalanced ==
    [][
        \/ groupDepth' = groupDepth
        \/ (groupDepth' = groupDepth + 1)  \* BeginGroup
        \/ (groupDepth' = groupDepth - 1)  \* EndGroup
        \/ (groupDepth' = 0 /\ groupDepth > 0)  \* CancelGroup
    ]_vars

THEOREM GroupingIsBalanced == Spec => GroupingBalanced

\* After save, modified is false
SaveClearsModified ==
    [][savedUndoDepth' # savedUndoDepth => modified' = FALSE]_vars

THEOREM SaveMarksClean == Spec => SaveClearsModified

(***************************************************************************)
(* MODEL CHECKING CONFIGURATION                                            *)
(*                                                                         *)
(* For tractable model checking, use small constants:                      *)
(* MaxLines = 3, MaxLineLen = 5, MaxUndoDepth = 3                          *)
(* MaxGroupDepth = 2, MaxChangeSize = 2                                    *)
(*                                                                         *)
(* This gives a manageable state space while still exercising:             *)
(* - Multi-line operations                                                 *)
(* - Cursor movement at boundaries                                         *)
(* - Undo/redo with grouping                                               *)
(* - Insert and delete operations                                          *)
(***************************************************************************)

=============================================================================
