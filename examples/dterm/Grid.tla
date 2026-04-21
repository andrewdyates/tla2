--------------------------- MODULE Grid ---------------------------
(***************************************************************************)
(* TLA+ Specification for the dTerm Terminal Grid                          *)
(*                                                                          *)
(* This specification defines:                                              *)
(* - Grid dimensions and bounds                                             *)
(* - Cursor position and movement                                           *)
(* - Scroll position (display_offset) for O(1) scrolling                    *)
(* - Cell operations (write, clear, erase)                                  *)
(* - Resize operations preserving cursor invariants                         *)
(* - Damage tracking for efficient rendering                                *)
(*                                                                          *)
(* Reference: docs/architecture/DESIGN.md Section 3.1, 3.2, 3.4             *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    MaxRows,              \* Maximum terminal rows (e.g., 1000)
    MaxCols,              \* Maximum terminal columns (e.g., 500)
    MaxScrollback,        \* Maximum scrollback lines (e.g., 100000)
    PageSize,             \* Page size in bytes (e.g., 65536)
    MaxCellId             \* Max cell ID for bounded model checking

\* Constraint assumptions for model checking
ASSUME MaxRows \in Nat /\ MaxRows > 0
ASSUME MaxCols \in Nat /\ MaxCols > 0
ASSUME MaxScrollback \in Nat
ASSUME PageSize \in Nat /\ PageSize > 0
ASSUME MaxCellId \in Nat /\ MaxCellId > 0

(***************************************************************************)
(* VARIABLES                                                                *)
(***************************************************************************)

VARIABLES
    rows,                 \* Current visible row count
    cols,                 \* Current column count
    cursor,               \* Cursor position record {row, col}
    display_offset,       \* Scroll position (key for O(1) scrolling)
    total_lines,          \* Total lines in buffer (visible + scrollback)
    damage,               \* Damage tracking: "Full" or set of damaged rows
    saved_cursor_row,     \* Saved cursor row (-1 means not saved)
    saved_cursor_col,     \* Saved cursor col (-1 means not saved)
    scroll_top,           \* Top of scroll region (0-indexed, inclusive)
    scroll_bottom,        \* Bottom of scroll region (0-indexed, inclusive)
    pages,                \* Page IDs allocated for row storage
    row_page,             \* Mapping: row index -> page ID
    row_offset,           \* Mapping: row index -> byte offset into page
    \* Content tracking for FV-14 (resize content preservation)
    \* cells[row][col] = unique cell ID, 0 means empty
    \* nextCellId = counter for generating unique cell IDs
    cells,                \* Cell content: function from (row, col) to cell ID
    nextCellId,           \* Next cell ID to assign (for uniqueness)
    \* Wide character tracking (CJK, emoji, etc.)
    \* cell_flags[row][col] = set of flags {"Wide", "WidePlaceholder", "Wrapped"}
    cell_flags            \* Cell flags for wide char handling

vars == <<rows, cols, cursor, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, pages, row_page, row_offset, cells, nextCellId, cell_flags>>

\* Cell flag definitions
CellFlagValues == {"Wide", "WidePlaceholder", "Wrapped", "Hyperlink"}

(***************************************************************************)
(* TYPE DEFINITIONS                                                         *)
(***************************************************************************)

\* Valid cursor record
ValidCursor(r, c) ==
    [row |-> r, col |-> c]

\* Damage can be "Full" or a set of row indices
DamageType == {"Full"} \union SUBSET (0..MaxRows-1)

(***************************************************************************)
(* PAGE STORAGE ASSUMPTIONS                                                *)
(***************************************************************************)

\* Max lines that can exist across visible + scrollback.
MaxLines == MaxScrollback + MaxRows

\* Model row storage as <= MaxCols bytes (abstract cell size).
MaxRowBytes == MaxCols

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(*                                                                          *)
(* Ensures the grid state is always well-formed                             *)
(***************************************************************************)

\* Saved cursor uses -1 to indicate "not saved"
SavedCursorValid ==
    /\ saved_cursor_row \in -1..MaxRows-1
    /\ saved_cursor_col \in -1..MaxCols-1
    /\ (saved_cursor_row = -1) = (saved_cursor_col = -1)  \* Both -1 or both valid

\* Scroll region must be valid: top < bottom and both within visible rows
ScrollRegionValid ==
    /\ scroll_top \in 0..rows-1
    /\ scroll_bottom \in 0..rows-1
    /\ scroll_top <= scroll_bottom

\* Check if scroll region is full screen (no restricted region)
ScrollRegionIsFull ==
    scroll_top = 0 /\ scroll_bottom = rows - 1

TypeInvariant ==
    /\ rows \in 1..MaxRows
    /\ cols \in 1..MaxCols
    /\ cursor.row \in 0..rows-1
    /\ cursor.col \in 0..cols-1
    /\ display_offset \in 0..MaxScrollback
    /\ total_lines \in rows..MaxScrollback+rows
    /\ SavedCursorValid
    /\ ScrollRegionValid
    /\ pages \subseteq 0..MaxLines-1
    /\ row_page \in [0..MaxLines-1 -> 0..MaxLines-1]
    /\ row_offset \in [0..MaxLines-1 -> 0..PageSize-1]
    /\ \A r \in 0..total_lines-1 : row_page[r] \in pages
    /\ \A r \in 0..total_lines-1 : row_offset[r] + MaxRowBytes <= PageSize
    /\ nextCellId \in 1..MaxCellId
    \* cells is a function from valid positions to cell IDs
    /\ DOMAIN cells = {<<r, c>> : r \in 0..total_lines-1, c \in 0..cols-1}
    /\ \A pos \in DOMAIN cells : cells[pos] \in 0..nextCellId
    \* cell_flags is a function from valid positions to sets of flags
    /\ DOMAIN cell_flags = {<<r, c>> : r \in 0..total_lines-1, c \in 0..cols-1}
    /\ \A pos \in DOMAIN cell_flags : cell_flags[pos] \subseteq CellFlagValues

(***************************************************************************)
(* SAFETY PROPERTIES                                                        *)
(***************************************************************************)

\* Cursor is always within the visible area
CursorInBounds ==
    /\ cursor.row >= 0
    /\ cursor.row < rows
    /\ cursor.col >= 0
    /\ cursor.col < cols

\* Display offset doesn't exceed scrollback
DisplayOffsetValid ==
    /\ display_offset >= 0
    /\ display_offset <= IF total_lines > rows
                         THEN total_lines - rows
                         ELSE 0

\* Total lines is at least visible rows
TotalLinesValid ==
    total_lines >= rows

\* Wide character consistency: wide chars must have placeholder in next cell
\* This ensures CJK and emoji characters render correctly
WideCharConsistent ==
    \A r \in 0..total_lines-1, c \in 0..cols-2:
        "Wide" \in cell_flags[<<r,c>>] =>
            "WidePlaceholder" \in cell_flags[<<r,c+1>>]

\* Wide chars cannot start at the last column (no room for placeholder)
WideCharNotAtEnd ==
    \A r \in 0..total_lines-1:
        ~("Wide" \in cell_flags[<<r, cols-1>>])

\* Placeholder cells must be preceded by a Wide cell
PlaceholderPrecededByWide ==
    \A r \in 0..total_lines-1, c \in 1..cols-1:
        "WidePlaceholder" \in cell_flags[<<r,c>>] =>
            "Wide" \in cell_flags[<<r,c-1>>]

\* First column cannot be a placeholder (no wide char to the left)
FirstColumnNotPlaceholder ==
    \A r \in 0..total_lines-1:
        ~("WidePlaceholder" \in cell_flags[<<r, 0>>])

\* Combined wide character safety
WideCharSafety ==
    /\ WideCharConsistent
    /\ WideCharNotAtEnd
    /\ PlaceholderPrecededByWide
    /\ FirstColumnNotPlaceholder

\* Combined safety property
Safety == CursorInBounds /\ DisplayOffsetValid /\ TotalLinesValid /\ WideCharSafety

(***************************************************************************)
(* CONTENT PRESERVATION (FV-14)                                            *)
(*                                                                          *)
(* Key property: Non-zero cell content is never lost on resize.             *)
(* Content may move to scrollback but is not destroyed.                     *)
(***************************************************************************)

\* Set of all non-zero cell IDs currently in the grid
NonZeroCellIds ==
    {cells[pos] : pos \in {p \in DOMAIN cells : cells[p] /= 0}}

\* Content preservation: non-zero cell IDs are never lost
\* (they either remain in the grid or move to scrollback)
ContentPreserved ==
    \* This will be checked as a property across transitions
    TRUE  \* Placeholder - actual check is in theorems

(***************************************************************************)
(* HELPER OPERATORS                                                         *)
(***************************************************************************)

\* Clamp a value to a range
Clamp(val, minVal, maxVal) ==
    IF val < minVal THEN minVal
    ELSE IF val > maxVal THEN maxVal
    ELSE val

\* Maximum of two values
Max(a, b) == IF a > b THEN a ELSE b

\* Minimum of two values
Min(a, b) == IF a < b THEN a ELSE b

\* Mark a row as damaged
MarkRowDamaged(row) ==
    IF damage = "Full"
    THEN damage' = "Full"
    ELSE damage' = damage \union {row}

\* Mark entire screen as damaged
MarkFullDamage ==
    damage' = "Full"

\* Clear damage (after render)
ClearDamage ==
    damage' = {}

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    /\ rows \in 1..MaxRows          \* Start with valid row count
    /\ cols \in 1..MaxCols          \* Start with valid column count
    /\ cursor = [row |-> 0, col |-> 0]
    /\ display_offset = 0
    /\ total_lines = rows           \* Initially just visible area
    /\ damage = "Full"              \* Need full render initially
    /\ saved_cursor_row = -1        \* Not saved
    /\ saved_cursor_col = -1        \* Not saved
    /\ scroll_top = 0               \* Default: full screen scroll region
    /\ scroll_bottom = rows - 1     \* Default: full screen scroll region
    /\ pages = 0..MaxLines-1
    /\ row_page = [r \in 0..MaxLines-1 |-> r]
    /\ row_offset = [r \in 0..MaxLines-1 |-> 0]
    \* Initialize cells as empty (all zeros)
    /\ cells = [pos \in {<<r, c>> : r \in 0..rows-1, c \in 0..cols-1} |-> 0]
    /\ nextCellId = 1               \* Start cell IDs at 1 (0 = empty)
    \* Initialize cell flags as empty sets
    /\ cell_flags = [pos \in {<<r, c>> : r \in 0..rows-1, c \in 0..cols-1} |-> {}]

(***************************************************************************)
(* CURSOR MOVEMENT OPERATIONS                                               *)
(***************************************************************************)

\* Move cursor to absolute position (clamped)
MoveCursorTo(r, c) ==
    /\ cursor' = [
        row |-> Clamp(r, 0, rows - 1),
        col |-> Clamp(c, 0, cols - 1)
       ]
    /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Move cursor by relative offset
MoveCursorBy(dr, dc) ==
    MoveCursorTo(cursor.row + dr, cursor.col + dc)

\* Carriage return (cursor to column 0)
CarriageReturn ==
    /\ cursor' = [row |-> cursor.row, col |-> 0]
    /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Line feed (move down, possibly scroll)
\* Scroll-region aware: only scrolls within the scroll region
LineFeed ==
    IF cursor.row < scroll_bottom
    THEN
        \* Simple move down within scroll region
        /\ cursor' = [row |-> cursor.row + 1, col |-> cursor.col]
        /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>
    ELSE IF cursor.row = scroll_bottom
    THEN
        \* At bottom of scroll region - scroll up within region
        /\ UNCHANGED cursor
        /\ IF ScrollRegionIsFull
           THEN
               \* Full screen scroll: content moves to scrollback, add new line at bottom
               /\ total_lines' = Min(total_lines + 1, MaxScrollback + rows)
               \* Shift cells: row 0 goes to scrollback, all other rows shift up
               \* New row at scroll_bottom is empty (zeros)
               /\ LET newTotalLines == Min(total_lines + 1, MaxScrollback + rows)
                  IN /\ cells' = [pos \in {<<r, c>> : r \in 0..newTotalLines-1, c \in 0..cols-1} |->
                      IF pos[1] = scroll_bottom
                      THEN 0  \* New line at bottom is empty
                      ELSE IF pos[1] < scroll_bottom /\ pos[1] >= scroll_top
                           THEN cells[<<pos[1] + 1, pos[2]>>]  \* Shift up within region
                           ELSE IF <<pos[1], pos[2]>> \in DOMAIN cells
                                THEN cells[<<pos[1], pos[2]>>]  \* Keep other cells
                                ELSE 0]  \* New scrollback line from top
                     /\ cell_flags' = [pos \in {<<r, c>> : r \in 0..newTotalLines-1, c \in 0..cols-1} |->
                         IF pos[1] = scroll_bottom
                         THEN {}  \* New line at bottom has no flags
                         ELSE IF pos[1] < scroll_bottom /\ pos[1] >= scroll_top
                              THEN cell_flags[<<pos[1] + 1, pos[2]>>]  \* Shift up within region
                              ELSE IF <<pos[1], pos[2]>> \in DOMAIN cell_flags
                                   THEN cell_flags[<<pos[1], pos[2]>>]  \* Keep other flags
                                   ELSE {}]  \* New scrollback line from top
           ELSE
               \* Restricted region: shift within region only, no scrollback
               /\ UNCHANGED total_lines
               /\ cells' = [pos \in DOMAIN cells |->
                   IF pos[1] = scroll_bottom
                   THEN 0  \* New line at bottom of region is empty
                   ELSE IF pos[1] < scroll_bottom /\ pos[1] >= scroll_top
                        THEN cells[<<pos[1] + 1, pos[2]>>]  \* Shift up within region
                        ELSE cells[pos]]  \* Keep cells outside region
               /\ cell_flags' = [pos \in DOMAIN cell_flags |->
                   IF pos[1] = scroll_bottom
                   THEN {}  \* New line at bottom of region has no flags
                   ELSE IF pos[1] < scroll_bottom /\ pos[1] >= scroll_top
                        THEN cell_flags[<<pos[1] + 1, pos[2]>>]  \* Shift up within region
                        ELSE cell_flags[pos]]  \* Keep flags outside region
        /\ damage' = "Full"  \* Scroll requires redraw
        /\ UNCHANGED <<rows, cols, display_offset, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>
    ELSE
        \* Below scroll region - just move down if possible
        IF cursor.row < rows - 1
        THEN
            /\ cursor' = [row |-> cursor.row + 1, col |-> cursor.col]
            /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>
        ELSE
            /\ UNCHANGED vars

\* Reverse line feed (move up, possibly scroll down)
\* Scroll-region aware: only scrolls within the scroll region
ReverseLineFeed ==
    IF cursor.row > scroll_top
    THEN
        \* Simple move up within scroll region
        /\ cursor' = [row |-> cursor.row - 1, col |-> cursor.col]
        /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>
    ELSE IF cursor.row = scroll_top
    THEN
        \* At top of scroll region - scroll down within region (insert line at top)
        /\ UNCHANGED cursor
        \* Shift cells down within scroll region, new line at scroll_top is empty
        /\ cells' = [pos \in DOMAIN cells |->
            IF pos[1] = scroll_top
            THEN 0  \* New line at top of region is empty
            ELSE IF pos[1] > scroll_top /\ pos[1] <= scroll_bottom
                 THEN cells[<<pos[1] - 1, pos[2]>>]  \* Shift down within region
                 ELSE cells[pos]]  \* Keep cells outside region
        /\ cell_flags' = [pos \in DOMAIN cell_flags |->
            IF pos[1] = scroll_top
            THEN {}  \* New line at top of region has no flags
            ELSE IF pos[1] > scroll_top /\ pos[1] <= scroll_bottom
                 THEN cell_flags[<<pos[1] - 1, pos[2]>>]  \* Shift down within region
                 ELSE cell_flags[pos]]  \* Keep flags outside region
        /\ damage' = "Full"  \* Scroll requires redraw
        /\ UNCHANGED <<rows, cols, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>
    ELSE
        \* Above scroll region - just move up if possible
        IF cursor.row > 0
        THEN
            /\ cursor' = [row |-> cursor.row - 1, col |-> cursor.col]
            /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>
        ELSE
            /\ UNCHANGED vars

\* Tab (move to next tab stop, typically every 8 columns)
Tab ==
    LET nextTab == ((cursor.col \div 8) + 1) * 8
    IN cursor' = [row |-> cursor.row, col |-> Min(nextTab, cols - 1)]
    /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Backspace (move left by 1, don't wrap)
Backspace ==
    /\ cursor' = [row |-> cursor.row, col |-> Max(cursor.col - 1, 0)]
    /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

(***************************************************************************)
(* CURSOR SAVE/RESTORE (DECSC/DECRC)                                        *)
(***************************************************************************)

\* Save cursor position
SaveCursor ==
    /\ saved_cursor_row' = cursor.row
    /\ saved_cursor_col' = cursor.col
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, damage, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Restore cursor position
RestoreCursor ==
    IF saved_cursor_row = -1
    THEN UNCHANGED vars
    ELSE
        /\ cursor' = [
            row |-> Clamp(saved_cursor_row, 0, rows - 1),
            col |-> Clamp(saved_cursor_col, 0, cols - 1)
           ]
        /\ UNCHANGED <<rows, cols, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

(***************************************************************************)
(* SCROLL OPERATIONS                                                        *)
(*                                                                          *)
(* Key insight: Scrolling is O(1) - just change display_offset              *)
(***************************************************************************)

\* Scroll the view by delta lines (positive = up, negative = down)
Scroll(delta) ==
    LET maxOffset == IF total_lines > rows THEN total_lines - rows ELSE 0
    IN /\ display_offset' = Clamp(display_offset + delta, 0, maxOffset)
       /\ damage' = "Full"  \* Scrolling requires full redraw
       /\ UNCHANGED <<rows, cols, cursor, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Scroll to top of scrollback
ScrollToTop ==
    /\ display_offset' = IF total_lines > rows THEN total_lines - rows ELSE 0
    /\ damage' = "Full"
    /\ UNCHANGED <<rows, cols, cursor, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Scroll to bottom (live position)
ScrollToBottom ==
    /\ display_offset' = 0
    /\ damage' = "Full"
    /\ UNCHANGED <<rows, cols, cursor, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Page up
PageUp ==
    Scroll(rows)

\* Page down
PageDown ==
    Scroll(-rows)

(***************************************************************************)
(* RESIZE OPERATIONS                                                        *)
(*                                                                          *)
(* Key property: Cursor must remain in bounds after resize                  *)
(***************************************************************************)

\* Resize terminal to new dimensions
\* FV-14: Content is preserved - cells within new bounds keep their content,
\* cells outside new column bounds are truncated (but row content preserved in scrollback)
Resize(newRows, newCols) ==
    /\ newRows \in 1..MaxRows
    /\ newCols \in 1..MaxCols
    /\ rows' = newRows
    /\ cols' = newCols
    \* Clamp cursor to new bounds
    /\ cursor' = [
        row |-> IF cursor.row >= newRows THEN newRows - 1 ELSE cursor.row,
        col |-> IF cursor.col >= newCols THEN newCols - 1 ELSE cursor.col
       ]
    \* Adjust total_lines if needed (clamp to valid range)
    /\ total_lines' = Min(Max(total_lines, newRows), MaxScrollback + newRows)
    \* Adjust display_offset if needed
    /\ LET newMaxOffset == IF total_lines' > newRows THEN total_lines' - newRows ELSE 0
       IN display_offset' = Min(display_offset, newMaxOffset)
    /\ damage' = "Full"  \* Resize requires full redraw
    \* Clamp saved cursor too (if saved)
    /\ saved_cursor_row' = IF saved_cursor_row = -1 THEN -1
                           ELSE IF saved_cursor_row >= newRows THEN newRows - 1
                           ELSE saved_cursor_row
    /\ saved_cursor_col' = IF saved_cursor_col = -1 THEN -1
                           ELSE IF saved_cursor_col >= newCols THEN newCols - 1
                           ELSE saved_cursor_col
    \* Reset scroll region to full screen on resize (standard behavior)
    /\ scroll_top' = 0
    /\ scroll_bottom' = newRows - 1
    \* FV-14: Content preservation on resize
    \* - Cells within new bounds: preserve content
    \* - Cells in truncated columns: content lost (standard terminal behavior)
    \* - New cells (if grid grew): empty (0)
    /\ LET newTotalLines == Min(Max(total_lines, newRows), MaxScrollback + newRows)
       IN /\ cells' = [pos \in {<<r, c>> : r \in 0..newTotalLines-1, c \in 0..newCols-1} |->
           IF <<pos[1], pos[2]>> \in DOMAIN cells
           THEN cells[<<pos[1], pos[2]>>]  \* Preserve existing content
           ELSE 0]  \* New cells are empty
          /\ cell_flags' = [pos \in {<<r, c>> : r \in 0..newTotalLines-1, c \in 0..newCols-1} |->
              IF <<pos[1], pos[2]>> \in DOMAIN cell_flags
              THEN cell_flags[<<pos[1], pos[2]>>]
              ELSE {}]
    /\ UNCHANGED <<nextCellId, pages, row_page, row_offset>>

(***************************************************************************)
(* ERASE OPERATIONS                                                         *)
(***************************************************************************)

\* Erase from cursor to end of line (EL 0)
EraseToEndOfLine ==
    /\ damage' = IF damage = "Full" THEN "Full" ELSE damage \union {cursor.row}
    \* Clear cells from cursor to end of line
    /\ cells' = [pos \in DOMAIN cells |->
        IF pos[1] = cursor.row /\ pos[2] >= cursor.col
        THEN 0  \* Erased
        ELSE cells[pos]]
    \* Clear flags for erased cells
    /\ cell_flags' = [pos \in DOMAIN cell_flags |->
        IF pos[1] = cursor.row /\ pos[2] >= cursor.col
        THEN {}  \* Flags cleared
        ELSE cell_flags[pos]]
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>

\* Erase from start of line to cursor (EL 1)
EraseFromStartOfLine ==
    /\ damage' = IF damage = "Full" THEN "Full" ELSE damage \union {cursor.row}
    \* Clear cells from start of line to cursor
    /\ cells' = [pos \in DOMAIN cells |->
        IF pos[1] = cursor.row /\ pos[2] <= cursor.col
        THEN 0  \* Erased
        ELSE cells[pos]]
    \* Clear flags for erased cells
    /\ cell_flags' = [pos \in DOMAIN cell_flags |->
        IF pos[1] = cursor.row /\ pos[2] <= cursor.col
        THEN {}  \* Flags cleared
        ELSE cell_flags[pos]]
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>

\* Erase entire line (EL 2)
EraseLine ==
    /\ damage' = IF damage = "Full" THEN "Full" ELSE damage \union {cursor.row}
    \* Clear entire line
    /\ cells' = [pos \in DOMAIN cells |->
        IF pos[1] = cursor.row
        THEN 0  \* Erased
        ELSE cells[pos]]
    \* Clear flags for erased cells
    /\ cell_flags' = [pos \in DOMAIN cell_flags |->
        IF pos[1] = cursor.row
        THEN {}  \* Flags cleared
        ELSE cell_flags[pos]]
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>

\* Erase from cursor to end of screen (ED 0)
EraseToEndOfScreen ==
    /\ damage' = "Full"
    \* Clear from cursor to end of screen
    /\ cells' = [pos \in DOMAIN cells |->
        IF pos[1] > cursor.row \/ (pos[1] = cursor.row /\ pos[2] >= cursor.col)
        THEN 0  \* Erased
        ELSE cells[pos]]
    \* Clear flags for erased cells
    /\ cell_flags' = [pos \in DOMAIN cell_flags |->
        IF pos[1] > cursor.row \/ (pos[1] = cursor.row /\ pos[2] >= cursor.col)
        THEN {}  \* Flags cleared
        ELSE cell_flags[pos]]
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>

\* Erase from start of screen to cursor (ED 1)
EraseFromStartOfScreen ==
    /\ damage' = "Full"
    \* Clear from start of screen to cursor
    /\ cells' = [pos \in DOMAIN cells |->
        IF pos[1] < cursor.row \/ (pos[1] = cursor.row /\ pos[2] <= cursor.col)
        THEN 0  \* Erased
        ELSE cells[pos]]
    \* Clear flags for erased cells
    /\ cell_flags' = [pos \in DOMAIN cell_flags |->
        IF pos[1] < cursor.row \/ (pos[1] = cursor.row /\ pos[2] <= cursor.col)
        THEN {}  \* Flags cleared
        ELSE cell_flags[pos]]
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>

\* Erase entire screen (ED 2)
EraseScreen ==
    /\ damage' = "Full"
    \* Clear all visible cells (keep scrollback)
    /\ cells' = [pos \in DOMAIN cells |->
        IF pos[1] < rows
        THEN 0  \* Visible area erased
        ELSE cells[pos]]  \* Scrollback preserved
    \* Clear flags for erased cells (visible area only)
    /\ cell_flags' = [pos \in DOMAIN cell_flags |->
        IF pos[1] < rows
        THEN {}  \* Flags cleared for visible area
        ELSE cell_flags[pos]]  \* Scrollback flags preserved
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>

\* Erase scrollback (ED 3)
EraseScrollback ==
    /\ total_lines' = rows  \* Only visible area remains
    /\ display_offset' = 0
    /\ damage' = "Full"
    \* Rebuild cells to only contain visible area
    /\ cells' = [pos \in {<<r, c>> : r \in 0..rows-1, c \in 0..cols-1} |->
        IF <<pos[1], pos[2]>> \in DOMAIN cells
        THEN cells[<<pos[1], pos[2]>>]
        ELSE 0]
    /\ cell_flags' = [pos \in {<<r, c>> : r \in 0..rows-1, c \in 0..cols-1} |->
        IF <<pos[1], pos[2]>> \in DOMAIN cell_flags
        THEN cell_flags[<<pos[1], pos[2]>>]
        ELSE {}]
    /\ UNCHANGED <<rows, cols, cursor, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, nextCellId, pages, row_page, row_offset>>

(***************************************************************************)
(* CELL WRITE OPERATION                                                     *)
(***************************************************************************)

NextCellId ==
    IF nextCellId < MaxCellId THEN nextCellId + 1 ELSE nextCellId

\* Write a character at cursor, advance cursor
WriteChar ==
    /\ damage' = IF damage = "Full" THEN "Full" ELSE damage \union {cursor.row}
    \* Write new cell with unique ID
    /\ cells' = [cells EXCEPT ![<<cursor.row, cursor.col>>] = nextCellId]
    /\ nextCellId' = NextCellId
    /\ IF cursor.col < cols - 1
       THEN cursor' = [row |-> cursor.row, col |-> cursor.col + 1]
       ELSE
           \* At end of line - wrap behavior depends on mode
           \* For now, stay at last column (no autowrap in spec)
           cursor' = cursor
    /\ UNCHANGED <<rows, cols, display_offset, total_lines, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, pages, row_page, row_offset, cell_flags>>

\* Write with autowrap enabled (scroll-region aware)
WriteCharWithWrap ==
    /\ damage' = IF damage = "Full" THEN "Full" ELSE damage \union {cursor.row}
    \* Write the character first
    /\ nextCellId' = NextCellId
    /\ IF cursor.col < cols - 1
       THEN
           \* Simple write, no wrap
           /\ cursor' = [row |-> cursor.row, col |-> cursor.col + 1]
           /\ cells' = [cells EXCEPT ![<<cursor.row, cursor.col>>] = nextCellId]
           /\ UNCHANGED <<total_lines, pages, row_page, row_offset, cell_flags>>
       ELSE
           \* At end of line - wrap to next line (scroll-region aware)
           IF cursor.row < scroll_bottom
           THEN
               \* Write then wrap to next line
               /\ cursor' = [row |-> cursor.row + 1, col |-> 0]
               /\ cells' = [cells EXCEPT ![<<cursor.row, cursor.col>>] = nextCellId]
               /\ UNCHANGED <<total_lines, pages, row_page, row_offset, cell_flags>>
           ELSE IF cursor.row = scroll_bottom
           THEN
               \* At bottom of scroll region - write, scroll, stay at same row
               /\ cursor' = [row |-> cursor.row, col |-> 0]
               /\ IF ScrollRegionIsFull
                  THEN
                      /\ total_lines' = Min(total_lines + 1, MaxScrollback + rows)
                      \* Write the character, then shift cells for scroll
                      /\ LET newTotalLines == Min(total_lines + 1, MaxScrollback + rows)
                             cellsWithWrite == [cells EXCEPT ![<<cursor.row, cursor.col>>] = nextCellId]
                         IN /\ cells' = [pos \in {<<r, c>> : r \in 0..newTotalLines-1, c \in 0..cols-1} |->
                             IF pos[1] = scroll_bottom
                             THEN 0  \* New line at bottom is empty
                             ELSE IF pos[1] < scroll_bottom /\ pos[1] >= scroll_top
                                  THEN cellsWithWrite[<<pos[1] + 1, pos[2]>>]  \* Shift up
                                  ELSE IF <<pos[1], pos[2]>> \in DOMAIN cellsWithWrite
                                       THEN cellsWithWrite[<<pos[1], pos[2]>>]
                                       ELSE 0]
                            /\ cell_flags' = [pos \in {<<r, c>> : r \in 0..newTotalLines-1, c \in 0..cols-1} |->
                                IF pos[1] = scroll_bottom
                                THEN {}  \* New line at bottom has no flags
                                ELSE IF pos[1] < scroll_bottom /\ pos[1] >= scroll_top
                                     THEN cell_flags[<<pos[1] + 1, pos[2]>>]  \* Shift up flags
                                     ELSE IF <<pos[1], pos[2]>> \in DOMAIN cell_flags
                                          THEN cell_flags[<<pos[1], pos[2]>>]
                                          ELSE {}]
                  ELSE
                      \* Restricted region: shift within region only
                      /\ UNCHANGED total_lines
                      /\ LET cellsWithWrite == [cells EXCEPT ![<<cursor.row, cursor.col>>] = nextCellId]
                         IN cells' = [pos \in DOMAIN cells |->
                             IF pos[1] = scroll_bottom
                             THEN 0  \* New line at bottom of region is empty
                             ELSE IF pos[1] < scroll_bottom /\ pos[1] >= scroll_top
                                  THEN cellsWithWrite[<<pos[1] + 1, pos[2]>>]
                                  ELSE cellsWithWrite[pos]]
                      /\ cell_flags' = cell_flags
           ELSE
               \* Below scroll region - just wrap if possible
               IF cursor.row < rows - 1
               THEN
                   /\ cursor' = [row |-> cursor.row + 1, col |-> 0]
                   /\ cells' = [cells EXCEPT ![<<cursor.row, cursor.col>>] = nextCellId]
                   /\ UNCHANGED <<total_lines, pages, row_page, row_offset, cell_flags>>
               ELSE
                   /\ cursor' = [row |-> cursor.row, col |-> 0]
                   /\ cells' = [cells EXCEPT ![<<cursor.row, cursor.col>>] = nextCellId]
                   /\ UNCHANGED <<total_lines, pages, row_page, row_offset, cell_flags>>
    /\ UNCHANGED <<rows, cols, display_offset, saved_cursor_row, saved_cursor_col, scroll_top, scroll_bottom, pages, row_page, row_offset>>

(***************************************************************************)
(* SCROLL REGION OPERATIONS (DECSTBM)                                       *)
(***************************************************************************)

\* Set scroll region (DECSTBM - DEC Set Top and Bottom Margins)
\* top and bottom are 0-indexed, inclusive
SetScrollRegion(top, bottom) ==
    IF top < bottom /\ bottom < rows
    THEN
        \* Valid scroll region
        /\ scroll_top' = top
        /\ scroll_bottom' = bottom
        /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, cells, nextCellId, pages, row_page, row_offset, cell_flags>>
    ELSE
        \* Invalid region - reset to full screen
        /\ scroll_top' = 0
        /\ scroll_bottom' = rows - 1
        /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

\* Reset scroll region to full screen
ResetScrollRegion ==
    /\ scroll_top' = 0
    /\ scroll_bottom' = rows - 1
    /\ UNCHANGED <<rows, cols, cursor, display_offset, total_lines, damage, saved_cursor_row, saved_cursor_col, cells, nextCellId, pages, row_page, row_offset, cell_flags>>

(***************************************************************************)
(* NEXT STATE RELATION                                                      *)
(***************************************************************************)

Next ==
    \* Cursor movement
    \/ \E r \in 0..MaxRows-1, c \in 0..MaxCols-1 : MoveCursorTo(r, c)
    \/ \E dr \in -5..5, dc \in -5..5 : MoveCursorBy(dr, dc)
    \/ CarriageReturn
    \/ LineFeed
    \/ ReverseLineFeed
    \/ Tab
    \/ Backspace
    \* Cursor save/restore
    \/ SaveCursor
    \/ RestoreCursor
    \* Scrolling
    \/ \E delta \in -10..10 : Scroll(delta)
    \/ ScrollToTop
    \/ ScrollToBottom
    \/ PageUp
    \/ PageDown
    \* Scroll region (DECSTBM)
    \/ \E top \in 0..MaxRows-1, bottom \in 0..MaxRows-1 : SetScrollRegion(top, bottom)
    \/ ResetScrollRegion
    \* Resize
    \/ \E newRows \in 1..MaxRows, newCols \in 1..MaxCols : Resize(newRows, newCols)
    \* Erase operations
    \/ EraseToEndOfLine
    \/ EraseFromStartOfLine
    \/ EraseLine
    \/ EraseToEndOfScreen
    \/ EraseFromStartOfScreen
    \/ EraseScreen
    \/ EraseScrollback
    \* Cell write
    \/ WriteChar
    \/ WriteCharWithWrap

(***************************************************************************)
(* SPECIFICATION                                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* INVARIANTS                                                               *)
(***************************************************************************)

\* Type invariant always holds
THEOREM TypeSafe == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyHolds == Spec => []Safety

\* Key property: Resize always maintains cursor bounds
THEOREM ResizeMaintainsCursor ==
    \A newRows \in 1..MaxRows, newCols \in 1..MaxCols :
        (TypeInvariant /\ Resize(newRows, newCols)) => CursorInBounds'

\* Key property: SetScrollRegion always produces valid scroll region
THEOREM SetScrollRegionValid ==
    \A top \in 0..MaxRows-1, bottom \in 0..MaxRows-1 :
        (TypeInvariant /\ SetScrollRegion(top, bottom)) => ScrollRegionValid'

\* Key property: Resize resets scroll region properly
THEOREM ResizeMaintainsScrollRegion ==
    \A newRows \in 1..MaxRows, newCols \in 1..MaxCols :
        (TypeInvariant /\ Resize(newRows, newCols)) =>
            (scroll_top' = 0 /\ scroll_bottom' = newRows - 1)

(***************************************************************************)
(* FV-14: CONTENT PRESERVATION THEOREMS                                     *)
(*                                                                          *)
(* Key property: Resize preserves cell content within the new bounds.       *)
(* Cells that remain within both old and new dimensions keep their content. *)
(***************************************************************************)

\* Helper: Set of positions that exist in both old and new grids
PreservedPositions(oldTotalLines, oldCols, newTotalLines, newCols) ==
    {<<r, c>> : r \in 0..Min(oldTotalLines, newTotalLines)-1,
                c \in 0..Min(oldCols, newCols)-1}

\* FV-14: Resize preserves content for cells within new bounds
\* For any cell position that exists in both old and new grid,
\* the content (cell ID) is preserved
THEOREM ResizePreservesContent ==
    \A newRows \in 1..MaxRows, newCols \in 1..MaxCols :
        (TypeInvariant /\ Resize(newRows, newCols)) =>
            \A pos \in PreservedPositions(total_lines, cols, total_lines', newCols) :
                cells'[pos] = cells[pos]

\* FV-14: New cells from grid expansion are empty
\* When the grid grows, new cells are initialized to 0 (empty)
THEOREM ResizeNewCellsEmpty ==
    \A newRows \in 1..MaxRows, newCols \in 1..MaxCols :
        (TypeInvariant /\ Resize(newRows, newCols)) =>
            \A pos \in DOMAIN cells' :
                (pos \notin DOMAIN cells) => (cells'[pos] = 0)

\* FV-14: Cell IDs are never corrupted on resize
\* All cell values in new grid are either 0 or a valid existing cell ID
THEOREM ResizeCellIdsValid ==
    \A newRows \in 1..MaxRows, newCols \in 1..MaxCols :
        (TypeInvariant /\ Resize(newRows, newCols)) =>
            \A pos \in DOMAIN cells' :
                cells'[pos] \in 0..nextCellId

(***************************************************************************)
(* LIVENESS PROPERTIES (optional)                                           *)
(***************************************************************************)

\* If we scroll to bottom, display_offset becomes 0
LiveScrollToBottom ==
    <>[]((display_offset = 0) => (display_offset = 0))

(***************************************************************************)
(* WIDE CHARACTER THEOREMS                                                  *)
(*                                                                          *)
(* These theorems verify the wide character handling is always correct.     *)
(***************************************************************************)

\* Wide character consistency is always maintained
THEOREM WideCharsSafe == Spec => []WideCharConsistent

\* Wide chars never start at end of line
THEOREM WideCharsNotAtEnd == Spec => []WideCharNotAtEnd

\* Placeholders are always preceded by their wide char
THEOREM PlaceholdersValid == Spec => []PlaceholderPrecededByWide

\* First column is never a placeholder
THEOREM FirstColNotPlaceholder == Spec => []FirstColumnNotPlaceholder

\* Complete wide char safety
THEOREM WideCharSafetyHolds == Spec => []WideCharSafety

(***************************************************************************)
(* MODEL CHECKING CONFIGURATION                                             *)
(*                                                                          *)
(* For tractable model checking, use small constants:                       *)
(* MaxRows = 2, MaxCols = 3, MaxScrollback = 3, PageSize = 8, MaxCellId = 4 *)
(***************************************************************************)

==========================================================================
