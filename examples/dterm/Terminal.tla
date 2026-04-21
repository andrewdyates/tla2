--------------------------- MODULE Terminal ---------------------------
(***************************************************************************)
(* TLA+ Composite Specification for dTerm Terminal                         *)
(*                                                                          *)
(* This specification composes all terminal subsystems and defines:         *)
(* - Cross-module invariants ensuring consistent state                      *)
(* - Byte processing that dispatches parser actions to grid operations      *)
(* - Module interaction properties that individual specs cannot verify      *)
(*                                                                          *)
(* This is the TOP-LEVEL spec that should be model-checked to find          *)
(* integration bugs between subsystems.                                     *)
(*                                                                          *)
(* Reference: docs/architecture/ARCHITECTURE.md                             *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals, TLC

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    MaxRows,              \* Maximum terminal rows
    MaxCols,              \* Maximum terminal columns
    MaxScrollback,        \* Maximum scrollback lines
    MaxParams,            \* Maximum CSI parameters (16)
    MaxIntermediates,     \* Maximum intermediate bytes (4)
    PageSize,             \* Page size in bytes (65536)
    MemoryBudget,         \* Memory budget for scrollback
    BlockSize             \* Lines per compression block

ASSUME MaxRows \in Nat /\ MaxRows > 0
ASSUME MaxCols \in Nat /\ MaxCols > 0
ASSUME MaxScrollback \in Nat
ASSUME MaxParams \in Nat /\ MaxParams > 0
ASSUME MaxIntermediates \in Nat /\ MaxIntermediates > 0
ASSUME PageSize \in Nat /\ PageSize > 0
ASSUME MemoryBudget \in Nat /\ MemoryBudget > 0
ASSUME BlockSize \in Nat /\ BlockSize > 0

(***************************************************************************)
(* VARIABLES - Composed from all subsystems                                *)
(***************************************************************************)

\* ---- Grid State ----
VARIABLES
    grid_rows,            \* Current visible row count
    grid_cols,            \* Current column count
    grid_cursor,          \* Cursor position {row, col}
    grid_display_offset,  \* Scroll position for O(1) scrolling
    grid_total_lines,     \* Total lines in buffer
    grid_damage,          \* Damage tracking for rendering
    grid_scroll_top,      \* Top of scroll region
    grid_scroll_bottom,   \* Bottom of scroll region
    grid_cells,           \* Cell content mapping
    grid_cell_flags       \* Cell flags (wide char, wrapped, etc.)

\* ---- Parser State ----
VARIABLES
    parser_state,         \* Current parser state (Ground, Escape, etc.)
    parser_params,        \* Parameter accumulator
    parser_intermediates, \* Intermediate bytes
    parser_current_param  \* Current parameter being built

\* ---- Scrollback State ----
VARIABLES
    scrollback_hot,       \* Hot tier (uncompressed)
    scrollback_warm,      \* Warm tier (LZ4 compressed)
    scrollback_cold,      \* Cold tier (on disk)
    scrollback_line_count,\* Total lines in scrollback
    scrollback_memory     \* Current memory usage

\* ---- Selection State ----
VARIABLES
    selection_state,      \* None, InProgress, Complete
    selection_type,       \* Simple, Block, Semantic, Lines
    selection_start,      \* Start anchor {row, col, side}
    selection_end         \* End anchor {row, col, side}

\* ---- Terminal Modes ----
VARIABLES
    mode_origin,          \* DECOM - origin mode
    mode_autowrap,        \* DECAWM - auto-wrap mode
    mode_insert,          \* IRM - insert mode
    mode_cursor_visible,  \* DECTCEM - cursor visible
    mode_alternate_screen,\* Alternate screen buffer active
    mode_bracketed_paste, \* Bracketed paste mode
    mode_mouse            \* Mouse tracking mode

\* ---- Page Pool State ----
VARIABLES
    pool_active_pages,    \* Set of allocated page IDs
    pool_free_pages,      \* Set of free page IDs
    pool_generation,      \* Current generation for pin invalidation
    pool_page_gen         \* Map: page_id -> generation when freed

\* Variable groupings
grid_vars == <<grid_rows, grid_cols, grid_cursor, grid_display_offset,
               grid_total_lines, grid_damage, grid_scroll_top, grid_scroll_bottom,
               grid_cells, grid_cell_flags>>

parser_vars == <<parser_state, parser_params, parser_intermediates, parser_current_param>>

scrollback_vars == <<scrollback_hot, scrollback_warm, scrollback_cold,
                     scrollback_line_count, scrollback_memory>>

selection_vars == <<selection_state, selection_type, selection_start, selection_end>>

mode_vars == <<mode_origin, mode_autowrap, mode_insert, mode_cursor_visible,
               mode_alternate_screen, mode_bracketed_paste, mode_mouse>>

pool_vars == <<pool_active_pages, pool_free_pages, pool_generation, pool_page_gen>>

vars == <<grid_vars, parser_vars, scrollback_vars, selection_vars, mode_vars, pool_vars>>

(***************************************************************************)
(* TYPE DEFINITIONS                                                         *)
(***************************************************************************)

\* Parser states (subset - see Parser.tla for full list)
ParserStates == {"Ground", "Escape", "EscapeIntermediate", "CsiEntry",
                 "CsiParam", "CsiIntermediate", "CsiIgnore", "DcsEntry",
                 "DcsParam", "DcsIntermediate", "DcsPassthrough", "DcsIgnore",
                 "OscString", "SosPmApcString"}

\* Selection states
SelectionStates == {"None", "InProgress", "Complete"}

\* Selection types
SelectionTypes == {"Simple", "Block", "Semantic", "Lines"}

\* Mouse modes
MouseModes == {"None", "X10", "Normal", "Button", "Any", "Sgr", "Urxvt"}

\* Cell flags
CellFlagSets == SUBSET {"Wide", "WidePlaceholder", "Wrapped", "Hyperlink"}

(***************************************************************************)
(* INDIVIDUAL MODULE TYPE INVARIANTS                                        *)
(***************************************************************************)

GridTypeInvariant ==
    /\ grid_rows \in 1..MaxRows
    /\ grid_cols \in 1..MaxCols
    /\ grid_cursor.row \in 0..grid_rows-1
    /\ grid_cursor.col \in 0..grid_cols-1
    /\ grid_display_offset \in 0..MaxScrollback
    /\ grid_total_lines \in grid_rows..MaxScrollback+grid_rows
    /\ grid_scroll_top \in 0..grid_rows-1
    /\ grid_scroll_bottom \in 0..grid_rows-1
    /\ grid_scroll_top <= grid_scroll_bottom

ParserTypeInvariant ==
    /\ parser_state \in ParserStates
    /\ Len(parser_params) <= MaxParams
    /\ Len(parser_intermediates) <= MaxIntermediates
    /\ parser_current_param \in 0..65535

ScrollbackTypeInvariant ==
    /\ scrollback_line_count \in 0..MaxScrollback
    /\ scrollback_memory \in 0..MemoryBudget * 2  \* Allow temporary overage

SelectionTypeInvariant ==
    /\ selection_state \in SelectionStates
    /\ selection_type \in SelectionTypes

ModeTypeInvariant ==
    /\ mode_origin \in BOOLEAN
    /\ mode_autowrap \in BOOLEAN
    /\ mode_insert \in BOOLEAN
    /\ mode_cursor_visible \in BOOLEAN
    /\ mode_alternate_screen \in BOOLEAN
    /\ mode_bracketed_paste \in BOOLEAN
    /\ mode_mouse \in MouseModes

PoolTypeInvariant ==
    /\ pool_active_pages \cap pool_free_pages = {}  \* Disjoint
    /\ pool_generation \in Nat

(***************************************************************************)
(* CROSS-MODULE INVARIANTS                                                  *)
(*                                                                          *)
(* These are the KEY properties that individual specs cannot verify.        *)
(* They ensure the modules work together correctly.                         *)
(***************************************************************************)

\* Grid total lines must match scrollback + visible
GridScrollbackConsistent ==
    grid_total_lines = scrollback_line_count + grid_rows

\* Selection anchors must be within valid grid bounds (including scrollback)
SelectionWithinBounds ==
    selection_state /= "None" =>
        /\ selection_start.row >= -scrollback_line_count
        /\ selection_start.row < grid_rows
        /\ selection_start.col >= 0
        /\ selection_start.col < grid_cols
        /\ selection_end.row >= -scrollback_line_count
        /\ selection_end.row < grid_rows
        /\ selection_end.col >= 0
        /\ selection_end.col < grid_cols

\* Origin mode constrains cursor to scroll region
OriginModeCursorConstraint ==
    mode_origin =>
        /\ grid_cursor.row >= grid_scroll_top
        /\ grid_cursor.row <= grid_scroll_bottom

\* Display offset cannot exceed scrollback
DisplayOffsetValid ==
    grid_display_offset <= scrollback_line_count

\* Memory usage should be bounded (with epsilon for in-flight operations)
MemoryBudgetRespected ==
    scrollback_memory <= MemoryBudget + (BlockSize * MaxCols)

\* All grid pages must come from the pool
GridPagesFromPool ==
    \* Abstract: grid's page references should be in pool_active_pages
    TRUE  \* Detailed check requires page mapping variables

\* Wide character consistency: wide chars must have placeholder in next cell
WideCharConsistent ==
    \A r \in 0..grid_rows-1, c \in 0..grid_cols-2:
        "Wide" \in grid_cell_flags[<<r,c>>] =>
            /\ "WidePlaceholder" \in grid_cell_flags[<<r,c+1>>]

\* Wide chars cannot start at last column
WideCharNotAtEnd ==
    \A r \in 0..grid_rows-1:
        ~("Wide" \in grid_cell_flags[<<r, grid_cols-1>>])

\* Selection must not split wide characters
SelectionWideCharIntegrity ==
    selection_state /= "None" =>
        \* Start of selection should not be on a wide placeholder
        ~("WidePlaceholder" \in grid_cell_flags[<<selection_start.row, selection_start.col>>])

(***************************************************************************)
(* COMPOSITE TYPE INVARIANT                                                 *)
(***************************************************************************)

TypeInvariant ==
    /\ GridTypeInvariant
    /\ ParserTypeInvariant
    /\ ScrollbackTypeInvariant
    /\ SelectionTypeInvariant
    /\ ModeTypeInvariant
    /\ PoolTypeInvariant

(***************************************************************************)
(* COMPOSITE SAFETY INVARIANT                                               *)
(***************************************************************************)

SafetyInvariant ==
    /\ GridScrollbackConsistent
    /\ SelectionWithinBounds
    /\ OriginModeCursorConstraint
    /\ DisplayOffsetValid
    /\ MemoryBudgetRespected
    /\ WideCharConsistent
    /\ WideCharNotAtEnd
    /\ SelectionWideCharIntegrity

(***************************************************************************)
(* PARSER ACTION DISPATCH                                                   *)
(*                                                                          *)
(* Models how parser actions affect grid state.                             *)
(***************************************************************************)

\* Print action: write character at cursor, advance cursor
PrintChar(ch) ==
    /\ grid_cursor' = IF grid_cursor.col < grid_cols - 1
                      THEN [grid_cursor EXCEPT !.col = @ + 1]
                      ELSE IF mode_autowrap
                           THEN [row |-> (grid_cursor.row + 1) % grid_rows, col |-> 0]
                           ELSE grid_cursor
    /\ grid_damage' = grid_damage \union {grid_cursor.row}
    /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                   grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>

\* Execute C0 control: handle control characters
ExecuteControl(byte) ==
    CASE byte = 8 ->   \* BS - backspace
            /\ grid_cursor' = [grid_cursor EXCEPT !.col = IF @ > 0 THEN @ - 1 ELSE 0]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] byte = 9 ->   \* HT - tab
            /\ grid_cursor' = [grid_cursor EXCEPT !.col =
                IF ((@ \div 8) + 1) * 8 < grid_cols
                THEN ((@ \div 8) + 1) * 8
                ELSE grid_cols - 1]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] byte = 10 ->  \* LF - line feed
            /\ grid_cursor' = [grid_cursor EXCEPT !.row = IF @ < grid_scroll_bottom
                                                          THEN @ + 1
                                                          ELSE @]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] byte = 13 ->  \* CR - carriage return
            /\ grid_cursor' = [grid_cursor EXCEPT !.col = 0]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] OTHER ->
            /\ UNCHANGED grid_vars

\* CSI dispatch: handle escape sequences
CsiDispatch(final, params) ==
    CASE final = 65 ->  \* CUU - Cursor Up
            /\ grid_cursor' = [grid_cursor EXCEPT !.row = IF @ > grid_scroll_top
                                                          THEN @ - 1
                                                          ELSE @]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] final = 66 ->  \* CUD - Cursor Down
            /\ grid_cursor' = [grid_cursor EXCEPT !.row = IF @ < grid_scroll_bottom
                                                          THEN @ + 1
                                                          ELSE @]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] final = 67 ->  \* CUF - Cursor Forward
            /\ grid_cursor' = [grid_cursor EXCEPT !.col = IF @ < grid_cols - 1
                                                          THEN @ + 1
                                                          ELSE @]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] final = 68 ->  \* CUB - Cursor Backward
            /\ grid_cursor' = [grid_cursor EXCEPT !.col = IF @ > 0
                                                          THEN @ - 1
                                                          ELSE @]
            /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                          grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags>>
      [] OTHER ->
            /\ UNCHANGED grid_vars

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    \* Grid initialization
    /\ grid_rows = MaxRows
    /\ grid_cols = MaxCols
    /\ grid_cursor = [row |-> 0, col |-> 0]
    /\ grid_display_offset = 0
    /\ grid_total_lines = grid_rows
    /\ grid_damage = {}
    /\ grid_scroll_top = 0
    /\ grid_scroll_bottom = grid_rows - 1
    /\ grid_cells = [pos \in (0..grid_rows - 1) \X (0..grid_cols - 1) |-> 0]
    /\ grid_cell_flags = [pos \in (0..grid_rows - 1) \X (0..grid_cols - 1) |-> {}]
    \* Parser initialization
    /\ parser_state = "Ground"
    /\ parser_params = <<>>
    /\ parser_intermediates = <<>>
    /\ parser_current_param = 0
    \* Scrollback initialization
    /\ scrollback_hot = <<>>
    /\ scrollback_warm = <<>>
    /\ scrollback_cold = <<>>
    /\ scrollback_line_count = 0
    /\ scrollback_memory = 0
    \* Selection initialization
    /\ selection_state = "None"
    /\ selection_type = "Simple"
    /\ selection_start = [row |-> 0, col |-> 0, side |-> "Left"]
    /\ selection_end = [row |-> 0, col |-> 0, side |-> "Right"]
    \* Mode initialization
    /\ mode_origin = FALSE
    /\ mode_autowrap = TRUE
    /\ mode_insert = FALSE
    /\ mode_cursor_visible = TRUE
    /\ mode_alternate_screen = FALSE
    /\ mode_bracketed_paste = FALSE
    /\ mode_mouse = "None"
    \* Pool initialization
    /\ pool_active_pages = {}
    /\ pool_free_pages = {}
    /\ pool_generation = 0
    /\ pool_page_gen = [p \in {} |-> 0]

(***************************************************************************)
(* NEXT STATE RELATION                                                      *)
(***************************************************************************)

\* Process a single byte through the terminal
ProcessByte(byte) ==
    \* Simplified: dispatch based on parser state
    \/ /\ parser_state = "Ground"
       /\ byte \in 32..126  \* Printable
       /\ PrintChar(byte)
       /\ UNCHANGED <<parser_vars, scrollback_vars, selection_vars, mode_vars, pool_vars>>
    \/ /\ parser_state = "Ground"
       /\ byte \in 0..31  \* C0 control
       /\ ExecuteControl(byte)
       /\ UNCHANGED <<parser_vars, scrollback_vars, selection_vars, mode_vars, pool_vars>>
    \/ UNCHANGED vars  \* Other cases

\* Selection operations
StartSelection ==
    /\ selection_state = "None"
    /\ selection_state' = "InProgress"
    /\ selection_start' = [row |-> grid_cursor.row, col |-> grid_cursor.col, side |-> "Left"]
    /\ selection_end' = selection_start'
    /\ UNCHANGED <<selection_type, grid_vars, parser_vars, scrollback_vars, mode_vars, pool_vars>>

CompleteSelection ==
    /\ selection_state = "InProgress"
    /\ selection_state' = "Complete"
    /\ UNCHANGED <<selection_type, selection_start, selection_end,
                   grid_vars, parser_vars, scrollback_vars, mode_vars, pool_vars>>

ClearSelection ==
    /\ selection_state /= "None"
    /\ selection_state' = "None"
    /\ UNCHANGED <<selection_type, selection_start, selection_end,
                   grid_vars, parser_vars, scrollback_vars, mode_vars, pool_vars>>

\* Mode changes
SetOriginMode ==
    /\ mode_origin' = TRUE
    \* Cursor must move to scroll region top
    /\ grid_cursor' = [grid_cursor EXCEPT !.row = grid_scroll_top]
    /\ UNCHANGED <<grid_rows, grid_cols, grid_display_offset, grid_total_lines,
                   grid_damage, grid_scroll_top, grid_scroll_bottom, grid_cells, grid_cell_flags,
                   parser_vars, scrollback_vars, selection_vars,
                   mode_autowrap, mode_insert, mode_cursor_visible,
                   mode_alternate_screen, mode_bracketed_paste, mode_mouse, pool_vars>>

ResetOriginMode ==
    /\ mode_origin' = FALSE
    /\ UNCHANGED <<grid_vars, parser_vars, scrollback_vars, selection_vars,
                   mode_autowrap, mode_insert, mode_cursor_visible,
                   mode_alternate_screen, mode_bracketed_paste, mode_mouse, pool_vars>>

Next ==
    \/ \E b \in 0..127: ProcessByte(b)
    \/ StartSelection
    \/ CompleteSelection
    \/ ClearSelection
    \/ SetOriginMode
    \/ ResetOriginMode

(***************************************************************************)
(* SPECIFICATION                                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* THEOREMS                                                                 *)
(***************************************************************************)

\* Type safety is preserved
THEOREM TypeSafe == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyHolds == Spec => []SafetyInvariant

\* Grid and scrollback stay in sync
THEOREM GridScrollbackSync == Spec => []GridScrollbackConsistent

\* Origin mode always constrains cursor
THEOREM OriginModeWorks == Spec => []OriginModeCursorConstraint

\* Wide characters are always consistent
THEOREM WideCharsValid == Spec => [](WideCharConsistent /\ WideCharNotAtEnd)

\* Selection never splits wide chars
THEOREM SelectionValid == Spec => []SelectionWideCharIntegrity

=============================================================================
